use std::any::TypeId;
use std::cell::{RefCell, UnsafeCell};
use std::collections::HashMap;
use std::ffi::CString;
use std::marker::PhantomData;
use std::os::raw::{c_char, c_int, c_void};
use std::sync::{Arc, Mutex, mpsc};
use std::{mem, ptr, str};

use futures::future::{self, BoxFuture, Future, FutureExt, TryFutureExt};
use futures::task::{Context, Poll, Waker};

use crate::error::{Error, Result};
use crate::ffi;
use crate::function::Function;
use crate::scope::Scope;
use crate::stdlib::StdLib;
use crate::string::String;
use crate::table::Table;
use crate::thread::Thread;
use crate::types::{AsyncCallback, Callback, Integer, LightUserData, LuaRef, Number, RegistryKey};
use crate::userdata::{AnyUserData, MetaMethod, UserData, UserDataMethods};
#[cfg(any(feature = "lua51", feature = "luajit"))]
use crate::util::set_main_state;
use crate::util::{
    assert_stack, callback_error, check_stack, push_gc_userdata, get_gc_userdata,
    get_main_state, get_wrapped_error, init_error_registry, init_gc_metatable_for,
    init_userdata_metatable, pop_error, protect_lua, protect_lua_closure, push_string,
    push_userdata, push_wrapped_error, StackGuard,
};
use crate::value::{FromLua, FromLuaMulti, MultiValue, Nil, ToLua, ToLuaMulti, Value};

/// Top level Lua struct which holds the Lua state itself.
#[derive(Clone)]
pub struct Lua {
    pub(crate) state: *mut ffi::lua_State,
    main_state: *mut ffi::lua_State,
    extra: Arc<RefCell<ExtraData>>,
    ephemeral: bool,
    // Lua has lots of interior mutability, should not be RefUnwindSafe
    _no_ref_unwind_safe: PhantomData<UnsafeCell<()>>,
}

// Data associated with the lua_State.
struct ExtraData {
    registered_userdata: HashMap<TypeId, c_int>,
    registry_unref_list: Arc<Mutex<Option<Vec<c_int>>>>,

    ref_thread: *mut ffi::lua_State,
    ref_stack_size: c_int,
    ref_stack_max: c_int,
    ref_free: Vec<c_int>,
}

pub(crate) struct AsyncPollPending;
pub(crate) static WAKER_REGISTRY_KEY: u8 = 0;

unsafe impl Send for Lua {}

impl Drop for Lua {
    fn drop(&mut self) {
        unsafe {
            if !self.ephemeral && Arc::strong_count(&self.extra) == 1 {
                let mut extra = self.extra.borrow_mut();
                mlua_debug_assert!(
                    ffi::lua_gettop(extra.ref_thread) == extra.ref_stack_max
                        && extra.ref_stack_max as usize == extra.ref_free.len(),
                    "reference leak detected"
                );
                *mlua_expect!(extra.registry_unref_list.lock(), "unref list poisoned") = None;
                ffi::lua_close(self.state);
            }
        }
    }
}

impl Lua {
    /// Creates a new Lua state and loads standard library without the `debug` library.
    pub fn new() -> Lua {
        Self::new_with(StdLib::ALL_NO_DEBUG)
    }

    /// Creates a new Lua state and loads the specified set of standard libraries.
    ///
    /// Use the [`StdLib`] flags to specifiy the libraries you want to load.
    ///
    /// [`StdLib`]: struct.StdLib.html
    pub fn new_with(libs: StdLib) -> Lua {
        unsafe {
            let state = ffi::luaL_newstate();

            ffi::luaL_requiref(state, cstr!("_G"), ffi::luaopen_base, 1);
            ffi::lua_pop(state, 1);

            let mut lua = Lua::init_from_ptr(state);
            lua.ephemeral = false;

            mlua_expect!(
                protect_lua_closure(lua.main_state, 0, 0, |state| {
                    load_from_std_lib(state, libs);
                }),
                "Error during loading standard libraries"
            );

            lua
        }
    }

    /// Loads the specified set of standard libraries into an existing Lua state.
    ///
    /// Use the [`StdLib`] flags to specifiy the libraries you want to load.
    ///
    /// [`StdLib`]: struct.StdLib.html
    pub fn load_from_std_lib(&self, libs: StdLib) -> Result<()> {
        unsafe {
            protect_lua_closure(self.main_state, 0, 0, |state| {
                load_from_std_lib(state, libs);
            })
        }
    }

    /// Constructs a new Lua instance from the existing state.
    pub unsafe fn init_from_ptr(state: *mut ffi::lua_State) -> Lua {
        #[cfg(any(feature = "lua53", feature = "lua52"))]
        let main_state = get_main_state(state);
        #[cfg(any(feature = "lua51", feature = "luajit"))]
        let main_state = {
            set_main_state(state);
            state
        };
        let main_state_top = ffi::lua_gettop(state);

        let ref_thread = mlua_expect!(
            protect_lua_closure(main_state, 0, 0, |state| {
                init_error_registry(state);

                // Create the internal metatables and place them in the registry
                // to prevent them from being garbage collected.

                init_gc_metatable_for::<Callback>(state, None);
                init_gc_metatable_for::<AsyncCallback>(state, None);
                init_gc_metatable_for::<BoxFuture<Result<MultiValue>>>(state, None);
                init_gc_metatable_for::<AsyncPollPending>(state, None);
                init_gc_metatable_for::<Waker>(state, None);
                init_gc_metatable_for::<Arc<RefCell<ExtraData>>>(state, None);
                init_gc_metatable_for::<mpsc::Sender<i32>>(state, None);

                // Create ref stack thread and place it in the registry to prevent it from being garbage
                // collected.

                let _ref_thread = ffi::lua_newthread(state);
                ffi::luaL_ref(state, ffi::LUA_REGISTRYINDEX);
                _ref_thread
            }),
            "Error during Lua construction",
        );

        // Create ExtraData

        let extra = Arc::new(RefCell::new(ExtraData {
            registered_userdata: HashMap::new(),
            registry_unref_list: Arc::new(Mutex::new(Some(Vec::new()))),
            ref_thread,
            // We need 1 extra stack space to move values in and out of the ref stack.
            ref_stack_size: ffi::LUA_MINSTACK - 1,
            ref_stack_max: 0,
            ref_free: Vec::new(),
        }));

        mlua_debug_assert!(
            ffi::lua_gettop(main_state) == main_state_top,
            "stack leak during creation"
        );
        assert_stack(main_state, ffi::LUA_MINSTACK);

        Lua {
            state,
            main_state: main_state,
            extra: extra,
            ephemeral: true,
            _no_ref_unwind_safe: PhantomData,
        }
    }

    // Executes module entrypoint function, which returns only one Value.
    // The returned value then pushed to the Lua stack.
    #[doc(hidden)]
    pub fn entrypoint1<R, F>(&self, func: F) -> Result<c_int>
    where
        R: ToLua,
        F: 'static + Send + Fn(Lua) -> Result<R>,
    {
        let cb = self.create_callback(Box::new(move |lua, _| func(lua.clone())?.to_lua_multi(&lua)))?;
        unsafe { self.push_value(cb.call(())?).map(|_| 1) }
    }

    /// Returns true if the garbage collector is currently running automatically.
    #[cfg(any(feature = "lua53", feature = "lua52"))]
    pub fn gc_is_running(&self) -> bool {
        unsafe { ffi::lua_gc(self.main_state, ffi::LUA_GCISRUNNING, 0) != 0 }
    }

    /// Stop the Lua GC from running
    pub fn gc_stop(&self) {
        unsafe {
            ffi::lua_gc(self.main_state, ffi::LUA_GCSTOP, 0);
        }
    }

    /// Restarts the Lua GC if it is not running
    pub fn gc_restart(&self) {
        unsafe {
            ffi::lua_gc(self.main_state, ffi::LUA_GCRESTART, 0);
        }
    }

    /// Perform a full garbage-collection cycle.
    ///
    /// It may be necessary to call this function twice to collect all currently unreachable
    /// objects.  Once to finish the current gc cycle, and once to start and finish the next cycle.
    pub fn gc_collect(&self) -> Result<()> {
        unsafe {
            protect_lua_closure(self.main_state, 0, 0, |state| {
                ffi::lua_gc(state, ffi::LUA_GCCOLLECT, 0);
            })
        }
    }

    /// Steps the garbage collector one indivisible step.
    ///
    /// Returns true if this has finished a collection cycle.
    pub fn gc_step(&self) -> Result<bool> {
        self.gc_step_kbytes(0)
    }

    /// Steps the garbage collector as though memory had been allocated.
    ///
    /// if `kbytes` is 0, then this is the same as calling `gc_step`.  Returns true if this step has
    /// finished a collection cycle.
    pub fn gc_step_kbytes(&self, kbytes: c_int) -> Result<bool> {
        unsafe {
            protect_lua_closure(self.main_state, 0, 0, |state| {
                ffi::lua_gc(state, ffi::LUA_GCSTEP, kbytes) != 0
            })
        }
    }

    /// Sets the 'pause' value of the collector.
    ///
    /// Returns the previous value of 'pause'.  More information can be found in the [Lua 5.3
    /// documentation][lua_doc].
    ///
    /// [lua_doc]: https://www.lua.org/manual/5.3/manual.html#2.5
    pub fn gc_set_pause(&self, pause: c_int) -> c_int {
        unsafe { ffi::lua_gc(self.main_state, ffi::LUA_GCSETPAUSE, pause) }
    }

    /// Sets the 'step multiplier' value of the collector.
    ///
    /// Returns the previous value of the 'step multiplier'.  More information can be found in the
    /// [Lua 5.3 documentation][lua_doc].
    ///
    /// [lua_doc]: https://www.lua.org/manual/5.3/manual.html#2.5
    pub fn gc_set_step_multiplier(&self, step_multiplier: c_int) -> c_int {
        unsafe { ffi::lua_gc(self.main_state, ffi::LUA_GCSETSTEPMUL, step_multiplier) }
    }

    /// Returns Lua source code as a `Chunk` builder type.
    ///
    /// In order to actually compile or run the resulting code, you must call [`Chunk::exec`] or
    /// similar on the returned builder.  Code is not even parsed until one of these methods is
    /// called.
    ///
    /// [`Chunk::exec`]: struct.Chunk.html#method.exec
    pub fn load<'a, S>(&self, source: &'a S) -> Chunk<'a>
    where
        S: ?Sized + AsRef<[u8]>,
    {
        Chunk {
            lua: self.clone(),
            source: source.as_ref(),
            name: None,
            env: None,
        }
    }

    fn load_chunk(
        &self,
        source: &[u8],
        name: Option<&CString>,
        env: Option<Value>,
    ) -> Result<Function> {
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 1);

            match if let Some(name) = name {
                ffi::luaL_loadbufferx(
                    self.state,
                    source.as_ptr() as *const c_char,
                    source.len(),
                    name.as_ptr() as *const c_char,
                    cstr!("t"),
                )
            } else {
                ffi::luaL_loadbufferx(
                    self.state,
                    source.as_ptr() as *const c_char,
                    source.len(),
                    ptr::null(),
                    cstr!("t"),
                )
            } {
                ffi::LUA_OK => {
                    if let Some(env) = env {
                        self.push_value(env)?;
                        #[cfg(any(feature = "lua53", feature = "lua52"))]
                        ffi::lua_setupvalue(self.state, -2, 1);
                        #[cfg(any(feature = "lua51", feature = "luajit"))]
                        ffi::lua_setfenv(self.state, -2);
                    }
                    Ok(Function(self.pop_ref()))
                }
                err => Err(pop_error(self.state, err)),
            }
        }
    }

    /// Create and return an interned Lua string.  Lua strings can be arbitrary [u8] data including
    /// embedded nulls, so in addition to `&str` and `&String`, you can also pass plain `&[u8]`
    /// here.
    pub fn create_string<S>(&self, s: &S) -> Result<String>
    where
        S: ?Sized + AsRef<[u8]>,
    {
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 4);
            push_string(self.state, s)?;
            Ok(String(self.pop_ref()))
        }
    }

    /// Creates and returns a new table.
    pub fn create_table(&self) -> Result<Table> {
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 3);
            unsafe extern "C" fn new_table(state: *mut ffi::lua_State) -> c_int {
                ffi::lua_newtable(state);
                1
            }
            protect_lua(self.state, 0, new_table)?;
            Ok(Table(self.pop_ref()))
        }
    }

    /// Creates a table and fills it with values from an iterator.
    pub fn create_table_from<K, V, I>(&self, cont: I) -> Result<Table>
    where
        K: ToLua,
        V: ToLua,
        I: IntoIterator<Item = (K, V)>,
    {
        unsafe {
            let _sg = StackGuard::new(self.state);
            // `Lua` instance assumes that on any callback, the Lua stack has at least LUA_MINSTACK
            // slots available to avoid panics.
            check_stack(self.state, 5 + ffi::LUA_MINSTACK)?;

            unsafe extern "C" fn new_table(state: *mut ffi::lua_State) -> c_int {
                ffi::lua_newtable(state);
                1
            }
            protect_lua(self.state, 0, new_table)?;

            for (k, v) in cont {
                self.push_value(k.to_lua(self)?)?;
                self.push_value(v.to_lua(self)?)?;
                unsafe extern "C" fn raw_set(state: *mut ffi::lua_State) -> c_int {
                    ffi::lua_rawset(state, -3);
                    1
                }
                protect_lua(self.state, 3, raw_set)?;
            }
            Ok(Table(self.pop_ref()))
        }
    }

    /// Creates a table from an iterator of values, using `1..` as the keys.
    pub fn create_sequence_from<T, I>(&self, cont: I) -> Result<Table>
    where
        T: ToLua,
        I: IntoIterator<Item = T>,
    {
        self.create_table_from(cont.into_iter().enumerate().map(|(k, v)| (k + 1, v)))
    }

    /// Wraps a Rust function or closure, creating a callable Lua function handle to it.
    ///
    /// The function's return value is always a `Result`: If the function returns `Err`, the error
    /// is raised as a Lua error, which can be caught using `(x)pcall` or bubble up to the Rust code
    /// that invoked the Lua code. This allows using the `?` operator to propagate errors through
    /// intermediate Lua code.
    ///
    /// If the function returns `Ok`, the contained value will be converted to one or more Lua
    /// values. For details on Rust-to-Lua conversions, refer to the [`ToLua`] and [`ToLuaMulti`]
    /// traits.
    ///
    /// # Examples
    ///
    /// Create a function which prints its argument:
    ///
    /// ```
    /// # use mlua::{Lua, Result};
    /// # fn main() -> Result<()> {
    /// # let lua = Lua::new();
    /// let greet = lua.create_function(|_, name: String| {
    ///     println!("Hello, {}!", name);
    ///     Ok(())
    /// });
    /// # let _ = greet;    // used
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Use tuples to accept multiple arguments:
    ///
    /// ```
    /// # use mlua::{Lua, Result};
    /// # fn main() -> Result<()> {
    /// # let lua = Lua::new();
    /// let print_person = lua.create_function(|_, (name, age): (String, u8)| {
    ///     println!("{} is {} years old!", name, age);
    ///     Ok(())
    /// });
    /// # let _ = print_person;    // used
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [`ToLua`]: trait.ToLua.html
    /// [`ToLuaMulti`]: trait.ToLuaMulti.html
    pub fn create_function<A, R, F>(&self, func: F) -> Result<Function>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + Fn(&Lua, A) -> Result<R>,
    {
        self.create_callback(Box::new(move |lua, args| {
            func(lua, A::from_lua_multi(args, lua)?)?.to_lua_multi(lua)
        }))
    }

    /// Wraps a Rust mutable closure, creating a callable Lua function handle to it.
    ///
    /// This is a version of [`create_function`] that accepts a FnMut argument.  Refer to
    /// [`create_function`] for more information about the implementation.
    ///
    /// [`create_function`]: #method.create_function
    pub fn create_function_mut<A, R, F>(&self, func: F) -> Result<Function>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + FnMut(&Lua, A) -> Result<R>,
    {
        let func = RefCell::new(func);
        self.create_function(move |lua, args| {
            (&mut *func
                .try_borrow_mut()
                .map_err(|_| Error::RecursiveMutCallback)?)(lua, args)
        })
    }

    pub fn create_async_function<A, R, F, FR>(&self, func: F) -> Result<Function>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + Fn(Lua, A) -> FR,
        FR: 'static + Send + Future<Output = Result<R>>,
    {
        self.create_async_callback(Box::new(move |lua, args| {
            let args = match A::from_lua_multi(args, &lua) {
                Ok(x) => x,
                Err(e) => return future::err(e).boxed(),
            };
            func(lua.clone(), args)
                .and_then(move |x| future::ready(x.to_lua_multi(&lua)))
                .boxed()
        }))
    }

    /// Wraps a Lua function into a new thread (or coroutine).
    ///
    /// Equivalent to `coroutine.create`.
    pub fn create_thread(&self, func: Function) -> Result<Thread> {
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 2);

            let thread_state =
                protect_lua_closure(self.state, 0, 1, |state| ffi::lua_newthread(state))?;
            self.push_ref(&func.0);
            ffi::lua_xmove(self.state, thread_state, 1);

            Ok(Thread(self.pop_ref()))
        }
    }

    /// Create a Lua userdata object from a custom userdata type.
    pub fn create_userdata<T>(&self, data: T) -> Result<AnyUserData>
    where
        T: 'static + Send + UserData,
    {
        unsafe { self.make_userdata(data) }
    }

    /// Returns a handle to the global environment.
    pub fn globals(&self) -> Table {
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 2);
            #[cfg(any(feature = "lua53", feature = "lua52"))]
            ffi::lua_rawgeti(self.state, ffi::LUA_REGISTRYINDEX, ffi::LUA_RIDX_GLOBALS);
            #[cfg(any(feature = "lua51", feature = "luajit"))]
            ffi::lua_pushvalue(self.state, ffi::LUA_GLOBALSINDEX);
            Table(self.pop_ref())
        }
    }

    /// Returns a handle to the active `Thread`.  For calls to `Lua` this will be the main Lua thread,
    /// for parameters given to a callback, this will be whatever Lua thread called the callback.
    pub fn current_thread(&self) -> Thread {
        unsafe {
            ffi::lua_pushthread(self.state);
            Thread(self.pop_ref())
        }
    }

    /// Calls the given function with a `Scope` parameter, giving the function the ability to create
    /// userdata and callbacks from rust types that are !Send or non-'static.
    ///
    /// The lifetime of any function or userdata created through `Scope` lasts only until the
    /// completion of this method call, on completion all such created values are automatically
    /// dropped and Lua references to them are invalidated.  If a script accesses a value created
    /// through `Scope` outside of this method, a Lua error will result.  Since we can ensure the
    /// lifetime of values created through `Scope`, and we know that `Lua` cannot be sent to another
    /// thread while `Scope` is live, it is safe to allow !Send datatypes and whose lifetimes only
    /// outlive the scope lifetime.
    ///
    /// Inside the scope callback, all handles created through Scope will share the same unique 'lua
    /// lifetime of the parent `Lua`.  This allows scoped and non-scoped values to be mixed in
    /// API calls, which is very useful (e.g. passing a scoped userdata to a non-scoped function).
    /// However, this also enables handles to scoped values to be trivially leaked from the given
    /// callback. This is not dangerous, though!  After the callback returns, all scoped values are
    /// invalidated, which means that though references may exist, the Rust types backing them have
    /// dropped.  `Function` types will error when called, and `AnyUserData` will be typeless.  It
    /// would be impossible to prevent handles to scoped values from escaping anyway, since you
    /// would always be able to smuggle them through Lua state.
    pub fn scope<'scope, F, R>(&self, f: F) -> R
    where
        F: FnOnce(&Scope<'scope>) -> R,
    {
        f(&Scope::new(self))
    }

    /// Attempts to coerce a Lua value into a String in a manner consistent with Lua's internal
    /// behavior.
    ///
    /// To succeed, the value must be a string (in which case this is a no-op), an integer, or a
    /// number.
    pub fn coerce_string(&self, v: Value) -> Result<Option<String>> {
        Ok(match v {
            Value::String(s) => Some(s),
            v => unsafe {
                let _sg = StackGuard::new(self.state);
                assert_stack(self.state, 4);

                self.push_value(v)?;
                if protect_lua_closure(self.state, 1, 1, |state| {
                    !ffi::lua_tostring(state, -1).is_null()
                })? {
                    Some(String(self.pop_ref()))
                } else {
                    None
                }
            },
        })
    }

    /// Attempts to coerce a Lua value into an integer in a manner consistent with Lua's internal
    /// behavior.
    ///
    /// To succeed, the value must be an integer, a floating point number that has an exact
    /// representation as an integer, or a string that can be converted to an integer. Refer to the
    /// Lua manual for details.
    pub fn coerce_integer(&self, v: Value) -> Result<Option<Integer>> {
        Ok(match v {
            Value::Integer(i) => Some(i),
            v => unsafe {
                let _sg = StackGuard::new(self.state);
                assert_stack(self.state, 2);

                self.push_value(v)?;
                let mut isint = 0;
                let i = ffi::lua_tointegerx(self.state, -1, &mut isint);
                if isint == 0 {
                    None
                } else {
                    Some(i)
                }
            },
        })
    }

    /// Attempts to coerce a Lua value into a Number in a manner consistent with Lua's internal
    /// behavior.
    ///
    /// To succeed, the value must be a number or a string that can be converted to a number. Refer
    /// to the Lua manual for details.
    pub fn coerce_number(&self, v: Value) -> Result<Option<Number>> {
        Ok(match v {
            Value::Number(n) => Some(n),
            v => unsafe {
                let _sg = StackGuard::new(self.state);
                assert_stack(self.state, 2);

                self.push_value(v)?;
                let mut isnum = 0;
                let n = ffi::lua_tonumberx(self.state, -1, &mut isnum);
                if isnum == 0 {
                    None
                } else {
                    Some(n)
                }
            },
        })
    }

    /// Converts a value that implements `ToLua` into a `Value` instance.
    pub fn pack<T: ToLua>(&self, t: T) -> Result<Value> {
        t.to_lua(self)
    }

    /// Converts a `Value` instance into a value that implements `FromLua`.
    pub fn unpack<T: FromLua>(&self, value: Value) -> Result<T> {
        T::from_lua(value, self)
    }

    /// Converts a value that implements `ToLuaMulti` into a `MultiValue` instance.
    pub fn pack_multi<T: ToLuaMulti>(&self, t: T) -> Result<MultiValue> {
        t.to_lua_multi(self)
    }

    /// Converts a `MultiValue` instance into a value that implements `FromLuaMulti`.
    pub fn unpack_multi<T: FromLuaMulti>(&self, value: MultiValue) -> Result<T> {
        T::from_lua_multi(value, self)
    }

    /// Set a value in the Lua registry based on a string name.
    ///
    /// This value will be available to rust from all `Lua` instances which share the same main
    /// state.
    pub fn set_named_registry_value<S, T>(&self, name: &S, t: T) -> Result<()>
    where
        S: ?Sized + AsRef<[u8]>,
        T: ToLua,
    {
        let t = t.to_lua(self)?;
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 5);

            push_string(self.state, name)?;
            self.push_value(t)?;

            unsafe extern "C" fn set_registry(state: *mut ffi::lua_State) -> c_int {
                ffi::lua_rawset(state, ffi::LUA_REGISTRYINDEX);
                0
            }
            protect_lua(self.state, 2, set_registry)
        }
    }

    /// Get a value from the Lua registry based on a string name.
    ///
    /// Any Lua instance which shares the underlying main state may call this method to
    /// get a value previously set by [`set_named_registry_value`].
    ///
    /// [`set_named_registry_value`]: #method.set_named_registry_value
    pub fn named_registry_value<S, T>(&self, name: &S) -> Result<T>
    where
        S: ?Sized + AsRef<[u8]>,
        T: FromLua,
    {
        let value = unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 4);

            push_string(self.state, name)?;
            unsafe extern "C" fn get_registry(state: *mut ffi::lua_State) -> c_int {
                ffi::lua_rawget(state, ffi::LUA_REGISTRYINDEX);
                1
            }
            protect_lua(self.state, 1, get_registry)?;

            self.pop_value()
        };
        T::from_lua(value, self)
    }

    /// Removes a named value in the Lua registry.
    ///
    /// Equivalent to calling [`set_named_registry_value`] with a value of Nil.
    ///
    /// [`set_named_registry_value`]: #method.set_named_registry_value
    pub fn unset_named_registry_value<S>(&self, name: &S) -> Result<()>
    where
        S: ?Sized + AsRef<[u8]>,
    {
        self.set_named_registry_value(name, Nil)
    }

    /// Place a value in the Lua registry with an auto-generated key.
    ///
    /// This value will be available to rust from all `Lua` instances which share the same main
    /// state.
    ///
    /// Be warned, garbage collection of values held inside the registry is not automatic, see
    /// [`RegistryKey`] for more details.
    ///
    /// [`RegistryKey`]: struct.RegistryKey.html
    pub fn create_registry_value<T: ToLua>(&self, t: T) -> Result<RegistryKey> {
        let t = t.to_lua(self)?;
        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 2);

            self.push_value(t)?;
            let registry_id = protect_lua_closure(self.state, 1, 0, |state| {
                ffi::luaL_ref(state, ffi::LUA_REGISTRYINDEX)
            })?;

            Ok(RegistryKey {
                registry_id,
                unref_list: self.extra.borrow().registry_unref_list.clone(),
            })
        }
    }

    /// Get a value from the Lua registry by its `RegistryKey`
    ///
    /// Any Lua instance which shares the underlying main state may call this method to get a value
    /// previously placed by [`create_registry_value`].
    ///
    /// [`create_registry_value`]: #method.create_registry_value
    pub fn registry_value<T: FromLua>(&self, key: &RegistryKey) -> Result<T> {
        let value = unsafe {
            if !self.owns_registry_value(key) {
                return Err(Error::MismatchedRegistryKey);
            }

            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 2);

            ffi::lua_rawgeti(
                self.state,
                ffi::LUA_REGISTRYINDEX,
                key.registry_id as ffi::lua_Integer,
            );
            self.pop_value()
        };
        T::from_lua(value, self)
    }

    /// Removes a value from the Lua registry.
    ///
    /// You may call this function to manually remove a value placed in the registry with
    /// [`create_registry_value`]. In addition to manual `RegistryKey` removal, you can also call
    /// [`expire_registry_values`] to automatically remove values from the registry whose
    /// `RegistryKey`s have been dropped.
    ///
    /// [`create_registry_value`]: #method.create_registry_value
    /// [`expire_registry_values`]: #method.expire_registry_values
    pub fn remove_registry_value(&self, key: RegistryKey) -> Result<()> {
        unsafe {
            if !self.owns_registry_value(&key) {
                return Err(Error::MismatchedRegistryKey);
            }

            ffi::luaL_unref(self.state, ffi::LUA_REGISTRYINDEX, key.take());
            Ok(())
        }
    }

    /// Returns true if the given `RegistryKey` was created by a `Lua` which shares the underlying
    /// main state with this `Lua` instance.
    ///
    /// Other than this, methods that accept a `RegistryKey` will return
    /// `Error::MismatchedRegistryKey` if passed a `RegistryKey` that was not created with a
    /// matching `Lua` state.
    pub fn owns_registry_value(&self, key: &RegistryKey) -> bool {
        Arc::ptr_eq(&key.unref_list, &self.extra.borrow().registry_unref_list)
    }

    /// Remove any registry values whose `RegistryKey`s have all been dropped.
    ///
    /// Unlike normal handle values, `RegistryKey`s do not automatically remove themselves on Drop,
    /// but you can call this method to remove any unreachable registry values not manually removed
    /// by `Lua::remove_registry_value`.
    pub fn expire_registry_values(&self) {
        unsafe {
            let unref_list = mem::replace(
                &mut *mlua_expect!(
                    self.extra.borrow().registry_unref_list.lock(),
                    "unref list poisoned"
                ),
                Some(Vec::new()),
            );
            for id in mlua_expect!(unref_list, "unref list not set") {
                ffi::luaL_unref(self.state, ffi::LUA_REGISTRYINDEX, id);
            }
        }
    }

    // Uses 2 stack spaces, does not call checkstack
    pub(crate) unsafe fn push_value(&self, value: Value) -> Result<()> {
        match value {
            Value::Nil => {
                ffi::lua_pushnil(self.state);
            }

            Value::Boolean(b) => {
                ffi::lua_pushboolean(self.state, if b { 1 } else { 0 });
            }

            Value::LightUserData(ud) => {
                ffi::lua_pushlightuserdata(self.state, ud.0);
            }

            Value::Integer(i) => {
                ffi::lua_pushinteger(self.state, i);
            }

            Value::Number(n) => {
                ffi::lua_pushnumber(self.state, n);
            }

            Value::String(s) => {
                self.push_ref(&s.0);
            }

            Value::Table(t) => {
                self.push_ref(&t.0);
            }

            Value::Function(f) => {
                self.push_ref(&f.0);
            }

            Value::Thread(t) => {
                self.push_ref(&t.0);
            }

            Value::UserData(ud) => {
                self.push_ref(&ud.0);
            }

            Value::Error(e) => {
                push_wrapped_error(self.state, e)?;
            }
        }

        Ok(())
    }

    // Uses 2 stack spaces, does not call checkstack
    pub(crate) unsafe fn pop_value(&self) -> Value {
        match ffi::lua_type(self.state, -1) {
            ffi::LUA_TNIL => {
                ffi::lua_pop(self.state, 1);
                Nil
            }

            ffi::LUA_TBOOLEAN => {
                let b = Value::Boolean(ffi::lua_toboolean(self.state, -1) != 0);
                ffi::lua_pop(self.state, 1);
                b
            }

            ffi::LUA_TLIGHTUSERDATA => {
                let ud = Value::LightUserData(LightUserData(ffi::lua_touserdata(self.state, -1)));
                ffi::lua_pop(self.state, 1);
                ud
            }

            ffi::LUA_TNUMBER => {
                if ffi::lua_isinteger(self.state, -1) != 0 {
                    let i = Value::Integer(ffi::lua_tointeger(self.state, -1));
                    ffi::lua_pop(self.state, 1);
                    i
                } else {
                    let n = Value::Number(ffi::lua_tonumber(self.state, -1));
                    ffi::lua_pop(self.state, 1);
                    n
                }
            }

            ffi::LUA_TSTRING => Value::String(String(self.pop_ref())),

            ffi::LUA_TTABLE => Value::Table(Table(self.pop_ref())),

            ffi::LUA_TFUNCTION => Value::Function(Function(self.pop_ref())),

            ffi::LUA_TUSERDATA => {
                // It should not be possible to interact with userdata types other than custom
                // UserData types OR a WrappedError.  WrappedPanic should not be here.
                if let Some(err) = get_wrapped_error(self.state, -1).as_ref() {
                    let err = err.clone();
                    ffi::lua_pop(self.state, 1);
                    Value::Error(err)
                } else {
                    Value::UserData(AnyUserData(self.pop_ref()))
                }
            }

            ffi::LUA_TTHREAD => Value::Thread(Thread(self.pop_ref())),

            _ => mlua_panic!("LUA_TNONE in pop_value"),
        }
    }

    // Pushes a LuaRef value onto the stack, uses 1 stack space, does not call checkstack
    pub(crate) unsafe fn push_ref(&self, lref: &LuaRef) {
        assert!(
            lref.lua.main_state == self.main_state,
            "Lua instance passed Value created from a different main Lua state"
        );
        let extra = self.extra.borrow();
        ffi::lua_pushvalue(extra.ref_thread, lref.index);
        ffi::lua_xmove(extra.ref_thread, self.state, 1);
    }

    // Pops the topmost element of the stack and stores a reference to it.  This pins the object,
    // preventing garbage collection until the returned `LuaRef` is dropped.
    //
    // References are stored in the stack of a specially created auxiliary thread that exists only
    // to store reference values.  This is much faster than storing these in the registry, and also
    // much more flexible and requires less bookkeeping than storing them directly in the currently
    // used stack.  The implementation is somewhat biased towards the use case of a relatively small
    // number of short term references being created, and `RegistryKey` being used for long term
    // references.
    pub(crate) unsafe fn pop_ref(&self) -> LuaRef {
        let mut extra = self.extra.borrow_mut();
        ffi::lua_xmove(self.state, extra.ref_thread, 1);
        let index = ref_stack_pop(&mut extra);
        LuaRef {
            lua: self.clone(),
            index,
        }
    }

    pub(crate) fn clone_ref(&self, lref: &LuaRef) -> LuaRef {
        unsafe {
            let mut extra = self.extra.borrow_mut();
            ffi::lua_pushvalue(extra.ref_thread, lref.index);
            let index = ref_stack_pop(&mut extra);
            LuaRef {
                lua: self.clone(),
                index,
            }
        }
    }

    pub(crate) fn drop_ref(&self, lref: &mut LuaRef) {
        unsafe {
            let mut extra = self.extra.borrow_mut();
            ffi::lua_pushnil(extra.ref_thread);
            ffi::lua_replace(extra.ref_thread, lref.index);
            extra.ref_free.push(lref.index);
        }
    }

    pub(crate) unsafe fn userdata_metatable<T: 'static + UserData>(&self) -> Result<c_int> {
        if let Some(table_id) = self
            .extra
            .borrow()
            .registered_userdata
            .get(&TypeId::of::<T>())
        {
            return Ok(*table_id);
        }

        let _sg = StackGuard::new(self.state);
        assert_stack(self.state, 8);

        let mut methods = StaticUserDataMethods::default();
        T::add_methods(&mut methods);

        protect_lua_closure(self.state, 0, 1, |state| {
            ffi::lua_newtable(state);
        })?;
        for (k, m) in methods.meta_methods {
            push_string(self.state, k.name())?;
            self.push_value(Value::Function(self.create_callback(m)?))?;

            protect_lua_closure(self.state, 3, 1, |state| {
                ffi::lua_rawset(state, -3);
            })?;
        }

        if methods.methods.is_empty() {
            init_userdata_metatable::<RefCell<T>>(self.state, -1, None)?;
        } else {
            protect_lua_closure(self.state, 0, 1, |state| {
                ffi::lua_newtable(state);
            })?;
            for (k, m) in methods.methods {
                push_string(self.state, &k)?;
                self.push_value(Value::Function(self.create_callback(m)?))?;
                protect_lua_closure(self.state, 3, 1, |state| {
                    ffi::lua_rawset(state, -3);
                })?;
            }

            init_userdata_metatable::<RefCell<T>>(self.state, -2, Some(-1))?;
            ffi::lua_pop(self.state, 1);
        }

        let id = protect_lua_closure(self.state, 1, 0, |state| {
            ffi::luaL_ref(state, ffi::LUA_REGISTRYINDEX)
        })?;

        self.extra
            .borrow_mut()
            .registered_userdata
            .insert(TypeId::of::<T>(), id);

        Ok(id)
    }

    // Creates a Function out of a Callback containing a 'static Fn.  This is safe ONLY because the
    // Fn is 'static, otherwise it could capture 'callback arguments improperly.  Without ATCs, we
    // cannot easily deal with the "correct" callback type of:
    //
    // Box<for Fn(Rc<Lua>, MultiValue) -> Result<MultiValue>)>
    //
    // So we instead use a caller provided lifetime, which without the 'static requirement would be
    // unsafe.
    pub(crate) fn create_callback<'callback>(&self, func: Callback<'static>) -> Result<Function> {
        unsafe extern "C" fn call_callback(state: *mut ffi::lua_State) -> c_int {
            callback_error(state, |nargs| {
                let func = get_gc_userdata::<Callback>(state, ffi::lua_upvalueindex(1));
                let extra = get_gc_userdata::<Arc<RefCell<ExtraData>>>(state, ffi::lua_upvalueindex(2));
                if func.is_null() || extra.is_null() {
                    return Err(Error::CallbackDestructed);
                }

                if nargs < ffi::LUA_MINSTACK {
                    check_stack(state, ffi::LUA_MINSTACK - nargs)?;
                }

                let lua = Lua {
                    state: state,
                    main_state: get_main_state(state),
                    extra: (*extra).clone(),
                    ephemeral: true,
                    _no_ref_unwind_safe: PhantomData,
                };

                let mut args = MultiValue::new();
                args.reserve(nargs as usize);
                for _ in 0..nargs {
                    args.push_front(lua.pop_value());
                }

                let results = (*func)(&lua, args)?;
                let nresults = results.len() as c_int;

                check_stack(state, nresults)?;
                for r in results {
                    lua.push_value(r)?;
                }

                Ok(nresults)
            })
        }

        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 6);

            push_gc_userdata(self.state, func)?;
            push_gc_userdata::<Arc<RefCell<ExtraData>>>(self.state, self.extra.clone())?;

            protect_lua_closure(self.state, 2, 1, |state| {
                ffi::lua_pushcclosure(state, call_callback, 2);
            })?;

            Ok(Function(self.pop_ref()))
        }
    }

    pub(crate) fn create_async_callback<'callback>(
        &self,
        func: AsyncCallback<'static>,
    ) -> Result<Function> {
        unsafe extern "C" fn call_callback(state: *mut ffi::lua_State) -> c_int {
            callback_error(state, |nargs| {
                let func = get_gc_userdata::<AsyncCallback>(state, ffi::lua_upvalueindex(1));
                let extra = get_gc_userdata::<Arc<RefCell<ExtraData>>>(state, ffi::lua_upvalueindex(2));
                if func.is_null() || extra.is_null() {
                    return Err(Error::CallbackDestructed);
                }

                if nargs < ffi::LUA_MINSTACK {
                    check_stack(state, ffi::LUA_MINSTACK - nargs)?;
                }

                let lua = Lua {
                    state: state,
                    main_state: get_main_state(state),
                    extra: (*extra).clone(),
                    ephemeral: true,
                    _no_ref_unwind_safe: PhantomData,
                };

                let mut args = MultiValue::new();
                args.reserve(nargs as usize);
                for _ in 0..nargs {
                    args.push_front(lua.pop_value());
                }

                let fut = (*func)(lua, args);
                push_gc_userdata(state, fut)?;

                Ok(1)
            });

            poll_future(state)
        }

        unsafe extern "C" fn poll_future(state: *mut ffi::lua_State) -> c_int {
            let mut do_yield = false;
            let r = callback_error(state, |_nargs| {
                let fut = get_gc_userdata::<BoxFuture<Result<MultiValue>>>(state, -1);
                let extra = get_gc_userdata::<Arc<RefCell<ExtraData>>>(state, ffi::lua_upvalueindex(2));
                if fut.is_null() || extra.is_null() {
                    return Err(Error::CallbackDestructed);
                }

                let lua = Lua {
                    state: state,
                    main_state: get_main_state(state),
                    extra: (*extra).clone(),
                    ephemeral: true,
                    _no_ref_unwind_safe: PhantomData,
                };

                let mut waker = futures::task::noop_waker();

                // Try to get an outer poll waker
                ffi::lua_pushlightuserdata(
                    lua.state,
                    &WAKER_REGISTRY_KEY as *const u8 as *mut c_void,
                );
                ffi::lua_rawget(lua.state, ffi::LUA_REGISTRYINDEX);
                if let Some(w) = get_gc_userdata::<Waker>(lua.state, -1).as_ref() {
                    waker = (*w).clone();
                }
                ffi::lua_pop(lua.state, 1);

                let mut ctx = Context::from_waker(&waker);

                match (*fut).as_mut().poll(&mut ctx) {
                    Poll::Pending => {
                        push_gc_userdata(state, AsyncPollPending)?;
                        do_yield = true;
                        Ok(1)
                    }
                    Poll::Ready(results) => {
                        let results = results?;
                        let nresults = results.len() as c_int;

                        check_stack(state, nresults)?;
                        for r in results {
                            lua.push_value(r)?;
                        }

                        Ok(nresults)
                    }
                }
            });
            if do_yield {
                ffi::lua_yieldk(state, 1, 0, Some(continue_poll));
                unreachable!();
            }
            r
        }

        unsafe extern "C" fn continue_poll(
            state: *mut ffi::lua_State,
            _status: c_int,
            _ctx: ffi::lua_KContext,
        ) -> c_int {
            poll_future(state)
        }

        unsafe {
            let _sg = StackGuard::new(self.state);
            assert_stack(self.state, 6);

            push_gc_userdata(self.state, func)?;
            push_gc_userdata(self.state, self.extra.clone())?;

            protect_lua_closure(self.state, 2, 1, |state| {
                ffi::lua_pushcclosure(state, call_callback, 2);
            })?;

            Ok(Function(self.pop_ref()))
        }
    }

    // Does not require Send bounds, which can lead to unsafety.
    pub(crate) unsafe fn make_userdata<T>(&self, data: T) -> Result<AnyUserData>
    where
        T: 'static + UserData,
    {
        let _sg = StackGuard::new(self.state);
        assert_stack(self.state, 4);

        let ud_index = self.userdata_metatable::<T>()?;
        push_userdata::<RefCell<T>>(self.state, RefCell::new(data))?;

        ffi::lua_rawgeti(
            self.state,
            ffi::LUA_REGISTRYINDEX,
            ud_index as ffi::lua_Integer,
        );
        ffi::lua_setmetatable(self.state, -2);

        Ok(AnyUserData(self.pop_ref()))
    }
}

/// Returned from [`Lua::load`] and is used to finalize loading and executing Lua main chunks.
///
/// [`Lua::load`]: struct.Lua.html#method.load
#[must_use = "`Chunk`s do nothing unless one of `exec`, `eval`, `call`, or `into_function` are called on them"]
pub struct Chunk<'a> {
    lua: Lua,
    source: &'a [u8],
    name: Option<CString>,
    env: Option<Value>,
}

impl<'a> Chunk<'a> {
    /// Sets the name of this chunk, which results in more informative error traces.
    pub fn set_name<S: ?Sized + AsRef<[u8]>>(mut self, name: &S) -> Result<Chunk<'a>> {
        let name =
            CString::new(name.as_ref().to_vec()).map_err(|e| Error::ToLuaConversionError {
                from: "&str",
                to: "string",
                message: Some(e.to_string()),
            })?;
        self.name = Some(name);
        Ok(self)
    }

    /// Sets the first upvalue (`_ENV`) of the loaded chunk to the given value.
    ///
    /// Lua main chunks always have exactly one upvalue, and this upvalue is used as the `_ENV`
    /// variable inside the chunk.  By default this value is set to the global environment.
    ///
    /// Calling this method changes the `_ENV` upvalue to the value provided, and variables inside
    /// the chunk will refer to the given environment rather than the global one.
    ///
    /// All global variables (including the standard library!) are looked up in `_ENV`, so it may be
    /// necessary to populate the environment in order for scripts using custom environments to be
    /// useful.
    pub fn set_environment<V: ToLua>(mut self, env: V) -> Result<Chunk<'a>> {
        self.env = Some(env.to_lua(&self.lua)?);
        Ok(self)
    }

    /// Execute this chunk of code.
    ///
    /// This is equivalent to calling the chunk function with no arguments and no return values.
    pub fn exec(self) -> Result<()> {
        self.call(())?;
        Ok(())
    }

    /// Evaluate the chunk as either an expression or block.
    ///
    /// If the chunk can be parsed as an expression, this loads and executes the chunk and returns
    /// the value that it evaluates to.  Otherwise, the chunk is interpreted as a block as normal,
    /// and this is equivalent to calling `exec`.
    pub fn eval<R: FromLuaMulti>(self) -> Result<R> {
        // First, try interpreting the lua as an expression by adding
        // "return", then as a statement.  This is the same thing the
        // actual lua repl does.
        let mut expression_source = b"return ".to_vec();
        expression_source.extend(self.source);
        if let Ok(function) =
            self.lua
                .load_chunk(&expression_source, self.name.as_ref(), self.env.clone())
        {
            function.call(())
        } else {
            self.call(())
        }
    }

    /// Load the chunk function and call it with the given arguemnts.
    ///
    /// This is equivalent to `into_function` and calling the resulting function.
    pub fn call<A: ToLuaMulti, R: FromLuaMulti>(self, args: A) -> Result<R> {
        self.into_function()?.call(args)
    }

    /// Load this chunk into a regular `Function`.
    ///
    /// This simply compiles the chunk without actually executing it.
    pub fn into_function(self) -> Result<Function> {
        self.lua
            .load_chunk(self.source, self.name.as_ref(), self.env)
    }
}

unsafe fn load_from_std_lib(state: *mut ffi::lua_State, libs: StdLib) {
    #[cfg(any(feature = "lua53", feature = "lua52"))]
    {
        if libs.contains(StdLib::COROUTINE) {
            let colib_name = CString::new(ffi::LUA_COLIBNAME).unwrap();
            ffi::luaL_requiref(state, colib_name.as_ptr(), ffi::luaopen_coroutine, 1);
            ffi::lua_pop(state, 1);
        }
    }

    if libs.contains(StdLib::TABLE) {
        let tablib_name = CString::new(ffi::LUA_TABLIBNAME).unwrap();
        ffi::luaL_requiref(state, tablib_name.as_ptr(), ffi::luaopen_table, 1);
        ffi::lua_pop(state, 1);
    }

    if libs.contains(StdLib::IO) {
        let iolib_name = CString::new(ffi::LUA_IOLIBNAME).unwrap();
        ffi::luaL_requiref(state, iolib_name.as_ptr(), ffi::luaopen_io, 1);
        ffi::lua_pop(state, 1);
    }

    if libs.contains(StdLib::OS) {
        let oslib_name = CString::new(ffi::LUA_OSLIBNAME).unwrap();
        ffi::luaL_requiref(state, oslib_name.as_ptr(), ffi::luaopen_os, 1);
        ffi::lua_pop(state, 1);
    }

    if libs.contains(StdLib::STRING) {
        let strlib_name = CString::new(ffi::LUA_STRLIBNAME).unwrap();
        ffi::luaL_requiref(state, strlib_name.as_ptr(), ffi::luaopen_string, 1);
        ffi::lua_pop(state, 1);
    }

    #[cfg(feature = "lua53")]
    {
        if libs.contains(StdLib::UTF8) {
            let utf8lib_name = CString::new(ffi::LUA_UTF8LIBNAME).unwrap();
            ffi::luaL_requiref(state, utf8lib_name.as_ptr(), ffi::luaopen_utf8, 1);
            ffi::lua_pop(state, 1);
        }
    }

    #[cfg(feature = "lua52")]
    {
        if libs.contains(StdLib::BIT) {
            let bitlib_name = CString::new(ffi::LUA_BITLIBNAME).unwrap();
            ffi::luaL_requiref(state, bitlib_name.as_ptr(), ffi::luaopen_bit32, 1);
            ffi::lua_pop(state, 1);
        }
    }

    #[cfg(feature = "luajit")]
    {
        if libs.contains(StdLib::BIT) {
            let bitlib_name = CString::new(ffi::LUA_BITLIBNAME).unwrap();
            ffi::luaL_requiref(state, bitlib_name.as_ptr(), ffi::luaopen_bit, 1);
            ffi::lua_pop(state, 1);
        }
    }

    if libs.contains(StdLib::MATH) {
        let mathlib_name = CString::new(ffi::LUA_MATHLIBNAME).unwrap();
        ffi::luaL_requiref(state, mathlib_name.as_ptr(), ffi::luaopen_math, 1);
        ffi::lua_pop(state, 1);
    }

    if libs.contains(StdLib::DEBUG) {
        let dblib_name = CString::new(ffi::LUA_DBLIBNAME).unwrap();
        ffi::luaL_requiref(state, dblib_name.as_ptr(), ffi::luaopen_debug, 1);
        ffi::lua_pop(state, 1);
    }

    if libs.contains(StdLib::PACKAGE) {
        let loadlib_name = CString::new(ffi::LUA_LOADLIBNAME).unwrap();
        ffi::luaL_requiref(state, loadlib_name.as_ptr(), ffi::luaopen_package, 1);
        ffi::lua_pop(state, 1);
    }

    #[cfg(feature = "luajit")]
    {
        if libs.contains(StdLib::JIT) {
            let jitlib_name = CString::new(ffi::LUA_JITLIBNAME).unwrap();
            ffi::luaL_requiref(state, jitlib_name.as_ptr(), ffi::luaopen_jit, 1);
            ffi::lua_pop(state, 1);
        }

        if libs.contains(StdLib::FFI) {
            let ffilib_name = CString::new(ffi::LUA_FFILIBNAME).unwrap();
            ffi::luaL_requiref(state, ffilib_name.as_ptr(), ffi::luaopen_ffi, 1);
            ffi::lua_pop(state, 1);
        }
    }
}

unsafe fn ref_stack_pop(extra: &mut ExtraData) -> c_int {
    if let Some(free) = extra.ref_free.pop() {
        ffi::lua_replace(extra.ref_thread, free);
        free
    } else {
        if extra.ref_stack_max >= extra.ref_stack_size {
            // It is a user error to create enough references to exhaust the Lua max stack size for
            // the ref thread.
            if ffi::lua_checkstack(extra.ref_thread, extra.ref_stack_size) == 0 {
                mlua_panic!("cannot create a Lua reference, out of auxiliary stack space");
            }
            extra.ref_stack_size *= 2;
        }
        extra.ref_stack_max += 1;
        extra.ref_stack_max
    }
}

struct StaticUserDataMethods<T: 'static + UserData> {
    methods: Vec<(Vec<u8>, Callback<'static>)>,
    meta_methods: Vec<(MetaMethod, Callback<'static>)>,
    _type: PhantomData<T>,
}

impl<T: 'static + UserData> Default for StaticUserDataMethods<T> {
    fn default() -> StaticUserDataMethods<T> {
        StaticUserDataMethods {
            methods: Vec::new(),
            meta_methods: Vec::new(),
            _type: PhantomData,
        }
    }
}

impl<T: 'static + UserData> UserDataMethods<T> for StaticUserDataMethods<T> {
    fn add_method<S, A, R, M>(&mut self, name: &S, method: M)
    where
        S: ?Sized + AsRef<[u8]>,
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + Fn(&Lua, &T, A) -> Result<R>,
    {
        self.methods
            .push((name.as_ref().to_vec(), Self::box_method(method)));
    }

    fn add_method_mut<S, A, R, M>(&mut self, name: &S, method: M)
    where
        S: ?Sized + AsRef<[u8]>,
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + FnMut(&Lua, &mut T, A) -> Result<R>,
    {
        self.methods
            .push((name.as_ref().to_vec(), Self::box_method_mut(method)));
    }

    fn add_function<S, A, R, F>(&mut self, name: &S, function: F)
    where
        S: ?Sized + AsRef<[u8]>,
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + Fn(&Lua, A) -> Result<R>,
    {
        self.methods
            .push((name.as_ref().to_vec(), Self::box_function(function)));
    }

    fn add_function_mut<S, A, R, F>(&mut self, name: &S, function: F)
    where
        S: ?Sized + AsRef<[u8]>,
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + FnMut(&Lua, A) -> Result<R>,
    {
        self.methods
            .push((name.as_ref().to_vec(), Self::box_function_mut(function)));
    }

    fn add_meta_method<A, R, M>(&mut self, meta: MetaMethod, method: M)
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + Fn(&Lua, &T, A) -> Result<R>,
    {
        self.meta_methods.push((meta, Self::box_method(method)));
    }

    fn add_meta_method_mut<A, R, M>(&mut self, meta: MetaMethod, method: M)
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + FnMut(&Lua, &mut T, A) -> Result<R>,
    {
        self.meta_methods.push((meta, Self::box_method_mut(method)));
    }

    fn add_meta_function<A, R, F>(&mut self, meta: MetaMethod, function: F)
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + Fn(&Lua, A) -> Result<R>,
    {
        self.meta_methods.push((meta, Self::box_function(function)));
    }

    fn add_meta_function_mut<A, R, F>(&mut self, meta: MetaMethod, function: F)
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + FnMut(&Lua, A) -> Result<R>,
    {
        self.meta_methods
            .push((meta, Self::box_function_mut(function)));
    }
}

impl<T: 'static + UserData> StaticUserDataMethods<T> {
    fn box_method<A, R, M>(method: M) -> Callback<'static>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + Fn(&Lua, &T, A) -> Result<R>,
    {
        Box::new(move |lua, mut args| {
            if let Some(front) = args.pop_front() {
                let userdata = AnyUserData::from_lua(front, lua)?;
                let userdata = userdata.borrow::<T>()?;
                method(lua, &userdata, A::from_lua_multi(args, lua)?)?.to_lua_multi(lua)
            } else {
                Err(Error::FromLuaConversionError {
                    from: "missing argument",
                    to: "userdata",
                    message: None,
                })
            }
        })
    }

    fn box_method_mut<A, R, M>(method: M) -> Callback<'static>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        M: 'static + Send + FnMut(&Lua, &mut T, A) -> Result<R>,
    {
        let method = RefCell::new(method);
        Box::new(move |lua, mut args| {
            if let Some(front) = args.pop_front() {
                let userdata = AnyUserData::from_lua(front, lua)?;
                let mut userdata = userdata.borrow_mut::<T>()?;
                let mut method = method
                    .try_borrow_mut()
                    .map_err(|_| Error::RecursiveMutCallback)?;
                (&mut *method)(lua, &mut userdata, A::from_lua_multi(args, lua)?)?.to_lua_multi(lua)
            } else {
                Err(Error::FromLuaConversionError {
                    from: "missing argument",
                    to: "userdata",
                    message: None,
                })
            }
        })
    }

    fn box_function<A, R, F>(function: F) -> Callback<'static>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + Fn(&Lua, A) -> Result<R>,
    {
        Box::new(move |lua, args| function(lua, A::from_lua_multi(args, lua)?)?.to_lua_multi(lua))
    }

    fn box_function_mut<A, R, F>(function: F) -> Callback<'static>
    where
        A: FromLuaMulti,
        R: ToLuaMulti,
        F: 'static + Send + FnMut(&Lua, A) -> Result<R>,
    {
        let function = RefCell::new(function);
        Box::new(move |lua, args| {
            let function = &mut *function
                .try_borrow_mut()
                .map_err(|_| Error::RecursiveMutCallback)?;
            function(lua, A::from_lua_multi(args, lua)?)?.to_lua_multi(lua)
        })
    }
}
