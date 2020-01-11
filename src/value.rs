use std::iter::{self, FromIterator};
use std::{slice, str, vec};

use crate::error::{Error, Result};
use crate::ffi;
use crate::function::Function;
use crate::lua::Lua;
use crate::string::String;
use crate::table::Table;
use crate::thread::Thread;
use crate::types::{Integer, LightUserData, Number};
use crate::userdata::AnyUserData;

/// A dynamically typed Lua value.  The `String`, `Table`, `Function`, `Thread`, and `UserData`
/// variants contain handle types into the internal Lua state.  It is a logic error to mix handle
/// types between separate `Lua` instances, or between a parent `Lua` instance and one received as a
/// parameter in a Rust callback, and doing so will result in a panic.
#[derive(Debug, Clone)]
pub enum Value {
    /// The Lua value `nil`.
    Nil,
    /// The Lua value `true` or `false`.
    Boolean(bool),
    /// A "light userdata" object, equivalent to a raw pointer.
    LightUserData(LightUserData),
    /// An integer number.
    ///
    /// Any Lua number convertible to a `Integer` will be represented as this variant.
    Integer(Integer),
    /// A floating point number.
    Number(Number),
    /// An interned string, managed by Lua.
    ///
    /// Unlike Rust strings, Lua strings may not be valid UTF-8.
    String(String),
    /// Reference to a Lua table.
    Table(Table),
    /// Reference to a Lua function (or closure).
    Function(Function),
    /// Reference to a Lua thread (or coroutine).
    Thread(Thread),
    /// Reference to a userdata object that holds a custom type which implements `UserData`.
    /// Special builtin userdata types will be represented as other `Value` variants.
    UserData(AnyUserData),
    /// `Error` is a special builtin userdata type.  When received from Lua it is implicitly cloned.
    Error(Error),
}
pub use self::Value::Nil;

impl Value {
    pub fn type_name(&self) -> &'static str {
        match *self {
            Value::Nil => "nil",
            Value::Boolean(_) => "boolean",
            Value::LightUserData(_) => "lightuserdata",
            Value::Integer(_) => "integer",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Table(_) => "table",
            Value::Function(_) => "function",
            Value::Thread(_) => "thread",
            Value::UserData(_) => "userdata",
            Value::Error(_) => "error",
        }
    }

    /// Compares two values for equality.
    ///
    /// Equality comparisons do not convert strings to numbers or vice versa.
    /// Tables, Functions, Threads, and Userdata are compared by reference:
    /// two objects are considered equal only if they are the same object.
    ///
    /// If Tables or Userdata have `__eq` metamethod then mlua will try to invoke it.
    /// The first value is checked first. If that value does not define a metamethod
    /// for `__eq`, then mlua will check the second value.
    /// Then mlua calls the metamethod with the two values as arguments, if found.
    pub fn equals<T: AsRef<Self>>(&self, other: T) -> Result<bool> {
        match (self, other.as_ref()) {
            (Value::Table(a), Value::Table(b)) => a.equals(b),
            (Value::UserData(a), Value::UserData(b)) => a.equals(b),
            _ => Ok(self == other.as_ref()),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Boolean(a), Value::Boolean(b)) => a == b,
            (Value::LightUserData(a), Value::LightUserData(b)) => a == b,
            (Value::Integer(a), Value::Integer(b)) => *a == *b,
            (Value::Integer(a), Value::Number(b)) => *a as ffi::lua_Number == *b,
            (Value::Number(a), Value::Integer(b)) => *a == *b as ffi::lua_Number,
            (Value::Number(a), Value::Number(b)) => *a == *b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Table(a), Value::Table(b)) => a == b,
            (Value::Function(a), Value::Function(b)) => a == b,
            (Value::Thread(a), Value::Thread(b)) => a == b,
            (Value::UserData(a), Value::UserData(b)) => a == b,
            _ => false,
        }
    }
}

impl AsRef<Value> for Value {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

/// Trait for types convertible to `Value`.
pub trait ToLua {
    /// Performs the conversion.
    fn to_lua(self, lua: &Lua) -> Result<Value>;
}

/// Trait for types convertible from `Value`.
pub trait FromLua: Sized {
    /// Performs the conversion.
    fn from_lua(lua_value: Value, lua: &Lua) -> Result<Self>;
}

/// Multiple Lua values used for both argument passing and also for multiple return values.
#[derive(Debug, Clone)]
pub struct MultiValue(Vec<Value>);

impl MultiValue {
    /// Creates an empty `MultiValue` containing no values.
    pub fn new() -> MultiValue {
        MultiValue(Vec::new())
    }
}

impl Default for MultiValue {
    fn default() -> MultiValue {
        MultiValue::new()
    }
}

impl FromIterator<Value> for MultiValue {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        MultiValue::from_vec(Vec::from_iter(iter))
    }
}

impl IntoIterator for MultiValue {
    type Item = Value;
    type IntoIter = iter::Rev<vec::IntoIter<Value>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().rev()
    }
}

impl<'a> IntoIterator for &'a MultiValue {
    type Item = &'a Value;
    type IntoIter = iter::Rev<slice::Iter<'a, Value>>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter().rev()
    }
}

impl MultiValue {
    pub fn from_vec(mut v: Vec<Value>) -> MultiValue {
        v.reverse();
        MultiValue(v)
    }

    pub fn into_vec(self) -> Vec<Value> {
        let mut v = self.0;
        v.reverse();
        v
    }

    pub(crate) fn reserve(&mut self, size: usize) {
        self.0.reserve(size);
    }

    pub(crate) fn push_front(&mut self, value: Value) {
        self.0.push(value);
    }

    pub(crate) fn pop_front(&mut self) -> Option<Value> {
        self.0.pop()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    pub fn iter(&self) -> iter::Rev<slice::Iter<Value>> {
        self.0.iter().rev()
    }
}

/// Trait for types convertible to any number of Lua values.
///
/// This is a generalization of `ToLua`, allowing any number of resulting Lua values instead of just
/// one. Any type that implements `ToLua` will automatically implement this trait.
pub trait ToLuaMulti {
    /// Performs the conversion.
    fn to_lua_multi(self, lua: &Lua) -> Result<MultiValue>;
}

/// Trait for types that can be created from an arbitrary number of Lua values.
///
/// This is a generalization of `FromLua`, allowing an arbitrary number of Lua values to participate
/// in the conversion. Any type that implements `FromLua` will automatically implement this trait.
pub trait FromLuaMulti: Sized {
    /// Performs the conversion.
    ///
    /// In case `values` contains more values than needed to perform the conversion, the excess
    /// values should be ignored. This reflects the semantics of Lua when calling a function or
    /// assigning values. Similarly, if not enough values are given, conversions should assume that
    /// any missing values are nil.
    fn from_lua_multi(values: MultiValue, lua: &Lua) -> Result<Self>;
}
