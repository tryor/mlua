use std::collections::{BTreeMap, HashMap};
use std::ffi::{CStr, CString};
use std::hash::{BuildHasher, Hash};
use std::string::String as StdString;

use bstr::{BStr, BString};
use num_traits::cast;

use crate::error::{Error, Result};
use crate::function::Function;
use crate::lua::Lua;
use crate::string::String;
use crate::table::Table;
use crate::thread::Thread;
use crate::types::{LightUserData, Number};
use crate::userdata::{AnyUserData, UserData};
use crate::value::{FromLua, Nil, ToLua, Value};

impl ToLua for Value {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(self)
    }
}

impl FromLua for Value {
    fn from_lua(lua_value: Value, _: &Lua) -> Result<Self> {
        Ok(lua_value)
    }
}

impl ToLua for String {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::String(self))
    }
}

impl FromLua for String {
    fn from_lua(value: Value, lua: &Lua) -> Result<String> {
        let ty = value.type_name();
        lua.coerce_string(value)?
            .ok_or_else(|| Error::FromLuaConversionError {
                from: ty,
                to: "String",
                message: Some("expected string or number".to_string()),
            })
    }
}

impl ToLua for Table {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::Table(self))
    }
}

impl FromLua for Table {
    fn from_lua(value: Value, _: &Lua) -> Result<Table> {
        match value {
            Value::Table(table) => Ok(table),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "table",
                message: None,
            }),
        }
    }
}

impl ToLua for Function {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::Function(self))
    }
}

impl FromLua for Function {
    fn from_lua(value: Value, _: &Lua) -> Result<Function> {
        match value {
            Value::Function(table) => Ok(table),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "function",
                message: None,
            }),
        }
    }
}

impl ToLua for Thread {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::Thread(self))
    }
}

impl FromLua for Thread {
    fn from_lua(value: Value, _: &Lua) -> Result<Thread> {
        match value {
            Value::Thread(t) => Ok(t),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "thread",
                message: None,
            }),
        }
    }
}

impl ToLua for AnyUserData {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::UserData(self))
    }
}

impl FromLua for AnyUserData {
    fn from_lua(value: Value, _: &Lua) -> Result<AnyUserData> {
        match value {
            Value::UserData(ud) => Ok(ud),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "userdata",
                message: None,
            }),
        }
    }
}

impl<T: 'static + UserData> ToLua for T {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::UserData(lua.create_userdata(self)?))
    }
}

impl<T: 'static + UserData + Clone> FromLua for T {
    fn from_lua(value: Value, _: &Lua) -> Result<T> {
        match value {
            Value::UserData(ud) => Ok(ud.borrow::<T>()?.clone()),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "userdata",
                message: None,
            }),
        }
    }
}

impl ToLua for Error {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::Error(self))
    }
}

impl FromLua for Error {
    fn from_lua(value: Value, lua: &Lua) -> Result<Error> {
        match value {
            Value::Error(err) => Ok(err),
            val => Ok(Error::RuntimeError(
                lua.coerce_string(val)?
                    .and_then(|s| Some(s.to_str().ok()?.to_owned()))
                    .unwrap_or_else(|| "<unprintable error>".to_owned()),
            )),
        }
    }
}

impl ToLua for bool {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::Boolean(self))
    }
}

impl FromLua for bool {
    fn from_lua(v: Value, _: &Lua) -> Result<Self> {
        match v {
            Value::Nil => Ok(false),
            Value::Boolean(b) => Ok(b),
            _ => Ok(true),
        }
    }
}

impl ToLua for LightUserData {
    fn to_lua(self, _: &Lua) -> Result<Value> {
        Ok(Value::LightUserData(self))
    }
}

impl FromLua for LightUserData {
    fn from_lua(value: Value, _: &Lua) -> Result<Self> {
        match value {
            Value::LightUserData(ud) => Ok(ud),
            _ => Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "light userdata",
                message: None,
            }),
        }
    }
}

impl ToLua for StdString {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(&self)?))
    }
}

impl FromLua for StdString {
    fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
        let ty = value.type_name();
        Ok(lua
            .coerce_string(value)?
            .ok_or_else(|| Error::FromLuaConversionError {
                from: ty,
                to: "String",
                message: Some("expected string or number".to_string()),
            })?
            .to_str()?
            .to_owned())
    }
}

impl<'a> ToLua for &'a str {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(self)?))
    }
}

impl ToLua for CString {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(self.as_bytes())?))
    }
}

impl FromLua for CString {
    fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
        let ty = value.type_name();
        let string = lua
            .coerce_string(value)?
            .ok_or_else(|| Error::FromLuaConversionError {
                from: ty,
                to: "CString",
                message: Some("expected string or number".to_string()),
            })?;

        match CStr::from_bytes_with_nul(string.as_bytes_with_nul()) {
            Ok(s) => Ok(s.into()),
            Err(_) => Err(Error::FromLuaConversionError {
                from: ty,
                to: "CString",
                message: Some("invalid C-style string".to_string()),
            }),
        }
    }
}

impl<'a> ToLua for &'a CStr {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(self.to_bytes())?))
    }
}

impl<'a> ToLua for BString {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(&self)?))
    }
}

impl FromLua for BString {
    fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
        let ty = value.type_name();
        Ok(BString::from(
            lua.coerce_string(value)?
                .ok_or_else(|| Error::FromLuaConversionError {
                    from: ty,
                    to: "String",
                    message: Some("expected string or number".to_string()),
                })?
                .as_bytes()
                .to_vec(),
        ))
    }
}

impl<'a> ToLua for &BStr {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::String(lua.create_string(&self)?))
    }
}

macro_rules! lua_convert_int {
    ($x:ty) => {
        impl ToLua for $x {
            fn to_lua(self, _: &Lua) -> Result<Value> {
                if let Some(i) = cast(self) {
                    Ok(Value::Integer(i))
                } else {
                    cast(self)
                        .ok_or_else(|| Error::ToLuaConversionError {
                            from: stringify!($x),
                            to: "number",
                            message: Some("out of range".to_owned()),
                        })
                        .map(Value::Number)
                }
            }
        }

        impl FromLua for $x {
            fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
                let ty = value.type_name();
                (if let Some(i) = lua.coerce_integer(value.clone())? {
                    cast(i)
                } else {
                    cast(lua.coerce_number(value)?.ok_or_else(|| {
                        Error::FromLuaConversionError {
                            from: ty,
                            to: stringify!($x),
                            message: Some(
                                "expected number or string coercible to number".to_string(),
                            ),
                        }
                    })?)
                })
                .ok_or_else(|| Error::FromLuaConversionError {
                    from: ty,
                    to: stringify!($x),
                    message: Some("out of range".to_owned()),
                })
            }
        }
    };
}

lua_convert_int!(i8);
lua_convert_int!(u8);
lua_convert_int!(i16);
lua_convert_int!(u16);
lua_convert_int!(i32);
lua_convert_int!(u32);
lua_convert_int!(i64);
lua_convert_int!(u64);
lua_convert_int!(i128);
lua_convert_int!(u128);
lua_convert_int!(isize);
lua_convert_int!(usize);

macro_rules! lua_convert_float {
    ($x:ty) => {
        impl ToLua for $x {
            fn to_lua(self, _: &Lua) -> Result<Value> {
                Ok(Value::Number(self as Number))
            }
        }

        impl FromLua for $x {
            fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
                let ty = value.type_name();
                lua.coerce_number(value)?
                    .ok_or_else(|| Error::FromLuaConversionError {
                        from: ty,
                        to: stringify!($x),
                        message: Some("expected number or string coercible to number".to_string()),
                    })
                    .and_then(|n| {
                        cast(n).ok_or_else(|| Error::FromLuaConversionError {
                            from: ty,
                            to: stringify!($x),
                            message: Some("number out of range".to_string()),
                        })
                    })
            }
        }
    };
}

lua_convert_float!(f32);
lua_convert_float!(f64);

impl<T: ToLua> ToLua for Vec<T> {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::Table(lua.create_sequence_from(self)?))
    }
}

impl<T: FromLua> FromLua for Vec<T> {
    fn from_lua(value: Value, _: &Lua) -> Result<Self> {
        if let Value::Table(table) = value {
            table.sequence_values().collect()
        } else {
            Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "Vec",
                message: Some("expected table".to_string()),
            })
        }
    }
}

impl<K: Eq + Hash + ToLua, V: ToLua, S: BuildHasher> ToLua for HashMap<K, V, S> {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::Table(lua.create_table_from(self)?))
    }
}

impl<K: Eq + Hash + FromLua, V: FromLua, S: BuildHasher + Default> FromLua for HashMap<K, V, S> {
    fn from_lua(value: Value, _: &Lua) -> Result<Self> {
        if let Value::Table(table) = value {
            table.pairs().collect()
        } else {
            Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "HashMap",
                message: Some("expected table".to_string()),
            })
        }
    }
}

impl<K: Ord + ToLua, V: ToLua> ToLua for BTreeMap<K, V> {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        Ok(Value::Table(lua.create_table_from(self)?))
    }
}

impl<K: Ord + FromLua, V: FromLua> FromLua for BTreeMap<K, V> {
    fn from_lua(value: Value, _: &Lua) -> Result<Self> {
        if let Value::Table(table) = value {
            table.pairs().collect()
        } else {
            Err(Error::FromLuaConversionError {
                from: value.type_name(),
                to: "BTreeMap",
                message: Some("expected table".to_string()),
            })
        }
    }
}

impl<T: ToLua> ToLua for Option<T> {
    fn to_lua(self, lua: &Lua) -> Result<Value> {
        match self {
            Some(val) => val.to_lua(lua),
            None => Ok(Nil),
        }
    }
}

impl<T: FromLua> FromLua for Option<T> {
    fn from_lua(value: Value, lua: &Lua) -> Result<Self> {
        match value {
            Nil => Ok(None),
            value => Ok(Some(T::from_lua(value, lua)?)),
        }
    }
}
