//! Core data structures for VDF representation.

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;

/// A key in VDF - zero-copy when possible
pub type Key<'text> = Cow<'text, str>;

/// VDF Value - can be a string, number, object, or other types
#[derive(Clone, Debug, PartialEq)]
pub enum Value<'text> {
    /// A string value (text format and WideString from binary)
    Str(Cow<'text, str>),
    /// An object containing nested key-value pairs
    Obj(Obj<'text>),
    /// A 32-bit signed integer (binary Int32 type)
    I32(i32),
    /// A 64-bit unsigned integer (binary UInt64 type)
    U64(u64),
    /// A 32-bit float (binary Float type)
    Float(f32),
    /// A pointer value (binary Ptr type, stored as u32)
    Pointer(u32),
    /// A color value (binary Color type, RGBA)
    Color([u8; 4]),
}

impl<'text> Value<'text> {
    /// Returns `true` if this value is a string.
    pub fn is_str(&self) -> bool {
        matches!(self, Value::Str(_))
    }

    /// Returns `true` if this value is an object.
    pub fn is_obj(&self) -> bool {
        matches!(self, Value::Obj(_))
    }

    /// Returns `true` if this value is an i32.
    pub fn is_i32(&self) -> bool {
        matches!(self, Value::I32(_))
    }

    /// Returns `true` if this value is a u64.
    pub fn is_u64(&self) -> bool {
        matches!(self, Value::U64(_))
    }

    /// Returns `true` if this value is a float.
    pub fn is_float(&self) -> bool {
        matches!(self, Value::Float(_))
    }

    /// Returns `true` if this value is a pointer.
    pub fn is_pointer(&self) -> bool {
        matches!(self, Value::Pointer(_))
    }

    /// Returns `true` if this value is a color.
    pub fn is_color(&self) -> bool {
        matches!(self, Value::Color(_))
    }

    /// Returns a reference to the string value if this is a string.
    pub fn as_str(&self) -> Option<&Cow<'text, str>> {
        match self {
            Value::Str(s) => Some(s),
            _ => None,
        }
    }

    /// Returns a reference to the object if this is an object.
    pub fn as_obj(&self) -> Option<&Obj<'text>> {
        match self {
            Value::Obj(obj) => Some(obj),
            _ => None,
        }
    }

    /// Returns the i32 value if this is an i32.
    pub fn as_i32(&self) -> Option<i32> {
        match self {
            Value::I32(n) => Some(*n),
            _ => None,
        }
    }

    /// Returns the u64 value if this is a u64.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Value::U64(n) => Some(*n),
            _ => None,
        }
    }

    /// Returns the float value if this is a float.
    pub fn as_float(&self) -> Option<f32> {
        match self {
            Value::Float(n) => Some(*n),
            _ => None,
        }
    }

    /// Returns the pointer value if this is a pointer.
    pub fn as_pointer(&self) -> Option<u32> {
        match self {
            Value::Pointer(n) => Some(*n),
            _ => None,
        }
    }

    /// Returns the color value if this is a color.
    pub fn as_color(&self) -> Option<[u8; 4]> {
        match self {
            Value::Color(c) => Some(*c),
            _ => None,
        }
    }
}

impl<'text> fmt::Display for Value<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Str(s) => write!(f, "{}", s),
            Value::Obj(obj) => write!(f, "{}", obj),
            Value::I32(n) => write!(f, "{}", n),
            Value::U64(n) => write!(f, "{}", n),
            Value::Float(n) => write!(f, "{}", n),
            Value::Pointer(n) => write!(f, "0x{:08x}", n),
            Value::Color(c) => write!(f, "{}{}{}{}", c[0], c[1], c[2], c[3]),
        }
    }
}

/// Object - map from keys to values
///
/// Uses `HashMap` for O(1) lookup. Binary VDF doesn't have duplicate keys,
/// and for text VDF we use "last value wins" semantics.
#[derive(Clone, Debug, PartialEq)]
pub struct Obj<'text> {
    pub(crate) inner: HashMap<Key<'text>, Value<'text>>,
}

impl<'text> Obj<'text> {
    /// Creates a new empty object.
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Returns the number of key-value pairs in the object.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the object contains no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, key: &str) -> Option<&Value<'text>> {
        self.inner.get(key)
    }

    /// Returns an iterator over the key-value pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&Key<'text>, &Value<'text>)> {
        self.inner.iter()
    }

    /// Inserts a key-value pair into the object.
    pub(crate) fn insert(&mut self, key: Key<'text>, value: Value<'text>) {
        self.inner.insert(key, value);
    }
}

impl<'text> Default for Obj<'text> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'text> fmt::Display for Obj<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (key, value)) in self.inner.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", key, value)?;
        }
        write!(f, "}}")
    }
}

/// Top-level VDF document
///
/// A VDF document is essentially a single key-value pair at the root level.
#[derive(Clone, Debug, PartialEq)]
pub struct Vdf<'text> {
    /// The root key
    pub key: Key<'text>,
    /// The root value (typically an object)
    pub value: Value<'text>,
}

impl<'text> Vdf<'text> {
    /// Creates a new VDF document.
    pub fn new(key: Key<'text>, value: Value<'text>) -> Self {
        Self { key, value }
    }

    /// Returns `true` if the root value is an object.
    pub fn is_obj(&self) -> bool {
        self.value.is_obj()
    }

    /// Returns a reference to the root object if it is one.
    pub fn as_obj(&self) -> Option<&Obj<'text>> {
        self.value.as_obj()
    }
}

impl<'text> fmt::Display for Vdf<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.key, self.value)
    }
}
