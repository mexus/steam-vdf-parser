//! Core data structures for VDF representation.

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;

/// A key in VDF - zero-copy when possible
pub type Key<'text> = Cow<'text, str>;

/// VDF Value - either a string or an object (nested map)
#[derive(Clone, Debug, PartialEq)]
pub enum Value<'text> {
    /// A string value
    Str(Cow<'text, str>),
    /// An object containing nested key-value pairs
    Obj(Obj<'text>),
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
}

impl<'text> fmt::Display for Value<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Str(s) => write!(f, "{}", s),
            Value::Obj(obj) => write!(f, "{}", obj),
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
