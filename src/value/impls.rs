//! Trait implementations for VDF types.

use alloc::borrow::Cow;
use alloc::string::String;

use super::types::{Key, Obj, Value, Vdf};
use core::fmt;
use core::ops::Index;

// ============================================================================
// From implementations for Value
// ============================================================================

impl<'text> From<&'text str> for Value<'text> {
    fn from(s: &'text str) -> Self {
        Value::Str(Cow::Borrowed(s))
    }
}

impl From<String> for Value<'static> {
    fn from(s: String) -> Self {
        Value::Str(Cow::Owned(s))
    }
}

impl From<i32> for Value<'static> {
    fn from(n: i32) -> Self {
        Value::I32(n)
    }
}

impl From<u64> for Value<'static> {
    fn from(n: u64) -> Self {
        Value::U64(n)
    }
}

impl From<f32> for Value<'static> {
    fn from(n: f32) -> Self {
        Value::Float(n)
    }
}

impl From<u32> for Value<'static> {
    fn from(n: u32) -> Self {
        Value::Pointer(n)
    }
}

impl From<[u8; 4]> for Value<'static> {
    fn from(color: [u8; 4]) -> Self {
        Value::Color(color)
    }
}

impl<'text> From<Obj<'text>> for Value<'text> {
    fn from(obj: Obj<'text>) -> Self {
        Value::Obj(obj)
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

impl<'text> fmt::Display for Vdf<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.key(), self.value())
    }
}

// ============================================================================
// IntoIterator implementations for Obj
// ============================================================================

impl<'text> IntoIterator for Obj<'text> {
    type Item = (Key<'text>, Value<'text>);
    type IntoIter = hashbrown::hash_map::IntoIter<Key<'text>, Value<'text>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, 'text> IntoIterator for &'a Obj<'text> {
    type Item = (&'a Key<'text>, &'a Value<'text>);
    type IntoIter = hashbrown::hash_map::Iter<'a, Key<'text>, Value<'text>>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

// ============================================================================
// Index implementations for Value and Obj
// ============================================================================

impl<'text> Index<&str> for Value<'text> {
    type Output = Value<'text>;

    /// Returns a reference to the value at the given key.
    ///
    /// # Panics
    ///
    /// Panics if this is not an object or if the key doesn't exist.
    /// Use `get()` for non-panicking access.
    fn index(&self, key: &str) -> &Self::Output {
        self.get(key).expect("key not found in Value")
    }
}

impl<'text> Index<&str> for Obj<'text> {
    type Output = Value<'text>;

    /// Returns a reference to the value at the given key.
    ///
    /// # Panics
    ///
    /// Panics if the key doesn't exist. Use `get()` for non-panicking access.
    fn index(&self, key: &str) -> &Self::Output {
        self.get(key).expect("key not found in Obj")
    }
}
