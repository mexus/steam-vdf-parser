//! Core data structures for VDF representation.

use alloc::borrow::Cow;
use core::fmt;
use hashbrown::HashMap;

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

    /// Returns a reference to a nested value by key.
    ///
    /// Shorthand for `self.as_obj()?.get(key)`.
    pub fn get(&self, key: &str) -> Option<&Value<'text>> {
        self.as_obj()?.get(key)
    }

    /// Traverse nested objects by path.
    ///
    /// Returns `None` if any segment doesn't exist or isn't an object.
    pub fn get_path(&self, path: &[&str]) -> Option<&Value<'text>> {
        let mut current = self;
        for key in path {
            current = current.get(key)?;
        }
        Some(current)
    }

    /// Get a string at the given path.
    pub fn get_str(&self, path: &[&str]) -> Option<&Cow<'text, str>> {
        self.get_path(path)?.as_str()
    }

    /// Get an object at the given path.
    pub fn get_obj(&self, path: &[&str]) -> Option<&Obj<'text>> {
        self.get_path(path)?.as_obj()
    }

    /// Get an i32 at the given path.
    pub fn get_i32(&self, path: &[&str]) -> Option<i32> {
        self.get_path(path)?.as_i32()
    }

    /// Get a u64 at the given path.
    pub fn get_u64(&self, path: &[&str]) -> Option<u64> {
        self.get_path(path)?.as_u64()
    }

    /// Get a float at the given path.
    pub fn get_float(&self, path: &[&str]) -> Option<f32> {
        self.get_path(path)?.as_float()
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
    /// Creates a new empty VDF object.
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

    /// Returns a reference to a nested value by key.
    pub fn get(&self, key: &str) -> Option<&Value<'text>> {
        self.value.get(key)
    }

    /// Traverse nested objects by path from the root value.
    pub fn get_path(&self, path: &[&str]) -> Option<&Value<'text>> {
        self.value.get_path(path)
    }

    /// Get a string at the given path.
    pub fn get_str(&self, path: &[&str]) -> Option<&Cow<'text, str>> {
        self.value.get_str(path)
    }

    /// Get an object at the given path.
    pub fn get_obj(&self, path: &[&str]) -> Option<&Obj<'text>> {
        self.value.get_obj(path)
    }

    /// Get an i32 at the given path.
    pub fn get_i32(&self, path: &[&str]) -> Option<i32> {
        self.value.get_i32(path)
    }

    /// Get a u64 at the given path.
    pub fn get_u64(&self, path: &[&str]) -> Option<u64> {
        self.value.get_u64(path)
    }

    /// Get a float at the given path.
    pub fn get_float(&self, path: &[&str]) -> Option<f32> {
        self.value.get_float(path)
    }
}

impl<'text> fmt::Display for Vdf<'text> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.key, self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::ToString;

    #[test]
    fn test_value_is_methods() {
        let v = Value::I32(42);
        assert!(v.is_i32());
        assert!(!v.is_str());
        assert!(!v.is_obj());
    }

    #[test]
    fn test_value_is_str() {
        let v = Value::Str(Cow::Borrowed("test"));
        assert!(v.is_str());
        assert!(!v.is_i32());
    }

    #[test]
    fn test_value_is_obj() {
        let v = Value::Obj(Obj::new());
        assert!(v.is_obj());
        assert!(!v.is_str());
    }

    #[test]
    fn test_value_is_float() {
        let v = Value::Float(1.0);
        assert!(v.is_float());
        assert!(!v.is_i32());
    }

    #[test]
    fn test_value_is_u64() {
        let v = Value::U64(100);
        assert!(v.is_u64());
        assert!(!v.is_i32());
    }

    #[test]
    fn test_value_is_pointer() {
        let v = Value::Pointer(0x12345678);
        assert!(v.is_pointer());
        assert!(!v.is_i32());
    }

    #[test]
    fn test_value_is_color() {
        let v = Value::Color([255, 0, 0, 255]);
        assert!(v.is_color());
        assert!(!v.is_i32());
    }

    #[test]
    fn test_value_as_methods() {
        let v = Value::I32(42);
        assert_eq!(v.as_i32(), Some(42));
        assert_eq!(v.as_str(), None);
        assert_eq!(v.as_obj(), None);
    }

    #[test]
    fn test_value_as_str() {
        let v = Value::Str(Cow::Borrowed("test"));
        assert_eq!(v.as_str(), Some(&Cow::Borrowed("test")));
    }

    #[test]
    fn test_value_as_obj() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let v = Value::Obj(obj);
        assert!(v.as_obj().is_some());
    }

    #[test]
    fn test_value_as_float() {
        let v = Value::Float(1.5);
        assert_eq!(v.as_float(), Some(1.5));
    }

    #[test]
    fn test_value_as_u64() {
        let v = Value::U64(123456789);
        assert_eq!(v.as_u64(), Some(123456789));
    }

    #[test]
    fn test_value_as_pointer() {
        let v = Value::Pointer(0xABCDEF01);
        assert_eq!(v.as_pointer(), Some(0xABCDEF01));
    }

    #[test]
    fn test_value_as_color() {
        let v = Value::Color([255, 128, 64, 32]);
        assert_eq!(v.as_color(), Some([255, 128, 64, 32]));
    }

    #[test]
    fn test_value_display_i32() {
        assert_eq!(format!("{}", Value::I32(42)), "42");
        assert_eq!(format!("{}", Value::I32(-42)), "-42");
    }

    #[test]
    fn test_value_display_u64() {
        assert_eq!(format!("{}", Value::U64(100)), "100");
    }

    #[test]
    fn test_value_display_str() {
        assert_eq!(format!("{}", Value::Str(Cow::Borrowed("test"))), "test");
    }

    #[test]
    fn test_value_display_obj() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let v = Value::Obj(obj);
        assert!(format!("{}", v).contains("key"));
        assert!(format!("{}", v).contains("42"));
    }

    #[test]
    fn test_value_display_float() {
        let v = Value::Float(1.5);
        assert_eq!(format!("{}", v), "1.5");
    }

    #[test]
    fn test_value_display_pointer() {
        assert_eq!(format!("{}", Value::Pointer(0x12345678)), "0x12345678");
    }

    #[test]
    fn test_value_display_color() {
        assert_eq!(format!("{}", Value::Color([255, 0, 0, 255])), "25500255");
    }

    #[test]
    fn test_obj_new_is_empty() {
        let obj = Obj::new();
        assert!(obj.is_empty());
        assert_eq!(obj.len(), 0);
    }

    #[test]
    fn test_obj_get() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        assert_eq!(obj.get("key").and_then(|v| v.as_i32()), Some(42));
        assert_eq!(obj.get("missing"), None);
    }

    #[test]
    fn test_obj_len() {
        let mut obj = Obj::new();
        assert_eq!(obj.len(), 0);
        obj.insert(Cow::Borrowed("key1"), Value::I32(1));
        assert_eq!(obj.len(), 1);
        obj.insert(Cow::Borrowed("key2"), Value::I32(2));
        assert_eq!(obj.len(), 2);
    }

    #[test]
    fn test_obj_iter() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key1"), Value::I32(1));
        obj.insert(Cow::Borrowed("key2"), Value::I32(2));
        let mut iter = obj.iter();
        assert!(iter.next().is_some());
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_obj_default() {
        let obj = Obj::default();
        assert!(obj.is_empty());
    }

    #[test]
    fn test_vdf_new() {
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(Obj::new()));
        assert_eq!(vdf.key, "root");
        assert!(vdf.is_obj());
    }

    #[test]
    fn test_vdf_is_obj() {
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(Obj::new()));
        assert!(vdf.is_obj());
        let vdf2 = Vdf::new(Cow::Borrowed("root"), Value::I32(42));
        assert!(!vdf2.is_obj());
    }

    #[test]
    fn test_vdf_as_obj() {
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(Obj::new()));
        assert!(vdf.as_obj().is_some());
        let vdf2 = Vdf::new(Cow::Borrowed("root"), Value::I32(42));
        assert!(vdf2.as_obj().is_none());
    }

    #[test]
    fn test_vdf_display() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));
        let s = format!("{}", vdf);
        assert!(s.contains("root"));
    }

    #[test]
    fn test_into_owned_value_str() {
        let value = Value::Str(Cow::Borrowed("test"));
        let owned = value.into_owned();
        assert_eq!(owned, Value::Str(Cow::Owned("test".to_string())));
    }

    #[test]
    fn test_into_owned_value_str_already_owned() {
        let value = Value::Str(Cow::Owned("test".to_string()));
        let owned = value.into_owned();
        assert_eq!(owned, Value::Str(Cow::Owned("test".to_string())));
    }

    #[test]
    fn test_into_owned_value_obj() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let value = Value::Obj(obj);
        let owned = value.into_owned();
        assert!(owned.is_obj());
    }

    #[test]
    fn test_into_owned_value_numeric() {
        assert_eq!(Value::I32(42).into_owned(), Value::I32(42));
        assert_eq!(Value::U64(100).into_owned(), Value::U64(100));
        assert_eq!(Value::Float(1.5).into_owned(), Value::Float(1.5));
        assert_eq!(Value::Pointer(123).into_owned(), Value::Pointer(123));
        assert_eq!(
            Value::Color([1, 2, 3, 4]).into_owned(),
            Value::Color([1, 2, 3, 4])
        );
    }

    #[test]
    fn test_into_owned_obj() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let owned = obj.into_owned();
        assert_eq!(owned.len(), 1);
        assert_eq!(owned.get("key").and_then(|v| v.as_i32()), Some(42));
    }

    #[test]
    fn test_into_owned_obj_nested() {
        let mut inner = Obj::new();
        inner.insert(
            Cow::Borrowed("inner_key"),
            Value::Str(Cow::Borrowed("value")),
        );
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("outer_key"), Value::Obj(inner));
        let owned = outer.into_owned();
        let inner_obj = owned.get("outer_key").and_then(|v| v.as_obj()).unwrap();
        assert_eq!(
            inner_obj.get("inner_key").and_then(|v| v.as_str()),
            Some(&Cow::Owned("value".to_string()))
        );
    }

    #[test]
    fn test_into_owned_vdf() {
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::I32(42));
        let owned = vdf.into_owned();
        assert_eq!(owned.key, Cow::Owned::<str>("root".to_string()));
        assert_eq!(owned.value, Value::I32(42));
    }

    // Tests for Value::get and get_path methods

    #[test]
    fn test_value_get_on_obj() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let value = Value::Obj(obj);
        assert_eq!(value.get("key").and_then(|v| v.as_i32()), Some(42));
        assert_eq!(value.get("missing"), None);
    }

    #[test]
    fn test_value_get_on_non_obj() {
        let value = Value::I32(42);
        assert_eq!(value.get("key"), None);
    }

    #[test]
    fn test_value_get_path_single_key() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let value = Value::Obj(obj);
        assert_eq!(value.get_path(&["key"]).and_then(|v| v.as_i32()), Some(42));
    }

    #[test]
    fn test_value_get_path_empty() {
        let value = Value::I32(42);
        assert_eq!(value.get_path(&[]).and_then(|v| v.as_i32()), Some(42));
    }

    #[test]
    fn test_value_get_path_nested() {
        let mut inner = Obj::new();
        inner.insert(Cow::Borrowed("c"), Value::Str(Cow::Borrowed("found")));
        let mut middle = Obj::new();
        middle.insert(Cow::Borrowed("b"), Value::Obj(inner));
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("a"), Value::Obj(middle));
        let value = Value::Obj(outer);

        assert_eq!(
            value.get_path(&["a", "b", "c"]).and_then(|v| v.as_str()),
            Some(&Cow::Borrowed("found"))
        );
    }

    #[test]
    fn test_value_get_path_missing_intermediate() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("a"), Value::I32(42));
        let value = Value::Obj(obj);
        assert_eq!(value.get_path(&["a", "b"]), None);
    }

    #[test]
    fn test_value_get_path_non_obj_intermediate() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("a"), Value::I32(42));
        let value = Value::Obj(obj);
        assert_eq!(value.get_path(&["a", "b"]), None);
    }

    #[test]
    fn test_value_get_str() {
        let mut inner = Obj::new();
        inner.insert(Cow::Borrowed("name"), Value::Str(Cow::Borrowed("test")));
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("data"), Value::Obj(inner));
        let value = Value::Obj(outer);

        assert_eq!(
            value.get_str(&["data", "name"]),
            Some(&Cow::Borrowed("test"))
        );
        assert_eq!(value.get_str(&["data", "missing"]), None);
    }

    #[test]
    fn test_value_get_obj() {
        let mut inner = Obj::new();
        inner.insert(Cow::Borrowed("key"), Value::I32(1));
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("nested"), Value::Obj(inner));
        let value = Value::Obj(outer);

        let obj = value.get_obj(&["nested"]).unwrap();
        assert_eq!(obj.len(), 1);
    }

    #[test]
    fn test_value_get_i32() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("num"), Value::I32(123));
        let value = Value::Obj(obj);

        assert_eq!(value.get_i32(&["num"]), Some(123));
        assert_eq!(value.get_i32(&["missing"]), None);
    }

    #[test]
    fn test_value_get_u64() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("big"), Value::U64(9999999999));
        let value = Value::Obj(obj);

        assert_eq!(value.get_u64(&["big"]), Some(9999999999));
    }

    #[test]
    fn test_value_get_float() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("pi"), Value::Float(3.14));
        let value = Value::Obj(obj);

        assert_eq!(value.get_float(&["pi"]), Some(3.14));
    }

    // Tests for Vdf delegation methods

    #[test]
    fn test_vdf_get() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("key"), Value::I32(42));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));

        assert_eq!(vdf.get("key").and_then(|v| v.as_i32()), Some(42));
        assert_eq!(vdf.get("missing"), None);
    }

    #[test]
    fn test_vdf_get_path() {
        let mut inner = Obj::new();
        inner.insert(Cow::Borrowed("value"), Value::Str(Cow::Borrowed("found")));
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("nested"), Value::Obj(inner));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(outer));

        assert_eq!(
            vdf.get_path(&["nested", "value"]).and_then(|v| v.as_str()),
            Some(&Cow::Borrowed("found"))
        );
    }

    #[test]
    fn test_vdf_get_str() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("name"), Value::Str(Cow::Borrowed("test")));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));

        assert_eq!(vdf.get_str(&["name"]), Some(&Cow::Borrowed("test")));
    }

    #[test]
    fn test_vdf_get_obj() {
        let mut inner = Obj::new();
        inner.insert(Cow::Borrowed("k"), Value::I32(1));
        let mut outer = Obj::new();
        outer.insert(Cow::Borrowed("inner"), Value::Obj(inner));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(outer));

        assert!(vdf.get_obj(&["inner"]).is_some());
    }

    #[test]
    fn test_vdf_get_i32() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("num"), Value::I32(42));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));

        assert_eq!(vdf.get_i32(&["num"]), Some(42));
    }

    #[test]
    fn test_vdf_get_u64() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("big"), Value::U64(12345678901234));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));

        assert_eq!(vdf.get_u64(&["big"]), Some(12345678901234));
    }

    #[test]
    fn test_vdf_get_float() {
        let mut obj = Obj::new();
        obj.insert(Cow::Borrowed("f"), Value::Float(2.5));
        let vdf = Vdf::new(Cow::Borrowed("root"), Value::Obj(obj));

        assert_eq!(vdf.get_float(&["f"]), Some(2.5));
    }
}
