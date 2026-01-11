//! Blazing fast VDF (Valve Data Format) parser.
//!
//! This library provides parsers for both text and binary VDF formats used by Steam and
//! other Valve Software products.
//!
//! # Features
//!
//! - **Zero-copy parsing** for text format when possible (no escape sequences)
//! - **Binary format support** for Steam's appinfo.vdf and shortcuts.vdf
//! - **Winnow-powered** text parser for maximum performance
//!
//! # Example
//!
//! ```
//! use steam_vdf_parser::parse_text;
//!
//! let input = r#""root"
//! {
//!     "key" "value"
//!     "nested"
//!     {
//!         "subkey" "subvalue"
//!     }
//! }"#;
//!
//! let vdf = parse_text(input).unwrap();
//! ```

pub mod binary;
pub mod error;
pub mod text;
pub mod value;

pub use error::{Error, Result};
pub use value::{Obj, Value, Vdf};

// Re-export commonly used functions
pub use text::parse_text;

/// Parse VDF from binary format (autodetects shortcuts or appinfo format).
///
/// This function returns zero-copy data where possible - strings are borrowed
/// from the input buffer. Use `.into_owned()` to convert to an owned `Vdf<'static>`.
///
/// # Example
///
/// ```no_check
/// use steam_vdf_parser::parse_binary;
///
/// let data = std::fs::read("shortcuts.vdf")?;
/// let vdf = parse_binary(&data)?;
/// // For data that needs to outlive the input:
/// let owned = vdf.into_owned();
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn parse_binary(input: &[u8]) -> Result<Vdf<'_>> {
    binary::parse(input)
}

/// Parse a shortcuts.vdf format binary file.
///
/// This function returns zero-copy data where possible - strings are borrowed
/// from the input buffer. Use `.into_owned()` to convert to an owned `Vdf<'static>`.
pub fn parse_shortcuts(input: &[u8]) -> Result<Vdf<'_>> {
    binary::parse_shortcuts(input)
}

/// Parse an appinfo.vdf format binary file.
///
/// This function returns zero-copy data where possible - strings are borrowed
/// from the input buffer. Use `.into_owned()` to convert to an owned `Vdf<'static>`.
pub fn parse_appinfo(input: &[u8]) -> Result<Vdf<'_>> {
    binary::parse_appinfo(input)
}

/// Parse VDF from a text file.
///
/// This is a convenience function that reads a file and parses it.
/// Returns an owned `Vdf<'static>` since the file content is owned.
pub fn parse_text_file(path: impl AsRef<std::path::Path>) -> Result<Vdf<'static>> {
    let content = std::fs::read_to_string(path).map_err(Error::IoError)?;
    Ok(parse_text(&content)?.into_owned())
}

/// Parse VDF from a binary file.
///
/// This is a convenience function that reads a file and parses it.
/// Returns an owned `Vdf<'static>` since the file content is owned.
pub fn parse_binary_file(path: impl AsRef<std::path::Path>) -> Result<Vdf<'static>> {
    let content = std::fs::read(path).map_err(Error::IoError)?;
    Ok(parse_binary(&content)?.into_owned())
}

// Convert from borrowed to owned
impl Vdf<'_> {
    /// Convert to an owned version (with 'static lifetime).
    ///
    /// This creates a new `Vdf<'static>` with all strings owned, allowing the
    /// data to outlive the original input.
    pub fn into_owned(self) -> Vdf<'static> {
        Vdf {
            key: match self.key {
                std::borrow::Cow::Borrowed(s) => s.to_string().into(),
                std::borrow::Cow::Owned(s) => s.into(),
            },
            value: self.value.into_owned(),
        }
    }
}

impl Value<'_> {
    /// Convert to an owned version (with 'static lifetime).
    pub fn into_owned(self) -> Value<'static> {
        match self {
            Value::Str(s) => Value::Str(match s {
                std::borrow::Cow::Borrowed(b) => b.to_string().into(),
                std::borrow::Cow::Owned(o) => o.into(),
            }),
            Value::Obj(obj) => Value::Obj(obj.into_owned()),
            Value::I32(n) => Value::I32(n),
            Value::U64(n) => Value::U64(n),
            Value::Float(n) => Value::Float(n),
            Value::Pointer(n) => Value::Pointer(n),
            Value::Color(c) => Value::Color(c),
        }
    }
}

impl Obj<'_> {
    /// Convert to an owned version (with 'static lifetime).
    pub fn into_owned(self) -> Obj<'static> {
        let mut new = Obj::new();
        for (k, v) in self.iter() {
            let owned_key = match k {
                std::borrow::Cow::Borrowed(b) => b.to_string().into(),
                std::borrow::Cow::Owned(o) => o.clone().into(),
            };
            // Clone the value since we're iterating
            new.insert(owned_key, v.clone().into_owned());
        }
        new
    }
}
