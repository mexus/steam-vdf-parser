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
/// # Example
///
/// ```no_check
/// use steam_vdf_parser::parse_binary;
///
/// let data = std::fs::read("shortcuts.vdf")?;
/// let vdf = parse_binary(&data)?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn parse_binary(input: &[u8]) -> Result<Vdf<'static>> {
    binary::parse(input)
}

/// Parse a shortcuts.vdf format binary file.
pub fn parse_shortcuts(input: &[u8]) -> Result<Vdf<'static>> {
    binary::parse_shortcuts(input)
}

/// Parse an appinfo.vdf format binary file.
pub fn parse_appinfo(input: &[u8]) -> Result<Vdf<'static>> {
    binary::parse_appinfo(input)
}

/// Parse VDF from a text file.
pub fn parse_text_file(path: impl AsRef<std::path::Path>) -> Result<Vdf<'static>> {
    let content = std::fs::read_to_string(path)?;
    Ok(parse_text(&content)?.to_owned())
}

/// Parse VDF from a binary file.
pub fn parse_binary_file(path: impl AsRef<std::path::Path>) -> Result<Vdf<'static>> {
    let content = std::fs::read(path)?;
    parse_binary(&content)
}

// Add conversion from borrowed to owned
impl Vdf<'_> {
    /// Convert to an owned version (with 'static lifetime).
    pub fn to_owned(&self) -> Vdf<'static> {
        Vdf {
            key: self.key.to_string().into(),
            value: self.value.to_owned(),
        }
    }
}

impl Value<'_> {
    /// Convert to an owned version (with 'static lifetime).
    pub fn to_owned(&self) -> Value<'static> {
        match self {
            Value::Str(s) => Value::Str(s.to_string().into()),
            Value::Obj(obj) => Value::Obj(obj.to_owned()),
        }
    }
}

impl Obj<'_> {
    /// Convert to an owned version (with 'static lifetime).
    pub fn to_owned(&self) -> Obj<'static> {
        let mut new = Obj::new();
        for (k, v) in self.iter() {
            new.insert(k.to_string().into(), v.to_owned());
        }
        new
    }
}
