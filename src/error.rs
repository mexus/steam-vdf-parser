//! Error types for VDF parsing.

use std::fmt;

/// Result type for VDF operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Create a parse error with truncated input snippet (max 50 chars).
pub fn parse_error(input: &str, offset: usize, context: impl Into<String>) -> Error {
    let snippet = input.chars().take(50).collect::<String>();
    Error::ParseError {
        input: snippet,
        offset,
        context: context.into(),
    }
}

/// Errors that can occur during VDF parsing.
#[derive(Debug)]
pub enum Error {
    /// Binary format errors
    /// ---------------------

    /// Invalid magic number in binary VDF header.
    InvalidMagic { found: u32 },

    /// Unknown type byte encountered.
    UnknownType {
        /// The type byte that was found.
        type_byte: u8,
        /// Offset in the input where this occurred.
        offset: usize,
    },

    /// Invalid string index into the string table.
    InvalidStringIndex {
        /// The index that was requested.
        index: usize,
        /// The maximum valid index.
        max: usize,
    },

    /// Unexpected end of input while parsing.
    UnexpectedEndOfInput,

    /// Invalid UTF-8 sequence in binary data.
    InvalidUtf8 {
        /// Offset where the error occurred.
        offset: usize,
    },

    /// Text format errors
    /// ------------------

    /// Parse error with context.
    ParseError {
        /// A snippet of the input near the error.
        input: String,
        /// Offset in the input where this occurred.
        offset: usize,
        /// Context describing what was expected.
        context: String,
    },

    /// IO errors
    /// ---------

    /// An error from the underlying IO operation.
    IoError(std::io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidMagic { found } => {
                write!(f, "Invalid magic number: 0x{:08x}", found)
            }
            Error::UnknownType { type_byte, offset } => {
                write!(
                    f,
                    "Unknown type byte 0x{:02x} at offset {}",
                    type_byte, offset
                )
            }
            Error::InvalidStringIndex { index, max } => {
                write!(
                    f,
                    "Invalid string index {} (maximum valid index: {})",
                    index,
                    max.saturating_sub(1)
                )
            }
            Error::UnexpectedEndOfInput => {
                write!(f, "Unexpected end of input")
            }
            Error::InvalidUtf8 { offset } => {
                write!(f, "Invalid UTF-8 sequence at offset {}", offset)
            }
            Error::ParseError {
                input,
                offset,
                context,
            } => {
                let snippet = if input.len() > 50 {
                    format!("{}...", &input[..50])
                } else {
                    input.clone()
                };
                write!(
                    f,
                    "Parse error at offset {}: {} (near: \"{}\")",
                    offset, context, snippet
                )
            }
            Error::IoError(err) => {
                write!(f, "IO error: {}", err)
            }
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::IoError(err) => Some(err),
            _ => None,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::IoError(err)
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(_err: std::str::Utf8Error) -> Self {
        Error::InvalidUtf8 { offset: 0 }
    }
}
