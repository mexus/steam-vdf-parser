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
    InvalidMagic {
        /// The magic number that was found.
        found: u32,
        /// Expected magic numbers for this format.
        expected: &'static [u32],
    },

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
    UnexpectedEndOfInput {
        /// Description of what was being read.
        context: &'static str,
        /// Offset in the input where this occurred.
        offset: usize,
        /// Expected minimum number of bytes.
        expected: usize,
        /// Actual number of bytes available.
        actual: usize,
    },

    /// Invalid UTF-8 sequence in binary data.
    InvalidUtf8 {
        /// Offset where the error occurred.
        offset: usize,
    },

    /// Invalid UTF-16 sequence in binary data.
    InvalidUtf16 {
        /// Offset where the error occurred.
        offset: usize,
        /// Position of the unpaired surrogate.
        position: usize,
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
            Error::InvalidMagic { found, expected } => {
                let expected_str: String = expected
                    .iter()
                    .map(|v| format!("0x{:08x}", v))
                    .collect::<Vec<_>>()
                    .join(" or ");
                write!(
                    f,
                    "Invalid magic number: expected {}, found 0x{:08x}",
                    expected_str, found
                )
            }
            Error::UnknownType { type_byte, offset } => {
                write!(
                    f,
                    "Unknown type byte 0x{:02x} at offset {}",
                    type_byte, offset
                )
            }
            Error::InvalidStringIndex { index, max } => {
                if *max == 0 {
                    write!(f, "Invalid string index {}: string table is empty", index)
                } else {
                    write!(
                        f,
                        "Invalid string index {}: string table has {} entries (valid range: 0..{})",
                        index, max, max
                    )
                }
            }
            Error::UnexpectedEndOfInput {
                context,
                offset,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "Unexpected end of input at offset {} while {}: expected {} bytes, found {}",
                    offset, context, expected, actual
                )
            }
            Error::InvalidUtf8 { offset } => {
                write!(f, "Invalid UTF-8 sequence at offset {}", offset)
            }
            Error::InvalidUtf16 { offset, position } => {
                write!(
                    f,
                    "Invalid UTF-16 sequence at offset {} (surrogate position {})",
                    offset, position
                )
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

impl Error {
    /// Adjusts the offset in error variants that contain position information.
    ///
    /// This is used to add a base offset when parsing from a sub-slice,
    /// converting relative offsets to absolute offsets in the original input.
    pub fn with_offset(mut self, base: usize) -> Self {
        match &mut self {
            Error::UnexpectedEndOfInput { offset, .. } => *offset += base,
            Error::InvalidUtf8 { offset } => *offset += base,
            Error::InvalidUtf16 { offset, .. } => *offset += base,
            Error::UnknownType { offset, .. } => *offset += base,
            Error::ParseError { offset, .. } => *offset += base,
            // Other variants don't have offsets to adjust
            Error::InvalidMagic { .. } | Error::InvalidStringIndex { .. } | Error::IoError(_) => {}
        }
        self
    }
}

/// Returns a closure that adds an offset to an error.
///
/// This is used with `.map_err()` to adjust error offsets when parsing from sub-slices.
///
/// # Example
/// ```ignore
/// let result = parse_value(data).map_err(with_offset(base_offset))?;
/// ```
pub fn with_offset(base: usize) -> impl Fn(Error) -> Error {
    move |err| err.with_offset(base)
}
