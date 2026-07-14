//! Options controlling binary VDF parsing.

/// Strategy for handling byte sequences that are not valid UTF-8 (or UTF-16).
///
/// Steam stores string values in binary VDF files as raw byte strings and does
/// **not** guarantee they are valid UTF-8. Localized fields in particular often
/// carry legacy code-page bytes (e.g. a Czech app name `Moje Spore v\u{fffd}tvory`
/// where `0xFD` is Windows-1250 `ý`), which are not valid UTF-8 on their own.
///
/// This enum selects what the parser does when it encounters such bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum InvalidUtf8 {
    /// Replace invalid byte sequences with the U+FFFD REPLACEMENT CHARACTER.
    ///
    /// Parsing always succeeds. Valid strings are still borrowed zero-copy from
    /// the input; only strings that actually contain invalid bytes are
    /// allocated (to hold the replacement characters). This is the default.
    #[default]
    Lossy,
    /// Return an [`Error::InvalidUtf8`](crate::Error::InvalidUtf8) (or
    /// [`Error::InvalidUtf16`](crate::Error::InvalidUtf16)) error.
    ///
    /// Use this when you need to detect corruption rather than silently
    /// substituting replacement characters.
    Strict,
}

/// Options controlling how binary VDF data is parsed.
///
/// Construct with [`ParseOptions::new`] (or [`Default`]) and configure with the
/// builder-style methods:
///
/// ```
/// use steam_vdf_parser::{InvalidUtf8, ParseOptions};
///
/// // Default: lossy handling of invalid UTF-8.
/// let opts = ParseOptions::new();
/// assert_eq!(opts.invalid_utf8, InvalidUtf8::Lossy);
///
/// // Opt into strict error-on-invalid behavior.
/// let strict = ParseOptions::new().invalid_utf8(InvalidUtf8::Strict);
/// assert_eq!(strict.invalid_utf8, InvalidUtf8::Strict);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub struct ParseOptions {
    /// How to handle strings that are not valid UTF-8. Defaults to
    /// [`InvalidUtf8::Lossy`].
    pub invalid_utf8: InvalidUtf8,
}

impl ParseOptions {
    /// Create a new set of options with default values (lossy UTF-8 handling).
    pub fn new() -> Self {
        Self::default()
    }

    /// Set how invalid UTF-8 byte sequences are handled.
    pub fn invalid_utf8(mut self, mode: InvalidUtf8) -> Self {
        self.invalid_utf8 = mode;
        self
    }
}
