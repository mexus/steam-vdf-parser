//! Text VDF parser.

use std::borrow::Cow;

use crate::error::Error;
use crate::error::Result;
use crate::value::{Obj, Value, Vdf};

/// Parse a VDF document from text format.
///
/// # Example
///
/// ```
/// use steam_vdf_parser::parse_text;
///
/// let input = r#""root"
/// {
///     "key" "value"
/// }"#;
/// let vdf = parse_text(input).unwrap();
/// assert_eq!(vdf.key, "root");
/// ```
pub fn parse(input: &str) -> Result<Vdf<'_>> {
    let input = input.trim_start();

    // Parse the root key followed by an object
    let (input, key) = token(input).map_err(|e| Error::ParseError {
        input: input.to_string(),
        offset: 0,
        context: format!("Failed to parse key: {:?}", e),
    })?;

    let (input, _) = ws(input).map_err(|e| Error::ParseError {
        input: input.to_string(),
        offset: 0,
        context: format!("Failed to parse whitespace: {:?}", e),
    })?;

    // The value should be an object
    let (input, obj) = object(input).map_err(|e| Error::ParseError {
        input: input.to_string(),
        offset: 0,
        context: format!("Failed to parse object: {:?}", e),
    })?;

    // Allow trailing content
    let _ = input;

    Ok(Vdf {
        key: Cow::Borrowed(key),
        value: Value::Obj(obj),
    })
}

/// Parse a key-value pair from text input.
///
/// Returns (remaining input, (key, value)).
fn kv_pair(input: &str) -> core::result::Result<(&str, (&str, Value<'_>)), ParseError> {
    let (input, _) = ws(input)?;
    let (input, key) = token(input)?;
    let (input, _) = ws(input)?;

    // Look ahead to see if value is object or string
    let (input, value) = if input.starts_with('{') {
        let (input, obj) = object(input)?;
        (input, Value::Obj(obj))
    } else {
        let (input, s) = token(input)?;
        (input, Value::Str(Cow::Borrowed(s)))
    };

    let (input, _) = ws(input)?;

    Ok((input, (key, value)))
}

/// Parse an object (recursive block of key-value pairs).
///
/// Returns (remaining input, object).
fn object(input: &str) -> core::result::Result<(&str, Obj<'_>), ParseError> {
    if !input.starts_with('{') {
        return Err(ParseError::Expected("{"));
    }
    let mut input = &input[1..];

    let mut obj = Obj::new();

    // Parse key-value pairs until we hit '}'
    loop {
        let (rest, _) = ws(input)?;
        input = rest;

        // Check for end of object
        if input.starts_with('}') {
            input = &input[1..];
            break;
        }

        let (rest, (key, value)) = kv_pair(input)?;
        obj.insert(Cow::Borrowed(key), value);
        input = rest;
    }

    Ok((input, obj))
}

/// Parse a token (either quoted or unquoted).
///
/// Returns (remaining input, token).
fn token(input: &str) -> core::result::Result<(&str, &str), ParseError> {
    // Try quoted string first
    if input.starts_with('"') {
        return quoted_string(input);
    }

    // Otherwise, parse unquoted token
    unquoted_string(input)
}

/// Parse a quoted string.
///
/// Returns (remaining input, string content).
fn quoted_string(input: &str) -> core::result::Result<(&str, &str), ParseError> {
    if !input.starts_with('"') {
        return Err(ParseError::Expected("\""));
    }
    let input = &input[1..];

    // Parse until closing quote, handling escapes
    let mut escaped = false;
    let mut end = 0;

    for (idx, ch) in input.char_indices() {
        if escaped {
            escaped = false;
            end = idx + ch.len_utf8();
            continue;
        }
        if ch == '\\' {
            escaped = true;
            end = idx + ch.len_utf8();
            continue;
        }
        if ch == '"' {
            // Found the end - return the string content
            let result = &input[..end];
            let rest = &input[idx + 1..];
            return Ok((rest, result));
        }
        end = idx + ch.len_utf8();
    }

    // Unclosed string - return error
    Err(ParseError::UnclosedString)
}

/// Parse an unquoted string.
///
/// Unquoted strings end at whitespace, `{`, `}`, or `"`.
///
/// Returns (remaining input, token).
fn unquoted_string(input: &str) -> core::result::Result<(&str, &str), ParseError> {
    let mut end = 0;

    for (idx, ch) in input.char_indices() {
        if ch.is_whitespace() || ch == '{' || ch == '}' || ch == '"' {
            break;
        }
        end = idx + ch.len_utf8();
    }

    if end == 0 {
        return Err(ParseError::Expected("token"));
    }

    Ok((&input[end..], &input[..end]))
}

/// Skip zero or more whitespace characters or line comments.
///
/// Returns (remaining input, ()).
fn ws(input: &str) -> core::result::Result<(&str, ()), ParseError> {
    let mut rest = input;

    while !rest.is_empty() {
        let first = rest.chars().next().unwrap();

        // Whitespace
        if first.is_whitespace() {
            rest = &rest[first.len_utf8()..];
            continue;
        }

        // Line comment
        if rest.starts_with("//") {
            // Skip until newline or end
            let newline_pos = rest.find('\n').unwrap_or(rest.len());
            rest = &rest[newline_pos..];
            continue;
        }

        // Not whitespace or comment, stop
        break;
    }

    Ok((rest, ()))
}

/// Parse error type for internal parsing.
#[derive(Debug)]
enum ParseError {
    Expected(&'static str),
    UnclosedString,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Expected(s) => write!(f, "expected {}", s),
            ParseError::UnclosedString => write!(f, "unclosed string"),
        }
    }
}

impl std::error::Error for ParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_kv() {
        let input = r#""root"
        {
            "key" "value"
        }"#;
        let vdf = parse(input).unwrap();
        assert_eq!(vdf.key, "root");

        // vdf.value is the object containing the key-value pairs
        let obj = vdf.as_obj().unwrap();
        let value = obj.get("key").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Borrowed("value")));
    }

    #[test]
    fn test_parse_nested_objects() {
        let input = r#""outer"
        {
            "inner"
            {
                "key" "value"
            }
        }"#;
        let vdf = parse(input).unwrap();
        assert_eq!(vdf.key, "outer");

        let obj = vdf.as_obj().unwrap();
        let inner = obj.get("inner").and_then(|v| v.as_obj()).unwrap();
        let value = inner.get("key").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Borrowed("value")));
    }

    #[test]
    fn test_parse_unquoted_tokens() {
        let input = r#"root
        {
            key value
        }"#;
        let vdf = parse(input).unwrap();
        assert_eq!(vdf.key, "root");

        let obj = vdf.as_obj().unwrap();
        let value = obj.get("key").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Borrowed("value")));
    }

    #[test]
    fn test_parse_with_comments() {
        let input = r#""root"
        {
            // This is a comment
            "key" "value"
            // Another comment
        }"#;
        let vdf = parse(input).unwrap();

        let obj = vdf.as_obj().unwrap();
        let value = obj.get("key").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Borrowed("value")));
    }

    #[test]
    fn test_parse_multiple_keys() {
        let input = r#""settings"
        {
            "name" "test"
            "count" "42"
        }"#;
        let vdf = parse(input).unwrap();

        let obj = vdf.as_obj().unwrap();
        assert_eq!(obj.get("name").and_then(|v| v.as_str()), Some(&Cow::Borrowed("test")));
        assert_eq!(obj.get("count").and_then(|v| v.as_str()), Some(&Cow::Borrowed("42")));
    }
}
