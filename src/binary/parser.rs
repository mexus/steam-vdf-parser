//! Binary VDF parser implementation.
//!
//! Supports Steam's binary VDF formats:
//! - shortcuts.vdf (simple binary format)
//! - appinfo.vdf (with optional string table)

use std::borrow::Cow;

use crate::binary::types::{APPINFO_MAGIC_28, APPINFO_MAGIC_29, BinaryType};
use crate::error::{Error, Result};
use crate::value::{Obj, Value, Vdf};

/// Parse configuration for binary VDF formats.
///
/// Encapsulates the differences between shortcuts.vdf and appinfo.vdf formats.
struct ParseConfig<'a> {
    /// String table for v29 format (cloned for each parse context)
    string_table: Option<StringTable<'a>>,
    /// Strategy for parsing keys
    key_mode: KeyMode,
}

/// Key parsing strategy for binary VDF formats.
enum KeyMode {
    /// Parse keys as null-terminated UTF-8 strings (v28, shortcuts)
    NullTerminated,
    /// Parse keys as u32 indices into string table (v29)
    StringTableIndex,
}

/// String table for v29 appinfo format.
///
/// Encapsulates pre-extracted strings from the string table section,
/// enabling O(1) lookups by index.
#[derive(Clone)]
struct StringTable<'a> {
    strings: Vec<&'a str>,
}

impl<'a> StringTable<'a> {
    /// Get a string by index.
    fn get(&self, index: usize) -> Result<&'a str> {
        self.strings
            .get(index)
            .copied()
            .ok_or(Error::InvalidStringIndex {
                index,
                max: self.strings.len(),
            })
    }
}

impl KeyMode {
    /// Parse a key from input according to this mode.
    fn parse_key<'a>(
        &self,
        input: &'a [u8],
        config: &ParseConfig<'a>,
    ) -> Result<(&'a [u8], Cow<'a, str>)> {
        match self {
            KeyMode::NullTerminated => {
                let (rest, s) = parse_null_terminated_string_borrowed(input)?;
                Ok((rest, Cow::Borrowed(s)))
            }
            KeyMode::StringTableIndex => {
                if input.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let index = u32::from_le_bytes([input[0], input[1], input[2], input[3]]) as usize;
                let s = config.string_table.as_ref().unwrap().get(index)?;
                Ok((&input[4..], Cow::Borrowed(s)))
            }
        }
    }
}

/// Parse binary VDF data (autodetects format).
///
/// Attempts to parse as appinfo.vdf first, then falls back to shortcuts.vdf format.
/// For shortcuts format, returns zero-copy data borrowed from input.
/// For appinfo format, returns mixed data: root key and app ID keys are owned,
/// but actual parsed values (including string table entries) are borrowed.
pub fn parse(input: &[u8]) -> Result<Vdf<'_>> {
    // Check if this looks like appinfo format (starts with magic)
    if input.len() >= 4 {
        let magic = u32::from_le_bytes([input[0], input[1], input[2], input[3]]);
        if magic == APPINFO_MAGIC_28 || magic == APPINFO_MAGIC_29 {
            // parse_appinfo returns Vdf<'static>, which is compatible with Vdf<'_>
            return parse_appinfo(input);
        }
    }

    // Otherwise, parse as shortcuts format (zero-copy)
    parse_shortcuts(input)
}

/// Parse shortcuts.vdf format binary data.
///
/// This is the simpler binary format used by Steam for shortcuts and other data.
///
/// This function returns zero-copy data - strings are borrowed from the input buffer.
///
/// Format:
/// - Each entry starts with a type byte
/// - Type 0x00: Object start (key is the object name)
/// - Type 0x01: String value
/// - Type 0x02: Int32 value
/// - Type 0x08: Object end
///
/// All strings are null-terminated.
pub fn parse_shortcuts(input: &[u8]) -> Result<Vdf<'_>> {
    let config = ParseConfig {
        string_table: None,
        key_mode: KeyMode::NullTerminated,
    };
    let (_rest, obj) = parse_object(input, &config)?;

    Ok(Vdf {
        key: Cow::Borrowed("root"),
        value: Value::Obj(obj),
    })
}

/// Parse appinfo.vdf format binary data.
///
/// This function returns zero-copy data where possible - strings are borrowed from
/// the input buffer (including string table entries in v29 format).
///
/// Format:
/// - 4 bytes: Magic number (0x07564428 or 0x07564429)
/// - 4 bytes: Universe
/// - If magic == 0x07564429: 8 bytes: String table offset
/// - Apps continue until EOF (or string table for v29)
/// - For each app:
///   - 4 bytes: App ID
///   - 4 bytes: Size (remaining data size for this entry)
///   - 4 bytes: InfoState
///   - 4 bytes: LastUpdated (Unix timestamp)
///   - 8 bytes: AccessToken
///   - 20 bytes: SHA1 of text data
///   - 4 bytes: ChangeNumber
///   - 20 bytes: SHA1 of binary data
///   - Then the VDF data for the app (starts with 0x00)
/// - String table (if magic == 0x07564429, at string_table_offset)
///
/// App entry header is 68 bytes.
pub fn parse_appinfo(input: &[u8]) -> Result<Vdf<'_>> {
    if input.len() < 16 {
        return Err(Error::UnexpectedEndOfInput);
    }

    let magic = u32::from_le_bytes([input[0], input[1], input[2], input[3]]);
    let universe = u32::from_le_bytes([input[4], input[5], input[6], input[7]]);

    let (string_table_offset, mut rest) = match magic {
        APPINFO_MAGIC_28 => (None, &input[8..]),
        APPINFO_MAGIC_29 => {
            let offset = u64::from_le_bytes([
                input[8], input[9], input[10], input[11], input[12], input[13], input[14],
                input[15],
            ]);
            (Some(offset as usize), &input[16..])
        }
        _ => {
            return Err(Error::InvalidMagic { found: magic });
        }
    };

    // Parse the string table if present
    let string_table = if let Some(offset) = string_table_offset {
        let table_start = offset;
        if table_start >= input.len() {
            return Err(Error::UnexpectedEndOfInput);
        }
        Some(parse_string_table(&input[table_start..])?)
    } else {
        None
    };

    let mut obj = Obj::new();

    // Parse each app entry until we run out of data
    // App entry header: AppID(4) + Size(4) + InfoState(4) + LastUpdated(4) +
    //                  AccessToken(8) + SHA1(20) + ChangeNumber(4) + BinarySHA1(20) = 68 bytes
    // Calculate where apps end (at string table for v29, or EOF for v28)
    let apps_end_offset = string_table_offset.unwrap_or(input.len());

    loop {
        // Check if we've reached the end of apps section
        let current_offset = input.len() - rest.len();
        if current_offset >= apps_end_offset {
            break;
        }

        if rest.len() < 68 {
            break;
        }

        // App ID (offset 0)
        let app_id = u32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]);
        if app_id == 0 {
            break;
        }

        // Size (offset 4) - includes everything AFTER this field (60 bytes header + VDF data)
        let size = u32::from_le_bytes([rest[4], rest[5], rest[6], rest[7]]) as usize;

        // The 60 bytes after the size field:
        // info_state(4) + last_updated(4) + access_token(8) + sha1_text(20) + change_number(4) + sha1_binary(20)
        let header_after_size = 60;

        // VDF data starts after 68-byte header (app_id(4) + size(4) + header_after_size(60))
        let vdf_size = size - header_after_size;
        let vdf_start = 68;
        let vdf_end = vdf_start + vdf_size;

        if vdf_end > rest.len() {
            return Err(Error::UnexpectedEndOfInput);
        }

        let vdf_data = &rest[vdf_start..vdf_end];

        // Use v29 format (string table) if string_table_offset is Some
        let config = ParseConfig {
            string_table: string_table.clone(),
            key_mode: if string_table_offset.is_some() {
                KeyMode::StringTableIndex
            } else {
                KeyMode::NullTerminated
            },
        };
        let (_vdf_rest, app_obj) = parse_object(vdf_data, &config)?;

        // Insert with app ID as key
        obj.insert(Cow::Owned(app_id.to_string()), Value::Obj(app_obj));
        rest = &rest[vdf_end..];
    }

    Ok(Vdf {
        key: Cow::Owned(format!("appinfo_universe_{}", universe)),
        value: Value::Obj(obj),
    })
}

/// Parse an object from binary data.
///
/// Returns the remaining input and the parsed object.
///
/// # Parameters
/// - `input`: The binary data to parse
/// - `config`: Parse configuration including string table and key parsing strategy
fn parse_object<'a>(input: &'a [u8], config: &ParseConfig<'a>) -> Result<(&'a [u8], Obj<'a>)> {
    let mut obj = Obj::new();
    let mut rest = input;

    loop {
        match rest {
            [] => {
                // At root level, EOF is acceptable - file may end without trailing 0x08
                break Ok((rest, obj));
            }
            [type_byte, remainder @ ..] => {
                let type_byte = *type_byte;
                let typ = BinaryType::from_byte(type_byte);
                rest = remainder;

                match typ {
                    Some(BinaryType::ObjectEnd) => {
                        // Consume the end marker and return
                        return Ok((rest, obj));
                    }
                    Some(BinaryType::None) => {
                        // Map entry: 0x00 [key] { ... entries ... }
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, nested_obj) = parse_object(new_rest, config)?;
                        obj.insert(key, Value::Obj(nested_obj));
                        rest = new_rest;
                    }
                    Some(BinaryType::String) => {
                        // String entry: 0x01 [key] [value]
                        // VALUE is ALWAYS inline null-terminated string (never from string table!)
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_null_terminated_string_borrowed(new_rest)?;
                        obj.insert(key, Value::Str(Cow::Borrowed(value)));
                        rest = new_rest;
                    }
                    Some(BinaryType::Int32) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_int32(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::UInt64) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_uint64(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Float) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_float(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Ptr) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_ptr(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::WString) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_wstring(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Color) => {
                        let (new_rest, key) = config.key_mode.parse_key(rest, config)?;
                        let (new_rest, value) = parse_value_color(new_rest)?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    None => {
                        // Unknown type byte
                        return Err(Error::UnknownType {
                            type_byte,
                            offset: input.len() - rest.len(),
                        });
                    }
                }
            }
        }
    }
}

// ===== Value Parser Functions =====

/// Parse an Int32 value (4 bytes, little-endian).
fn parse_value_int32<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }
    let value = i32::from_le_bytes([input[0], input[1], input[2], input[3]]);
    Ok((&input[4..], Value::I32(value)))
}

/// Parse a UInt64 value (8 bytes, little-endian).
fn parse_value_uint64<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    if input.len() < 8 {
        return Err(Error::UnexpectedEndOfInput);
    }
    let value = u64::from_le_bytes([
        input[0], input[1], input[2], input[3], input[4], input[5], input[6], input[7],
    ]);
    Ok((&input[8..], Value::U64(value)))
}

/// Parse a Float value (4 bytes, little-endian).
fn parse_value_float<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }
    let value = f32::from_le_bytes([input[0], input[1], input[2], input[3]]);
    Ok((&input[4..], Value::Float(value)))
}

/// Parse a Pointer value (4 bytes, little-endian).
fn parse_value_ptr<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }
    let value = u32::from_le_bytes([input[0], input[1], input[2], input[3]]);
    Ok((&input[4..], Value::Pointer(value)))
}

/// Parse a WideString value (UTF-16LE, null-terminated).
fn parse_value_wstring<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let (rest, string) = parse_null_terminated_wstring(input)?;
    Ok((rest, Value::Str(Cow::Owned(string))))
}

/// Parse a Color value (4 bytes RGBA).
fn parse_value_color<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }
    let r = input[0];
    let g = input[1];
    let b = input[2];
    let a = input[3];
    Ok((&input[4..], Value::Color([r, g, b, a])))
}

// ===== String Parsing Functions =====

/// Parse a null-terminated string (UTF-8), returning a borrowed slice.
///
/// This is the zero-copy version that borrows from the input when possible.
fn parse_null_terminated_string_borrowed(input: &[u8]) -> Result<(&[u8], &str)> {
    let null_pos = input
        .iter()
        .position(|&b| b == 0)
        .ok_or(Error::UnexpectedEndOfInput)?;

    let bytes = &input[..null_pos];
    let string = std::str::from_utf8(bytes).map_err(|_| Error::InvalidUtf8 { offset: 0 })?;

    Ok((&input[null_pos + 1..], string))
}

/// Parse a null-terminated wide string (UTF-16LE).
///
/// WideString is terminated by two zero bytes (0x00 0x00).
/// Note: This allocates due to UTF-16 to UTF-8 conversion.
fn parse_null_terminated_wstring(input: &[u8]) -> Result<(&[u8], String)> {
    // Find the double-null terminator
    let mut i = 0;
    while i + 1 < input.len() {
        if input[i] == 0 && input[i + 1] == 0 {
            break;
        }
        i += 2;
    }

    if i + 1 >= input.len() {
        return Err(Error::UnexpectedEndOfInput);
    }

    // Convert UTF-16LE to String
    let utf16_data: Vec<u16> = (0..i)
        .step_by(2)
        .map(|j| u16::from_le_bytes([input[j], input[j + 1]]))
        .collect();

    let string = String::from_utf16(&utf16_data).map_err(|_| Error::InvalidUtf8 { offset: 0 })?;

    Ok((&input[i + 2..], string))
}

/// Parse the string table section (v29 format).
///
/// Returns a `StringTable` containing pre-extracted strings for O(1) lookups.
///
/// Format:
/// - 4 bytes: string_count (little-endian u32)
/// - Then string_count null-terminated UTF-8 strings
fn parse_string_table(input: &[u8]) -> Result<StringTable<'_>> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }

    // Read string_count (4 bytes, little-endian)
    let string_count = u32::from_le_bytes([input[0], input[1], input[2], input[3]]) as usize;

    let mut strings = Vec::with_capacity(string_count);
    let mut rest = &input[4..];

    // Extract each null-terminated string
    for _ in 0..string_count {
        if rest.is_empty() {
            return Err(Error::UnexpectedEndOfInput);
        }
        let null_pos = rest
            .iter()
            .position(|&b| b == 0)
            .ok_or(Error::UnexpectedEndOfInput)?;
        let string_bytes = &rest[..null_pos];
        let string =
            std::str::from_utf8(string_bytes).map_err(|_| Error::InvalidUtf8 { offset: 0 })?;
        strings.push(string);
        rest = &rest[null_pos + 1..];
    }

    Ok(StringTable { strings })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_object() {
        // Simple binary VDF: "test" { "key" "value" }
        let data: &[u8] = &[
            0x00, // Object start
            b't', b'e', b's', b't', 0x00, // Key "test"
            0x01, // String type
            b'k', b'e', b'y', 0x00, // Key "key"
            b'v', b'a', b'l', b'u', b'e', 0x00, // Value "value"
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let vdf = result.unwrap();
        assert_eq!(vdf.key, "root");

        let obj = vdf.as_obj().unwrap();
        let test_obj = obj.get("test").and_then(|v| v.as_obj());
        assert!(test_obj.is_some());

        let test_obj = test_obj.unwrap();
        let value = test_obj.get("key").and_then(|v| v.as_str());
        assert_eq!(value.map(|s| s.as_ref()), Some("value"));
    }

    #[test]
    fn test_parse_nested_objects() {
        // Nested objects: "outer" { "inner" { "key" "value" } }
        let data: &[u8] = &[
            0x00, // Object start
            b'o', b'u', b't', b'e', b'r', 0x00, // Key "outer"
            0x00, // Nested object start
            b'i', b'n', b'n', b'e', b'r', 0x00, // Key "inner"
            0x01, // String type
            b'k', b'e', b'y', 0x00, // Key "key"
            b'v', b'a', b'l', b'u', b'e', 0x00, // Value "value"
            0x08, // End inner object
            0x08, // End outer object
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let outer = obj.get("outer").and_then(|v| v.as_obj()).unwrap();
        let inner = outer.get("inner").and_then(|v| v.as_obj()).unwrap();
        let value = inner.get("key").and_then(|v| v.as_str());
        assert_eq!(value.map(|s| s.as_ref()), Some("value"));
    }

    #[test]
    fn test_parse_int32_value() {
        // Int32 value: "root" { "number" "42" }
        let data: &[u8] = &[
            0x00, // Object start
            b'r', b'o', b'o', b't', 0x00, // Key "root"
            0x02, // Int32 type
            b'n', b'u', b'm', b'b', b'e', b'r', 0x00, // Key "number"
            42, 0, 0, 0,    // Value 42 (little-endian)
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let root = obj.get("root").and_then(|v| v.as_obj()).unwrap();
        let value = root.get("number").and_then(|v| v.as_i32());
        assert_eq!(value, Some(42));
    }

    #[test]
    fn test_parse_uint64_value() {
        // UInt64 value
        let data: &[u8] = &[
            0x00, // Object start
            b'r', b'o', b'o', b't', 0x00, // Key "root"
            0x07, // UInt64 type
            b'n', b'u', b'm', b'b', b'e', b'r', 0x00, // Key "number"
            0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, // Value u32::MAX as u64
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let root = obj.get("root").and_then(|v| v.as_obj()).unwrap();
        let value = root.get("number").and_then(|v| v.as_u64());
        assert_eq!(value, Some(4294967295));
    }

    #[test]
    fn test_parse_float_value() {
        // Float value
        let data: &[u8] = &[
            0x00, // Object start
            b'r', b'o', b'o', b't', 0x00, // Key "root"
            0x03, // Float type
            b'v', b'a', b'l', 0x00, // Key "val"
            0x00, 0x00, 0x80, 0x3F, // Value 1.0 (little-endian)
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let root = obj.get("root").and_then(|v| v.as_obj()).unwrap();
        let value = root.get("val").and_then(|v| v.as_float());
        assert_eq!(value, Some(1.0));
    }

    #[test]
    fn test_parse_ptr_value() {
        // Pointer value
        let data: &[u8] = &[
            0x00, // Object start
            b'r', b'o', b'o', b't', 0x00, // Key "root"
            0x04, // Ptr type
            b'p', b't', b'r', 0x00, // Key "ptr"
            0xAB, 0xCD, 0xEF, 0x12, // Value 0x12EFCDAB
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let root = obj.get("root").and_then(|v| v.as_obj()).unwrap();
        let value = root.get("ptr").and_then(|v| v.as_pointer());
        assert_eq!(value, Some(0x12efcdab));
    }

    #[test]
    fn test_parse_color_value() {
        // Color value: RGBA (255, 0, 0, 255) = "25500255"
        let data: &[u8] = &[
            0x00, // Object start
            b'r', b'o', b'o', b't', 0x00, // Key "root"
            0x06, // Color type
            b'c', b'o', b'l', 0x00, // Key "col"
            0xFF, 0x00, 0x00, 0xFF, // RGBA: red, opaque
            0x08, // Object end
        ];

        let result = parse_shortcuts(data);
        assert!(result.is_ok());

        let vdf = result.unwrap();
        let obj = vdf.as_obj().unwrap();
        let root = obj.get("root").and_then(|v| v.as_obj()).unwrap();
        let value = root.get("col").and_then(|v| v.as_color());
        assert_eq!(value, Some([255, 0, 0, 255]));
    }
}
