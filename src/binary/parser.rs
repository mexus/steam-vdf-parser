//! Binary VDF parser implementation.
//!
//! Supports Steam's binary VDF formats:
//! - shortcuts.vdf (simple binary format)
//! - appinfo.vdf (with optional string table)

use std::borrow::Cow;

use crate::binary::types::{APPINFO_MAGIC_28, APPINFO_MAGIC_29, BinaryType};
use crate::error::{Error, Result};
use crate::value::{Obj, Value, Vdf};

/// Parse binary VDF data (autodetects format).
///
/// Attempts to parse as appinfo.vdf first, then falls back to shortcuts.vdf format.
pub fn parse(input: &[u8]) -> Result<Vdf<'static>> {
    // Check if this looks like appinfo format (starts with magic)
    if input.len() >= 4 {
        let magic = u32::from_le_bytes([input[0], input[1], input[2], input[3]]);
        if magic == APPINFO_MAGIC_28 || magic == APPINFO_MAGIC_29 {
            return parse_appinfo(input);
        }
    }

    // Otherwise, parse as shortcuts format
    parse_shortcuts(input)
}

/// Parse shortcuts.vdf format binary data.
///
/// This is the simpler binary format used by Steam for shortcuts and other data.
///
/// Format:
/// - Each entry starts with a type byte
/// - Type 0x00: Object start (key is the object name)
/// - Type 0x01: String value
/// - Type 0x02: Int32 value
/// - Type 0x08: Object end
///
/// All strings are null-terminated.
pub fn parse_shortcuts(input: &[u8]) -> Result<Vdf<'static>> {
    let (rest, obj) = parse_object(input, &[] as &[&str])?;

    // There should be nothing left except possibly the end marker
    let _ = rest;

    Ok(Vdf {
        key: Cow::Owned("root".to_string()),
        value: Value::Obj(obj),
    })
}

/// Parse appinfo.vdf format binary data.
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
///   - 20 bytes: SHA1 Hash
///   - 4 bytes: ChangeNumber
///   - 20 bytes: Binary SHA1
///   - Then the VDF data for the app (starts with 0x00)
/// - String table (if magic == 0x07564429, at string_table_offset)
///
/// App entry header is 68 bytes.
pub fn parse_appinfo(input: &[u8]) -> Result<Vdf<'static>> {
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
    let string_table: Vec<String> = if let Some(offset) = string_table_offset {
        let table_start = offset;
        if table_start >= input.len() {
            return Err(Error::UnexpectedEndOfInput);
        }
        parse_string_table(&input[table_start..])?
    } else {
        Vec::new()
    };

    // Convert to string references for use in parsing
    let table_refs: Vec<&str> = string_table.iter().map(|s| s.as_str()).collect();

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
        // info_state(4) + last_updated(4) + pics_token(8) + sha1_text(20) + change_number(4) + sha1_binary(20)
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
        let use_string_table = string_table_offset.is_some();
        let (_vdf_rest, app_obj) = parse_object_appinfo(vdf_data, &table_refs, use_string_table)?;

        // Insert with app ID as key
        obj.insert(
            Cow::Owned(app_id.to_string()),
            Value::Obj(app_obj),
        );
        rest = &rest[vdf_end..];
    }

    Ok(Vdf {
        key: Cow::Owned(format!("appinfo_universe_{}", universe)),
        value: Value::Obj(obj),
    })
}

/// Parse an object from binary data for appinfo format.
///
/// Returns the remaining input and the parsed object.
///
/// # Parameters
/// - `input`: The binary data to parse
/// - `string_table`: The string table (empty for v28, populated for v29)
/// - `use_string_table`: If true, use v29 parsing (uint32 indices); if false, use v28 parsing (null-terminated strings)
fn parse_object_appinfo<'a>(
    input: &'a [u8],
    string_table: &[&str],
    use_string_table: bool,
) -> Result<(&'a [u8], Obj<'static>)> {
    let mut obj = Obj::new();
    let mut rest = input;

    loop {
        if rest.is_empty() {
            // At root level, EOF is acceptable - file may end without trailing 0x08
            return Ok((rest, obj));
        }

        // Peek at the type byte
        let type_byte = rest[0];
        let typ = BinaryType::from_byte(type_byte);

        match typ {
            Some(BinaryType::ObjectEnd) => {
                // Consume the end marker and return
                rest = &rest[1..];
                return Ok((rest, obj));
            }
            Some(BinaryType::None) => {
                // Map entry: 0x00 [key] { ... entries ... }
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                // The entries following this key belong to the new object until we see 0x08
                let (new_rest, nested_obj) =
                    parse_object_appinfo(new_rest, string_table, use_string_table)?;
                obj.insert(key, Value::Obj(nested_obj));
                rest = new_rest;
            }
            Some(BinaryType::String) => {
                // String entry: 0x01 [key] [value]
                // KEY may be from string table (v29) or inline (v28)
                // VALUE is ALWAYS inline null-terminated string (never from string table!)
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                // VALUE is always inline null-terminated string
                let (new_rest, value) = parse_null_terminated_string(new_rest)?;
                obj.insert(key, Value::Str(Cow::Owned(value)));
                rest = new_rest;
            }
            Some(BinaryType::Int32) => {
                // Int32 entry: 0x02 [key] 4-byte-value
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value =
                    i32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(key, Value::Str(Cow::Owned(value.to_string())));
                rest = &new_rest[4..];
            }
            Some(BinaryType::UInt64) => {
                // UInt64 entry: 0x07 [key] 8-byte-value
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                if new_rest.len() < 8 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value = u64::from_le_bytes([
                    new_rest[0], new_rest[1], new_rest[2], new_rest[3], new_rest[4],
                    new_rest[5], new_rest[6], new_rest[7],
                ]);
                obj.insert(key, Value::Str(Cow::Owned(value.to_string())));
                rest = &new_rest[8..];
            }
            Some(BinaryType::Float) => {
                // Float entry: 0x03 [key] 4-byte-float
                rest = &rest[1..];
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value = f32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(key, Value::Str(Cow::Owned(value.to_string())));
                rest = &new_rest[4..];
            }
            Some(BinaryType::Ptr) => {
                // Pointer entry: 0x04 [key] 4-byte-pointer
                rest = &rest[1..];
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                // Just read as u32 and format as hex
                let value = u32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(
                    key,
                    Value::Str(Cow::Owned(format!("0x{:08x}", value))),
                );
                rest = &new_rest[4..];
            }
            Some(BinaryType::WString) => {
                // WideString entry: 0x05 [key] utf16-string\0\0
                // Note: WString seems to still use inline strings even in v29
                rest = &rest[1..];
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                let (new_rest, value) = parse_null_terminated_wstring(new_rest)?;
                obj.insert(key, Value::Str(Cow::Owned(value)));
                rest = new_rest;
            }
            Some(BinaryType::Color) => {
                // Color entry: 0x06 [key] 4-bytes RGBA
                rest = &rest[1..];
                let (new_rest, key) = if use_string_table {
                    parse_string_table_index(rest, string_table)?
                } else {
                    let (r, k) = parse_null_terminated_string(rest)?;
                    (r, Cow::Owned(k))
                };
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let r = new_rest[0];
                let g = new_rest[1];
                let b = new_rest[2];
                let a = new_rest[3];
                obj.insert(
                    key,
                    Value::Str(Cow::Owned(format!("{}{}{}{}", r, g, b, a))),
                );
                rest = &new_rest[4..];
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

/// Parse an object from binary data.
///
/// Returns the remaining input and the parsed object.
/// This is used for shortcuts.vdf format which doesn't use string tables.
fn parse_object<'a>(input: &'a [u8], string_table: &[&str]) -> Result<(&'a [u8], Obj<'static>)> {
    let mut obj = Obj::new();
    let mut rest = input;

    loop {
        if rest.is_empty() {
            // At root level, EOF is acceptable - file may end without trailing 0x08
            return Ok((rest, obj));
        }

        // Peek at the type byte
        let type_byte = rest[0];
        let typ = BinaryType::from_byte(type_byte);

        match typ {
            Some(BinaryType::ObjectEnd) => {
                // Consume the end marker and return
                rest = &rest[1..];
                return Ok((rest, obj));
            }
            Some(BinaryType::None) => {
                // Map entry: 0x00 "name" { ... entries ... }
                // Parse the key, then recursively parse entries into a new object
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                // The entries following this key belong to the new object until we see 0x08
                let (new_rest, nested_obj) = parse_object(new_rest, string_table)?;
                obj.insert(Cow::Owned(key.to_string()), Value::Obj(nested_obj));
                rest = new_rest;
            }
            Some(BinaryType::String) => {
                // String entry: 0x01 "key" "value"
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                let (new_rest, value) = parse_string_value(new_rest, string_table)?;
                obj.insert(Cow::Owned(key.to_string()), Value::Str(value));
                rest = new_rest;
            }
            Some(BinaryType::Int32) => {
                // Int32 entry: 0x02 "key" 4-byte-value
                rest = &rest[1..]; // Skip type byte
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value =
                    i32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(
                    Cow::Owned(key.to_string()),
                    Value::Str(Cow::Owned(value.to_string())),
                );
                rest = &new_rest[4..];
            }
            Some(BinaryType::Float) => {
                // Float entry: 0x03 "key" 4-byte-float
                rest = &rest[1..];
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value = f32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(
                    Cow::Owned(key.to_string()),
                    Value::Str(Cow::Owned(value.to_string())),
                );
                rest = &new_rest[4..];
            }
            Some(BinaryType::Ptr) => {
                // Pointer entry: 0x04 "key" 4-byte-pointer
                rest = &rest[1..];
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                // Just read as u32 and format as hex
                let value = u32::from_le_bytes([new_rest[0], new_rest[1], new_rest[2], new_rest[3]]);
                obj.insert(
                    Cow::Owned(key.to_string()),
                    Value::Str(Cow::Owned(format!("0x{:08x}", value))),
                );
                rest = &new_rest[4..];
            }
            Some(BinaryType::WString) => {
                // WideString entry: 0x05 "key" utf16-string\0\0
                rest = &rest[1..];
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                let (new_rest, value) = parse_null_terminated_wstring(new_rest)?;
                obj.insert(Cow::Owned(key.to_string()), Value::Str(Cow::Owned(value)));
                rest = new_rest;
            }
            Some(BinaryType::Color) => {
                // Color entry: 0x06 "key" 4-bytes RGBA
                rest = &rest[1..];
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                if new_rest.len() < 4 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let r = new_rest[0];
                let g = new_rest[1];
                let b = new_rest[2];
                let a = new_rest[3];
                obj.insert(
                    Cow::Owned(key.to_string()),
                    Value::Str(Cow::Owned(format!("{}{}{}{}", r, g, b, a))),
                );
                rest = &new_rest[4..];
            }
            Some(BinaryType::UInt64) => {
                // UInt64 entry: 0x07 "key" 8-byte-value
                rest = &rest[1..];
                let (new_rest, key) = parse_null_terminated_string(rest)?;
                if new_rest.len() < 8 {
                    return Err(Error::UnexpectedEndOfInput);
                }
                let value = u64::from_le_bytes([
                    new_rest[0], new_rest[1], new_rest[2], new_rest[3], new_rest[4],
                    new_rest[5], new_rest[6], new_rest[7],
                ]);
                obj.insert(
                    Cow::Owned(key.to_string()),
                    Value::Str(Cow::Owned(value.to_string())),
                );
                rest = &new_rest[8..];
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

/// Parse a null-terminated string (UTF-8).
fn parse_null_terminated_string(input: &[u8]) -> Result<(&[u8], String)> {
    let null_pos = input
        .iter()
        .position(|&b| b == 0)
        .ok_or(Error::UnexpectedEndOfInput)?;

    let bytes = &input[..null_pos];
    let string = std::str::from_utf8(bytes)
        .map_err(|_| Error::InvalidUtf8 { offset: 0 })?
        .to_string();

    Ok((&input[null_pos + 1..], string))
}

/// Parse a null-terminated wide string (UTF-16LE).
///
/// WideString is terminated by two zero bytes (0x00 0x00).
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

    let string = String::from_utf16(&utf16_data)
        .map_err(|_| Error::InvalidUtf8 { offset: 0 })?
        .to_string();

    Ok((&input[i + 2..], string))
}

/// Parse a string value (either inline or from string table).
///
/// In appinfo.vdf format with string table, type 0x02 can indicate a pooled string.
/// Note: shortcuts.vdf doesn't use string tables, so the parameter is unused.
fn parse_string_value<'a>(
    input: &'a [u8],
    _string_table: &[&str],
) -> Result<(&'a [u8], Cow<'static, str>)> {
    // Check if this is a pooled string (starts with a special marker)
    // In practice, we need to read the string and see if it's a valid reference

    let (rest, string) = parse_null_terminated_string(input)?;

    Ok((rest, Cow::Owned(string)))
}

/// Parse the string table section (v29 format).
///
/// Format:
/// - 4 bytes: string_count (little-endian u32)
/// - Then string_count null-terminated UTF-8 strings
fn parse_string_table(input: &[u8]) -> Result<Vec<String>> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }

    // Read string_count (4 bytes, little-endian)
    let string_count = u32::from_le_bytes([input[0], input[1], input[2], input[3]]) as usize;

    let mut strings = Vec::with_capacity(string_count);
    let mut rest = &input[4..];

    // Read exactly string_count null-terminated strings
    for _ in 0..string_count {
        if rest.is_empty() {
            return Err(Error::UnexpectedEndOfInput);
        }
        let (new_rest, string) = parse_null_terminated_string(rest)?;
        strings.push(string);
        rest = new_rest;
    }

    Ok(strings)
}

/// Parse a uint32 string table index and return the referenced string.
///
/// In v29 format, strings are stored as uint32 indices into the string table
/// rather than inline null-terminated strings.
/// Note: Indices are stored in LITTLE-ENDIAN format.
fn parse_string_table_index<'a>(
    input: &'a [u8],
    string_table: &[&str],
) -> Result<(&'a [u8], Cow<'static, str>)> {
    if input.len() < 4 {
        return Err(Error::UnexpectedEndOfInput);
    }

    let index = u32::from_le_bytes([input[0], input[1], input[2], input[3]]) as usize;

    if index >= string_table.len() {
        // Try big-endian as fallback (some entries may use different endianness)
        let index_be = u32::from_be_bytes([input[0], input[1], input[2], input[3]]) as usize;
        if index_be < string_table.len() {
            let string = string_table[index_be];
            return Ok((&input[4..], Cow::Owned(string.to_string())));
        }
        return Err(Error::InvalidStringIndex {
            index,
            max: string_table.len(),
        });
    }

    let string = string_table[index];
    Ok((&input[4..], Cow::Owned(string.to_string())))
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
        if let Err(e) = &result {
            println!("Error: {:?}", e);
        }
        assert!(result.is_ok());

        let vdf = result.unwrap();
        assert_eq!(vdf.key, "root");

        let obj = vdf.as_obj().unwrap();
        let test_obj = obj.get("test").and_then(|v| v.as_obj());
        assert!(test_obj.is_some());

        let test_obj = test_obj.unwrap();
        let value = test_obj.get("key").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Owned("value".to_string())));
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
        assert_eq!(value, Some(&Cow::Owned("value".to_string())));
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
        let value = root.get("number").and_then(|v| v.as_str());
        assert_eq!(value, Some(&Cow::Owned("42".to_string())));
    }
}
