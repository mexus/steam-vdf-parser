//! Binary VDF parser implementation.
//!
//! Supports Steam's binary VDF formats:
//! - shortcuts.vdf (simple binary format)
//! - appinfo.vdf (with optional string table)

use std::borrow::Cow;

use crate::binary::types::{
    APPINFO_MAGIC_28, APPINFO_MAGIC_29, BinaryType, PACKAGEINFO_MAGIC_39, PACKAGEINFO_MAGIC_40,
    PACKAGEINFO_MAGIC_BASE,
};
use crate::error::{Error, Result, with_offset};
use crate::value::{Obj, Value, Vdf};

// ===== Appinfo Header Constants =====

/// Size of the appinfo entry header (up to and including the size field).
const APPINFO_HEADER_SIZE: usize = 8;

/// Size of the header after the size field (60 bytes).
const APPINFO_HEADER_AFTER_SIZE: usize = 60;

/// Total size of the appinfo entry header.
const APPINFO_ENTRY_HEADER_SIZE: usize = APPINFO_HEADER_SIZE + APPINFO_HEADER_AFTER_SIZE;

/// Offset where VDF data starts within an appinfo entry.
const APPINFO_VDF_DATA_OFFSET: usize = APPINFO_ENTRY_HEADER_SIZE;

// ===== Helper Functions =====

/// Read a little-endian u32 from the start of a slice.
///
/// Returns `None` if the slice is too small.
#[inline]
fn read_u32_le(input: &[u8]) -> Option<u32> {
    input.get(..4).and_then(|bytes| {
        let arr: [u8; 4] = bytes.try_into().ok()?;
        Some(u32::from_le_bytes(arr))
    })
}

/// Read a little-endian u64 from the start of a slice.
///
/// Returns `None` if the slice is too small.
#[inline]
fn read_u64_le(input: &[u8]) -> Option<u64> {
    input.get(..8).and_then(|bytes| {
        let arr: [u8; 8] = bytes.try_into().ok()?;
        Some(u64::from_le_bytes(arr))
    })
}

/// Read a little-endian u32 from the start of a slice, returning an error if too small.
fn ensure_read_u32_le(input: &[u8]) -> Result<(&[u8], u32)> {
    read_u32_le(input)
        .map(|value| (&input[4..], value))
        .ok_or(Error::UnexpectedEndOfInput {
            context: "reading u32",
            offset: 0,
            expected: 4,
            actual: input.len(),
        })
}

/// Parse configuration for binary VDF formats.
///
/// Encapsulates the differences between shortcuts.vdf and appinfo.vdf formats.
#[derive(Clone, Copy, Debug, PartialEq, Default)]
struct ParseConfig<'input, 'table> {
    /// Strategy for parsing keys
    key_mode: KeyMode<'input, 'table>,
}

/// Key parsing strategy for binary VDF formats.
#[derive(Clone, Copy, Debug, PartialEq, Default)]
enum KeyMode<'input, 'table> {
    /// Parse keys as null-terminated UTF-8 strings (v28, shortcuts)
    #[default]
    NullTerminated,
    /// Parse keys as u32 indices into string table (v29)
    StringTableIndex {
        string_table: &'table StringTable<'input>,
    },
}

/// String table for v29 appinfo format.
///
/// Encapsulates pre-extracted strings from the string table section,
/// enabling O(1) lookups by index.
#[derive(Clone, Debug, PartialEq)]
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

impl<'a> KeyMode<'a, '_> {
    /// Parse a key from input according to this mode.
    fn parse_key(&self, input: &'a [u8]) -> Result<(&'a [u8], Cow<'a, str>)> {
        match self {
            KeyMode::NullTerminated => {
                let (rest, s) = parse_null_terminated_string_borrowed(input)?;
                Ok((rest, Cow::Borrowed(s)))
            }
            KeyMode::StringTableIndex { string_table } => {
                let (rest, index) = ensure_read_u32_le(input)?;
                let s = string_table.get(index as usize)?;
                Ok((rest, Cow::Borrowed(s)))
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
    if let Some(magic) = read_u32_le(input)
        && (magic == APPINFO_MAGIC_28 || magic == APPINFO_MAGIC_29)
    {
        // parse_appinfo returns Vdf<'static>, which is compatible with Vdf<'_>
        return parse_appinfo(input);
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
    let config = ParseConfig::default();
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
/// App entry header is `APPINFO_ENTRY_HEADER_SIZE` (68) bytes.
pub fn parse_appinfo(input: &[u8]) -> Result<Vdf<'_>> {
    if input.len() < 16 {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading appinfo header",
            offset: input.len(),
            expected: 16,
            actual: input.len(),
        });
    }

    let Some(magic) = read_u32_le(input) else {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading magic number",
            offset: 0,
            expected: 4,
            actual: input.len(),
        });
    };
    let Some(universe) = read_u32_le(&input[4..]) else {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading universe",
            offset: 4,
            expected: 4,
            actual: input.len() - 4,
        });
    };

    let (string_table_offset, mut rest) = match magic {
        APPINFO_MAGIC_28 => (None, &input[8..]),
        APPINFO_MAGIC_29 => {
            let Some(offset) = read_u64_le(&input[8..]) else {
                return Err(Error::UnexpectedEndOfInput {
                    context: "reading string table offset",
                    offset: 8,
                    expected: 8,
                    actual: input.len() - 8,
                });
            };
            (Some(offset as usize), &input[16..])
        }
        _ => {
            return Err(Error::InvalidMagic {
                found: magic,
                expected: &[APPINFO_MAGIC_28, APPINFO_MAGIC_29],
            });
        }
    };

    // Parse the string table if present
    let string_table = if let Some(offset) = string_table_offset {
        if offset >= input.len() {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading string table",
                offset,
                expected: 4,
                actual: input.len() - offset,
            });
        }
        Some(parse_string_table(&input[offset..]).map_err(with_offset(offset))?)
    } else {
        None
    };

    let mut obj = Obj::new();

    // Calculate where apps end (at string table for v29, or EOF for v28)
    let apps_end_offset = string_table_offset.unwrap_or(input.len());

    // Use v29 format (string table) if string_table_offset is Some
    let config = ParseConfig {
        key_mode: if let Some(string_table) = &string_table {
            KeyMode::StringTableIndex { string_table }
        } else {
            KeyMode::NullTerminated
        },
    };

    loop {
        // Check if we've reached the end of apps section
        let current_offset = input.len() - rest.len();
        if current_offset >= apps_end_offset {
            break;
        }

        // Not enough data for an app entry header.
        if rest.len() < APPINFO_ENTRY_HEADER_SIZE {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading app entry header",
                offset: current_offset,
                expected: APPINFO_ENTRY_HEADER_SIZE,
                actual: rest.len(),
            });
        }

        // App ID (offset 0)
        let Some(app_id) = read_u32_le(rest) else {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading app id",
                offset: current_offset,
                expected: 4,
                actual: rest.len(),
            });
        };
        if app_id == 0 {
            break;
        }

        // Size (offset 4) - includes everything AFTER this field (APPINFO_HEADER_AFTER_SIZE bytes + VDF data)
        let Some(size) = read_u32_le(&rest[4..]) else {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading entry size",
                offset: current_offset + 4,
                expected: 4,
                actual: rest.len() - 4,
            });
        };
        let size = size as usize;

        // VDF data starts after the header
        let vdf_size = size - APPINFO_HEADER_AFTER_SIZE;
        let vdf_end = APPINFO_VDF_DATA_OFFSET + vdf_size;

        if vdf_end > rest.len() {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading VDF data",
                offset: current_offset + vdf_end,
                expected: vdf_end,
                actual: rest.len(),
            });
        }

        let vdf_data = &rest[APPINFO_VDF_DATA_OFFSET..vdf_end];
        let vdf_offset = current_offset + APPINFO_VDF_DATA_OFFSET;

        let (_vdf_rest, app_obj) =
            parse_object(vdf_data, &config).map_err(with_offset(vdf_offset))?;

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
fn parse_object<'a>(input: &'a [u8], config: &ParseConfig<'a, '_>) -> Result<(&'a [u8], Obj<'a>)> {
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
                let offset = input.len() - remainder.len();
                rest = remainder;

                match typ {
                    Some(BinaryType::ObjectEnd) => {
                        // Consume the end marker and return
                        return Ok((rest, obj));
                    }
                    Some(BinaryType::None) => {
                        // Map entry: 0x00 [key] { ... entries ... }
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let (new_rest, nested_obj) = parse_object(new_rest, config)?;
                        obj.insert(key, Value::Obj(nested_obj));
                        rest = new_rest;
                    }
                    Some(BinaryType::String) => {
                        // String entry: 0x01 [key] [value]
                        // VALUE is ALWAYS inline null-terminated string (never from string table!)
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) = parse_null_terminated_string_borrowed(new_rest)
                            .map_err(with_offset(value_offset))?;
                        obj.insert(key, Value::Str(Cow::Borrowed(value)));
                        rest = new_rest;
                    }
                    Some(BinaryType::Int32) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_int32(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::UInt64) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_uint64(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Float) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_float(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Ptr) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_ptr(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::WString) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_wstring(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    Some(BinaryType::Color) => {
                        let key_offset = input.len() - rest.len();
                        let (new_rest, key) = config
                            .key_mode
                            .parse_key(rest)
                            .map_err(with_offset(key_offset))?;
                        let value_offset = input.len() - new_rest.len();
                        let (new_rest, value) =
                            parse_value_color(new_rest).map_err(with_offset(value_offset))?;
                        obj.insert(key, value);
                        rest = new_rest;
                    }
                    None => {
                        // Unknown type byte
                        return Err(Error::UnknownType { type_byte, offset });
                    }
                }
            }
        }
    }
}

// ===== Value Parser Functions =====

/// Parse an Int32 value (4 bytes, little-endian).
fn parse_value_int32<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let arr = <[u8; 4]>::try_from(input.get(..4).ok_or(Error::UnexpectedEndOfInput {
        context: "reading int32",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?)
    .map_err(|_| Error::UnexpectedEndOfInput {
        context: "reading int32",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?;
    let value = i32::from_le_bytes(arr);
    Ok((&input[4..], Value::I32(value)))
}

/// Parse a UInt64 value (8 bytes, little-endian).
fn parse_value_uint64<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let arr = <[u8; 8]>::try_from(input.get(..8).ok_or(Error::UnexpectedEndOfInput {
        context: "reading uint64",
        offset: 0,
        expected: 8,
        actual: input.len(),
    })?)
    .map_err(|_| Error::UnexpectedEndOfInput {
        context: "reading uint64",
        offset: 0,
        expected: 8,
        actual: input.len(),
    })?;
    let value = u64::from_le_bytes(arr);
    Ok((&input[8..], Value::U64(value)))
}

/// Parse a Float value (4 bytes, little-endian).
fn parse_value_float<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let arr = <[u8; 4]>::try_from(input.get(..4).ok_or(Error::UnexpectedEndOfInput {
        context: "reading float",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?)
    .map_err(|_| Error::UnexpectedEndOfInput {
        context: "reading float",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?;
    let value = f32::from_le_bytes(arr);
    Ok((&input[4..], Value::Float(value)))
}

/// Parse a Pointer value (4 bytes, little-endian).
fn parse_value_ptr<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let (rest, value) = ensure_read_u32_le(input)?;
    Ok((rest, Value::Pointer(value)))
}

/// Parse a WideString value (UTF-16LE, null-terminated).
fn parse_value_wstring<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let (rest, string) = parse_null_terminated_wstring(input)?;
    Ok((rest, Value::Str(Cow::Owned(string))))
}

/// Parse a Color value (4 bytes RGBA).
fn parse_value_color<'a>(input: &'a [u8]) -> Result<(&'a [u8], Value<'a>)> {
    let arr = <[u8; 4]>::try_from(input.get(..4).ok_or(Error::UnexpectedEndOfInput {
        context: "reading color",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?)
    .map_err(|_| Error::UnexpectedEndOfInput {
        context: "reading color",
        offset: 0,
        expected: 4,
        actual: input.len(),
    })?;
    Ok((&input[4..], Value::Color(arr)))
}

// ===== String Parsing Functions =====

/// Parse a null-terminated string (UTF-8), returning a borrowed slice.
///
/// This is the zero-copy version that borrows from the input when possible.
fn parse_null_terminated_string_borrowed(input: &[u8]) -> Result<(&[u8], &str)> {
    let null_pos = input
        .iter()
        .position(|&b| b == 0)
        .ok_or(Error::UnexpectedEndOfInput {
            context: "reading null-terminated string",
            offset: 0,
            expected: 1,
            actual: input.len(),
        })?;

    let bytes = &input[..null_pos];
    let string = std::str::from_utf8(bytes).map_err(|e| Error::InvalidUtf8 {
        offset: e.valid_up_to(),
    })?;

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
        return Err(Error::UnexpectedEndOfInput {
            context: "reading null-terminated wide string",
            offset: i,
            expected: 2,
            actual: input.len().saturating_sub(i),
        });
    }

    // Convert UTF-16LE to u16 code units
    let utf16_units = input[..i]
        .chunks_exact(2)
        .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]));

    // Decode UTF-16 to char and then to String
    let string: String = std::char::decode_utf16(utf16_units)
        .enumerate()
        .map(|(pos, r)| {
            r.map_err(|_| Error::InvalidUtf16 {
                offset: pos * 2,
                position: pos,
            })
        })
        .collect::<std::result::Result<_, _>>()?;

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
    let (mut rest, string_count) = ensure_read_u32_le(input)?;
    let string_count = string_count as usize;

    let mut strings = Vec::with_capacity(string_count);

    // Extract each null-terminated string
    for _ in 0..string_count {
        if rest.is_empty() {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading string table entry",
                offset: input.len() - rest.len(),
                expected: 1,
                actual: 0,
            });
        }
        let (new_rest, string) = parse_null_terminated_string_borrowed(rest)?;
        strings.push(string);
        rest = new_rest;
    }

    Ok(StringTable { strings })
}

/// Header size for packageinfo entries (package_id + hash + change_number + token).
const PACKAGEINFO_ENTRY_HEADER_SIZE_V39: usize = 4 + 20 + 4; // package_id + hash + change_number
const PACKAGEINFO_ENTRY_HEADER_SIZE_V40: usize = 4 + 20 + 4 + 8; // + token

/// Parse packageinfo.vdf format binary data.
///
/// This function returns zero-copy data where possible - strings are borrowed from
/// the input buffer.
///
/// Format:
/// - 4 bytes: Magic number + version (0x06565527 for v39, 0x06565528 for v40)
///   - Upper 3 bytes: 0x065655 (magic)
///   - Lower 1 byte: version (27 = 39, 28 = 40)
/// - 4 bytes: Universe
/// - Repeated package entries until package_id == 0xFFFFFFFF:
///   - 4 bytes: Package ID (uint32)
///   - 20 bytes: SHA-1 hash
///   - 4 bytes: Change number (uint32)
///   - 8 bytes: PICS token (uint64, only in v40+)
///   - Binary VDF blob (KeyValues1 binary) with package metadata
pub fn parse_packageinfo(input: &[u8]) -> Result<Vdf<'_>> {
    if input.len() < 8 {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading packageinfo header",
            offset: input.len(),
            expected: 8,
            actual: input.len(),
        });
    }

    let Some(magic) = read_u32_le(input) else {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading magic number",
            offset: 0,
            expected: 4,
            actual: input.len(),
        });
    };

    // Extract version from lower byte and magic from upper 3 bytes
    let version = magic & 0xFF;
    let magic_base = magic >> 8;

    if magic_base != PACKAGEINFO_MAGIC_BASE {
        return Err(Error::InvalidMagic {
            found: magic,
            expected: &[PACKAGEINFO_MAGIC_39, PACKAGEINFO_MAGIC_40],
        });
    }

    if version != 39 && version != 40 {
        return Err(Error::InvalidMagic {
            found: magic,
            expected: &[PACKAGEINFO_MAGIC_39, PACKAGEINFO_MAGIC_40],
        });
    }

    let Some(universe) = read_u32_le(&input[4..]) else {
        return Err(Error::UnexpectedEndOfInput {
            context: "reading universe",
            offset: 4,
            expected: 4,
            actual: input.len() - 4,
        });
    };

    let has_token = version >= 40;
    let header_size = if has_token {
        PACKAGEINFO_ENTRY_HEADER_SIZE_V40
    } else {
        PACKAGEINFO_ENTRY_HEADER_SIZE_V39
    };

    let mut rest = &input[8..];
    let mut obj = Obj::new();

    loop {
        // Check if we have at least 4 bytes for the package ID
        if rest.len() < 4 {
            // At EOF or termination marker, exit gracefully
            break;
        }

        // Read package ID
        let Some(package_id) = read_u32_le(rest) else {
            break;
        };

        // Check for termination marker
        if package_id == 0xFFFFFFFF {
            break;
        }

        // Now ensure we have enough data for the full header
        if rest.len() < header_size {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading package entry header",
                offset: input.len() - rest.len(),
                expected: header_size,
                actual: rest.len(),
            });
        }

        // Skip hash (20 bytes), read change number
        let hash_offset = 4;
        let change_number_offset = hash_offset + 20;

        let Some(change_number) = read_u32_le(&rest[change_number_offset..]) else {
            return Err(Error::UnexpectedEndOfInput {
                context: "reading change number",
                offset: input.len() - rest.len() + change_number_offset,
                expected: 4,
                actual: rest.len() - change_number_offset,
            });
        };

        // Skip token if present (8 bytes after change_number)
        let vdf_data_offset = if has_token {
            change_number_offset + 4 + 8
        } else {
            change_number_offset + 4
        };

        // Parse the VDF data for this package
        let vdf_data = &rest[vdf_data_offset..];

        let config = ParseConfig::default(); // Uses null-terminated keys like shortcuts

        let (_vdf_rest, package_obj) =
            parse_object(vdf_data, &config).map_err(with_offset(input.len() - vdf_data.len()))?;

        // Create metadata object for this package
        let mut package_with_meta = Obj::new();

        // Add metadata fields
        package_with_meta.insert(Cow::Borrowed("packageid"), Value::I32(package_id as i32));
        package_with_meta.insert(
            Cow::Borrowed("change_number"),
            Value::U64(change_number as u64),
        );
        package_with_meta.insert(
            Cow::Borrowed("sha1"),
            Value::Str(Cow::Owned(hex::encode(
                &rest[hash_offset..hash_offset + 20],
            ))),
        );

        // Merge the parsed VDF data
        for (key, value) in package_obj.iter() {
            package_with_meta.insert(key.clone(), value.clone());
        }

        // Insert with package ID as key
        obj.insert(
            Cow::Owned(package_id.to_string()),
            Value::Obj(package_with_meta),
        );

        // Find the end of this VDF object to move to the next entry
        // The VDF object is parsed starting with 0x00 and ending at the matching 0x08
        let (_vdf_rest, _) =
            parse_object(vdf_data, &config).map_err(with_offset(input.len() - vdf_data.len()))?;
        let vdf_end = vdf_data.len() - _vdf_rest.len();
        rest = &rest[vdf_data_offset + vdf_end..];
    }

    Ok(Vdf {
        key: Cow::Owned(format!("packageinfo_universe_{}", universe)),
        value: Value::Obj(obj),
    })
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
