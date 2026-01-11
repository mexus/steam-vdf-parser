# steam-vdf-parser

A Rust parser for Steam's VDF (Valve Data Format) files.

## Features

- TBD

## Installation

- TBD

## Usage

- TBD

## VDF Format Documentation

### Text VDF Format

Steam's text format is a simple key-value serialization with nested objects:

```
"root_key"
{
    "key1" "value1"
    "nested_key"
    {
        "subkey" "subvalue"
    }
}
```

**Grammar rules:**
- Tokens can be quoted (`"key"`) or unquoted (`key`)
- Objects are delimited by `{` and `}`
- String values are quoted
- Comments start with `//` and extend to end of line
- Whitespace (including newlines) is generally ignored

### Binary VDF Format (shortcuts.vdf)

Simple binary format used by Steam for shortcuts and other data.

| Type Byte | Name | Description |
|-----------|------|-------------|
| 0x00 | None/Object | Start of an object (followed by null-terminated key name) |
| 0x01 | String | Null-terminated UTF-8 string value |
| 0x02 | Int32 | 4-byte little-endian integer |
| 0x03 | Float | 4-byte little-endian float |
| 0x04 | Pointer | 4-byte pointer value |
| 0x05 | WString | Null-terminated UTF-16LE string (terminated by `0x00 0x00`) |
| 0x06 | Color | 4 bytes RGBA |
| 0x07 | UInt64 | 8-byte little-endian unsigned integer |
| 0x08 | ObjectEnd | End of current object |

**Entry format:** `[TypeByte] [NullTerminatedKey] [Value...]`

### Binary VDF Format (appinfo.vdf)

Complex format with versioned structure for caching Steam application metadata.

#### File Header

| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0x00 | 4 | Magic | `0x07564427` (v27), `0x07564428` (v28), or `0x07564429` (v29) |
| 0x04 | 4 | Universe | Always 1 (public) |
| 0x08 | 8 | String Table Offset | Present only in v29 |

#### String Table (v29 only)

Located at the `String Table Offset`:

| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0x00 | 4 | String Count | Number of strings (little-endian) |
| 0x04 | - | Strings | `String Count` null-terminated UTF-8 strings |

In v29, object **keys** are stored as uint32 indices into the string table. String **values** are always inline null-terminated strings.

#### App Entry Header

Each app entry has a 68-byte header:

| Offset | Size | Field | Description |
|--------|------|-------|-------------|
| 0x00 | 4 | App ID | Steam application ID |
| 0x04 | 4 | Size | Size of everything **after** this field (60 bytes + VDF data) |
| 0x08 | 4 | Info State | Flags (e.g., 2 = available) |
| 0x0C | 4 | Last Updated | Unix timestamp |
| 0x10 | 8 | PICS Token | Access token for PICS API |
| 0x18 | 20 | SHA1 | Hash of VDF payload |
| 0x2C | 4 | Change Number | Sequence number |
| 0x30 | 20 | Binary SHA1 | Hash of binary VDF data (v28/v29 only) |

After the 68-byte header, the VDF data begins. The VDF data length is `Size - 60`.

#### VDF Data Structure (appinfo)

The binary VDF data uses the same type bytes as shortcuts.vdf, with key encoding differences:

- **v27/v28**: Keys are null-terminated UTF-8 strings
- **v29**: Keys are uint32 indices into the string table (little-endian)
- **All versions**: String **values** are always null-terminated UTF-8 strings (inline, not from string table)

## Testing

- TBD

## License

- TBD
