//! Binary VDF format parser.
//!
//! Supports Steam's binary VDF formats:
//! - shortcuts.vdf format (simple binary)
//! - appinfo.vdf format (with optional string table)

mod parser;
mod types;

pub use parser::{parse, parse_appinfo, parse_packageinfo, parse_shortcuts};
pub use types::{APPINFO_MAGIC_40, APPINFO_MAGIC_41, BinaryType};
