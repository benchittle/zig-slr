const table = @import("slr-table-generator.zig");
const parser = @import("slr-parser.zig");

pub const Grammar = table.Grammar;
pub const ParseTable = table.ParseTable;

pub const ParseTree = parser.ParseTree;
pub const Parser = parser.Parser;