const std = @import("std");

const reserved_words = [_][]const u8{
    "and", "break",    "do",     "else", "elseif", "end",   "false",
    "for", "function", "if",     "in",   "local",  "nil",   "not",
    "or",  "repeat",   "return", "then", "true",   "until", "while",
};

pub const RuntimeGlobal = enum {
    bit32,
    coroutine,
    error_builtin,
    getfenv,
    getmetatable,
    next,
    pcall,
    rawget,
    rawset,
    select,
    string,
    table,
    type,
    xpcall,

    pub fn name(self: RuntimeGlobal) []const u8 {
        return switch (self) {
            .bit32 => "bit32",
            .coroutine => "coroutine",
            .error_builtin => "error",
            .getfenv => "getfenv",
            .getmetatable => "getmetatable",
            .next => "next",
            .pcall => "pcall",
            .rawget => "rawget",
            .rawset => "rawset",
            .select => "select",
            .string => "string",
            .table => "table",
            .type => "type",
            .xpcall => "xpcall",
        };
    }
};

pub const runtime_globals = [_]RuntimeGlobal{
    .bit32,
    .coroutine,
    .error_builtin,
    .getfenv,
    .getmetatable,
    .next,
    .pcall,
    .rawget,
    .rawset,
    .select,
    .string,
    .table,
    .type,
    .xpcall,
};

pub const always_reserved_runtime_globals = [_]RuntimeGlobal{
    .bit32,
    .coroutine,
    .error_builtin,
    .getfenv,
    .pcall,
    .rawget,
    .rawset,
    .string,
    .xpcall,
};

pub fn isIdentifier(name: []const u8) bool {
    if (name.len == 0 or !isIdentifierStart(name[0])) return false;
    for (name[1..]) |byte| if (!isIdentifierContinue(byte)) return false;
    for (reserved_words) |reserved| if (std.mem.eql(u8, name, reserved)) return false;
    return true;
}

fn isIdentifierStart(byte: u8) bool {
    return byte == '_' or (byte >= 'a' and byte <= 'z') or (byte >= 'A' and byte <= 'Z');
}

fn isIdentifierContinue(byte: u8) bool {
    return isIdentifierStart(byte) or (byte >= '0' and byte <= '9');
}

test "Luau source identifiers exclude punctuation, digits, and reserved words" {
    try std.testing.expect(isIdentifier("print"));
    try std.testing.expect(isIdentifier("_ENV"));
    try std.testing.expect(isIdentifier("value_42"));
    try std.testing.expect(!isIdentifier(""));
    try std.testing.expect(!isIdentifier("4value"));
    try std.testing.expect(!isIdentifier("value-name"));
    try std.testing.expect(!isIdentifier("return"));
}

test "backend runtime global spellings are unique Luau identifiers" {
    for (runtime_globals, 0..) |global, index| {
        try std.testing.expect(isIdentifier(global.name()));
        for (runtime_globals[0..index]) |prior| {
            try std.testing.expect(!std.mem.eql(u8, prior.name(), global.name()));
        }
    }
}
