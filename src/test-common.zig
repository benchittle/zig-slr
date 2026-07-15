const std = @import("std");

pub const TestWffTerminal = enum {
    const Self = @This();

    Proposition,
    Not,
    LParen,
    RParen,
    And,
    Or,
    Cond,
    Bicond,
    End,

    pub fn eql(self: Self, other: Self) bool {
        return self == other;
    }

    pub fn getString(self: Self) []const u8 {
        return switch (self) {
            .Proposition => "PROP",
            .Not => "~",
            .LParen => "(",
            .RParen => ")",
            .And => "^",
            .Or => "v",
            .Cond => "=>",
            .Bicond => "<=>",
            .End => "$",
        };
    }
};

pub const TestTerminal = struct {
    const Self = @This();

    name: []const u8,

    pub fn fromString(string: []const u8) Self {
        return Self{ .name = string };
    }

    pub fn getString(self: Self) []const u8 {
        return self.name;
    }

    pub fn eql(self: Self, other: Self) bool {
        return std.mem.eql(u8, self.name, other.name);
    }
};

pub const TestVariable = struct {
    const Self = @This();

    name: []const u8,

    pub fn fromString(string: []const u8) Self {
        return TestVariable{ .name = string };
    }

    pub fn getString(self: Self) []const u8 {
        return self.name;
    }

    pub fn eql(self: Self, other: Self) bool {
        return std.mem.eql(u8, self.name, other.name);
    }
};
