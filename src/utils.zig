const std = @import("std");

pub fn Slice2d(comptime SliceType: type) type {
    comptime {
        const info = @typeInfo(SliceType);
        if (info != .pointer or info.pointer.size != .slice) {
            @compileError("Slice2d requires a slice type, got " ++ @typeName(SliceType));
        }
    }

    return struct {
        const Self = @This();

        slice: SliceType,
        row_length: usize,

        pub fn init(data: SliceType, items_per_row: usize) Self {
            return .{
                .slice = data,
                .row_length = items_per_row,
            };
        }

        pub fn row(self: Self, r: usize) SliceType {
            const start = r * self.row_length;
            const end = start + self.row_length;
            return self.slice[start..end];
        }

        pub fn lessThan(_: void, lhs: Self, rhs: Self) bool {
            return lhs.from < rhs.from;
        }
    };
}

/// Analogous to a bitwise or like `dest = dest | src` but for each boolean
/// element in the given slices
pub fn sliceUnion(dest: []bool, src: []const bool) void {
    std.debug.assert(dest.len == src.len);
    for (src, 0..) |element, i| {
        if (element) {
            dest[i] = true;
        }
    }
}

/// See `sliceUnion`
pub fn rowUnion(data: Slice2d([]bool), row_dest: usize, row_src: usize) void {
    sliceUnion(data.row(row_dest), data.row(row_src));
}
