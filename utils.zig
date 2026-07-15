
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
    };
}