const std = @import("std");

// This file contains comptime-friendly data structures and views over data.

pub fn RaggedArray(comptime T: type, comptime reverse_indexed: bool) type {
    return struct {
        const RaggedArrayType = @This();
        const IndexToRowMap = if (reverse_indexed) []const usize else void;

        pub const RaggedArrayBuilder = struct {
            const IndexToRowMapMut = if (reverse_indexed) []usize else void;

            data: []T,
            row_offsets: []usize,
            next_data_index: usize,
            next_row: usize,
            index_to_row_map: IndexToRowMapMut,

            pub fn initWithCapacity(allocator: std.mem.Allocator, size: usize, rows: usize) !RaggedArrayBuilder {
                const data = try allocator.alloc(T, size);
                errdefer allocator.free(data);
                const row_offsets = try allocator.alloc(usize, rows + 1);
                errdefer allocator.free(row_offsets);
                row_offsets[0] = 0;
                const index_to_row_map = if (reverse_indexed) try allocator.alloc(usize, size) else {};
                errdefer if (reverse_indexed) allocator.free(reverse_indexed);

                return RaggedArrayBuilder{
                    .data = data,
                    .row_offsets = row_offsets,
                    .next_data_index = 0,
                    .next_row = 1,
                    .index_to_row_map = index_to_row_map,
                };
            }

            pub fn initWithCapacityComptime(size: usize, rows: usize) RaggedArrayBuilder {
                var data: [size]T = undefined;
                var row_offsets: [rows + 1]usize = undefined;
                row_offsets[0] = 0;
                const IndexToRowMapArray = if (reverse_indexed) [size]usize else void;
                var index_to_row_map: IndexToRowMapArray = if (reverse_indexed) undefined else {};
                return RaggedArrayBuilder{
                    .data = &data,
                    .row_offsets = &row_offsets,
                    .next_data_index = 0,
                    .next_row = 1,
                    .index_to_row_map = if (reverse_indexed) &index_to_row_map else {},
                };
            }

            pub fn deinit(self: RaggedArrayBuilder, allocator: std.mem.Allocator) void {
                allocator.free(self.data);
                allocator.free(self.row_offsets);
                if (reverse_indexed) allocator.free(self.index_to_row_map);
            }

            pub fn appendAssumeCapacity(self: *RaggedArrayBuilder, item: T) void {
                std.debug.assert(self.next_data_index < self.data.len);

                self.data[self.next_data_index] = item;
                if (reverse_indexed) {
                    self.index_to_row_map[self.next_data_index] = self.next_row - 1;
                }
                self.next_data_index += 1;
            }

            pub fn startNextRowAssumeCapacity(self: *RaggedArrayBuilder) void {
                std.debug.assert(self.next_row < self.row_offsets.len);

                self.row_offsets[self.next_row] = self.next_data_index;
                self.next_row += 1;
            }

            pub fn build(self: RaggedArrayBuilder) RaggedArrayType {
                self.row_offsets[self.row_offsets.len - 1] = self.data.len;
                if (@inComptime()) {
                    // Copy comptime data into const buffers so it can exist at
                    // runtime.
                    const data = self.data[0..self.data.len].*;
                    const row_offsets = self.row_offsets[0..self.row_offsets.len].*;
                    const index_to_row_map = if (reverse_indexed) self.index_to_row_map[0..self.index_to_row_map.len].* else self.index_to_row_map;
                    return RaggedArrayType{
                        .data = &data,
                        .row_offsets = &row_offsets,
                        .index_to_row_map = if (reverse_indexed) &index_to_row_map else {},
                    };
                } else {
                    return RaggedArrayType{
                        .data = self.data,
                        .row_offsets = self.row_offsets,
                        .index_to_row_map = self.index_to_row_map,
                    };
                }
            }
        };

        data: []const T,
        row_offsets: []const usize,
        index_to_row_map: IndexToRowMap,

        pub fn deinit(self: RaggedArrayType, allocator: std.mem.Allocator) void {
            allocator.free(self.data);
            allocator.free(self.row_offsets);
            if (reverse_indexed) {
                allocator.free(self.index_to_row_map);
            }
        }

        pub fn row(self: RaggedArrayType, r: usize) []const T {
            std.debug.assert(r < self.row_offsets.len - 1);

            const row_start = self.row_offsets[r];
            const row_end = self.row_offsets[r + 1];
            return self.data[row_start..row_end];
        }

        /// Given an index, find which row that index falls in.
        /// O(1) time if reverse indexed, otherwise O(log n) (binary search).
        pub fn findRow(self: RaggedArrayType, index: usize) usize {
            std.debug.assert(index < self.data.len);

            if (reverse_indexed) {
                return self.index_to_row_map[index];
            }

            const F = struct {
                pub fn compareFn(a: usize, b: usize) std.math.Order {
                    return std.math.order(a, b);
                }
            };
            return std.sort.upperBound(usize, self.row_offsets, index, F.compareFn) - 1;
        }

        pub fn getRowCount(self: RaggedArrayType) usize {
            return self.row_offsets.len - 1;
        }
    };
}

pub fn Slice2d(comptime SliceType: type) type {
    comptime {
        const info = @typeInfo(SliceType);
        if (info != .pointer or info.pointer.size != .slice) {
            @compileError("Slice2d requires a slice type, got " ++ @typeName(SliceType));
        }
    }

    return struct {
        const Self = @This();

        const RowIterator = struct {
            slice2d: Self,
            next_row: usize,

            pub fn next(self: *RowIterator) ?SliceType {
                if (self.next_row * self.slice2d.row_length >= self.slice2d.slice.len) {
                    return null;
                }
                const current_row = self.slice2d.row(self.next_row);
                self.next_row += 1;
                return current_row;
            }

            pub fn reset(self: *RowIterator) void {
                self.next_row = 0;
            }
        };

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

        pub fn iterRows(self: Self) RowIterator {
            return RowIterator{ .slice2d = self, .next_row = 0 };
        }

        pub fn rowCount(self: Self) usize {
            return self.slice.len / self.row_length;
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
