const std = @import("std");
const Allocator = std.mem.Allocator;
const Alignment = std.mem.Alignment;


pub const comptime_allocator: Allocator = .{
    .ptr = undefined,
    .vtable = &.{
        .alloc = &comptimeAlloc,
        .resize = &comptimeResize,
        .remap = &comptimeRemap,
        .free = &Allocator.noFree,
    },
};
fn comptimeAlloc(_: *anyopaque, len: usize, alignment: Alignment, _: usize) ?[*]u8 {
    if (!@inComptime()) @panic("comptimeAlloc called at runtime");
    // @compileLog("BINGUS");
    comptime {
        var buf: [len]u8 align(alignment.toByteUnits()) = undefined;
        return &buf;
    }
}
fn comptimeResize(_: *anyopaque, mem: []u8, _: Alignment, new_len: usize, _: usize) bool {
    if (!@inComptime()) @panic("comptimeResize called at runtime");
    return new_len <= mem.len; // allow shrinking in-place
}
fn comptimeRemap(_: *anyopaque, mem: []u8, _: Alignment, new_len: usize, _: usize) ?[*]u8 {
    if (!@inComptime()) @panic("comptimeRemap called at runtime");
    return if (new_len <= mem.len) mem.ptr else null; // allow shrinking in-place
}
