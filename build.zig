const std = @import("std");

pub fn build(b: *std.build.Builder) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // define static library
    const lib = b.addStaticLibrary(.{
        .name = "zre",
        .root_source_file = .{ .path = "zre.zig" },
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(lib);

    // export module definition
    _ = b.addModule("zre", .{ .source_file = .{ .path = "zre.zig" } });

    // define library tests
    const main_tests = b.addTest(.{
        .root_source_file = .{ .path = "tests.zig" },
        .target = target,
        .optimize = optimize,
    });
    const run_unit_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_unit_tests.step);
}
