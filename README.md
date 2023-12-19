# zre

Regular expression package for Zig targeting package installation

There are a number of stale regex implementations for Zig, none of which are compatible with v0.12.0 out of the box or supported by Zig packaging (a la .ZON references). In putting this project together I should acknowledge inspiration by two in particular:

https://github.com/tiehuis/zig-regex

https://github.com/alexnask/ctregex.zig

## Using

To install via zig-fetch, use the latest commit:

```sh
$ zig fetch --save https://github.com/Tythos/zre/archive/HEAD.tar.gz
```

Then, add it to your package's build dependencies:

```zig
    const zre = b.dependency("zre", .{ .target = target, .optimize = optimize });
    exe.addModule("zre", zre.module("zre"));
```

Lastly, you can import and call the regex behaviors from your source code:

```zig
const zre = @import("zre");
...
    try stdout.print("{any}", .{zre.match("abc", .{}, "abc")});
    try stdout.print("{any}\n", .{zre.search("a(b)c", .{}, "abcdef")});
```

## TODO

This is a very partial implementation. There are a number of features, including common shortcuts for symbol groups like digits, as well as string position references like `^` and `$`, that I would like to expand support to include. This will likely take a rewrite of the automoton, which is a little underdeveloped right now. But, this is a high priority for my Zig usage and contributions.
