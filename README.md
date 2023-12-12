# zre

Regular expression package for Zig targeting package installation

There are a number of stale regex implementations for Zig, none of which are compatible with v0.12 out of the box or supported by Zig packaging (a la .ZON references). Inspired by two in particular:

https://github.com/tiehuis/zig-regex

https://github.com/alexnask/ctregex.zig

## Using

Top-level exports include:

* `Encoding`

* `MatchOptions`

* `MatchResult`

* `match()`

* `search()`

For the time being, basic examples for these symbols are best drawn from `tests.zig`.
