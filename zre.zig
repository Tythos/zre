const std = @import("std");

/// Determines the length of a character sequence encoded in UTF-16 Little
/// Endian format, considering surrogate pairs.
///
/// This is a utility function dealing with UTF-16 encoding and is responsible
/// for identifying the length of UTF-16 encoded characters, considering
/// surrogate pairs which are used to represent characters outside the Basic
/// Multilingual Plane (BMP) in Unicode.
fn utf16leCharSequenceLength(first_char_: u16) !u2 {
    const c0: u21 = first_char_;
    if (first_char_ & ~@as(u21, 0x03ff) == 0xd800) {
        return 2;
    } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00) {
        return error.UnexpectedSecondSurrogateHalf;
    }
    return 1;
}

/// Decodes a sequence of UTF-16 Little Endian encoded characters (chars) into
/// their corresponding Unicode code point.
///
/// This function handles UTF-16 Little Endian decoding in the context of
/// processing regular expressions. It decodes individual characters or
/// surrogate pairs from UTF-16 encoding into their respective Unicode code
/// points.
fn utf16leDecode(chars: []const u16) !u21 {
    const c0: u21 = chars[0];
    if (c0 & ~@as(u21, 0x03ff) == 0xd800) {
        const c1: u21 = chars[1];
        if (c1 & ~@as(u21, 0x03ff) != 0xdc00) return error.ExpectedSecondSurrogateHalf;
        return 0x10000 + (((c0 & 0x03ff) << 10) | (c1 & 0x03ff));
    } else if (c0 & ~@as(u21, 0x03ff) == 0xdc00) {
        return error.UnexpectedSecondSurrogateHalf;
    } else {
        return c0;
    }
}

/// Performs compile-time UTF-8 encoding of a Unicode code point (codepoint)
/// into a sequence of bytes ([]const u8) representing that code point in UTF-8
/// format.
///
/// This function serves as a compile-time utility to generate UTF-8 encoded
/// sequences for specific Unicode code points. It uses compile-time evaluation
/// (comptime) to perform encoding, ensuring that the UTF-8 encoded bytes are
/// available during compilation rather than runtime.
fn ctUtf8EncodeChar(comptime codepoint: u21) []const u8 {
    var buf: [4]u8 = undefined;
    return buf[0 .. std.unicode.utf8Encode(codepoint, &buf) catch unreachable];
}

/// Implements a compile-time check for whether a given Unicode code point
/// (codepoint) is within the ASCII range.
///
/// This function serves as a safety check within the regular expression module
/// to ensure that only ASCII characters (code points 0 to 127) are used in
/// certain scenarios or modes. If a character outside the ASCII range is
/// encountered during compile-time evaluation (comptime), it raises a
/// compile-time error, indicating that the regular expression cannot match
/// non-ASCII characters in the specified mode.
fn checkAscii(comptime codepoint: u21) void {
    if (codepoint > 127) @compileError("Cannot match character '" ++ ctUtf8EncodeChar(codepoint) ++ "' in ascii mode.");
}

/// Determines the length of a character in different encodings (ASCII, UTF-8,
/// UTF-16LE, and codepoint).
///
/// This is a utility function within the regular expression module, helping to
/// ascertain the length of a character in various encodings based on the
/// provided encoding type and code point.
fn charLenInEncoding(comptime codepoint: u21, comptime encoding: Encoding) usize {
    switch (encoding) {
        .ascii => {
            checkAscii(codepoint);
            return 1;
        },
        .utf8 => return std.unicode.utf8CodepointSequenceLength(codepoint) catch unreachable,
        .utf16le => return if (codepoint < 0x10000) 1 else 2,
        .codepoint => return 1,
    }
}

/// This function is a compile-time utility that encodes a sequence of Unicode
/// code points (str) into a specified encoding (encoding).
///
/// This function serves as a compile-time encoder within the regular expression
/// module, enabling the transformation of a sequence of Unicode code points
/// into different encodings based on the specified encoding parameter.
fn ctEncode(comptime str: []const u21, comptime encoding: Encoding) []const encoding.CharT() {
    if (encoding == .codepoint) return str;

    var len: usize = 0;
    for (str) |c| len += charLenInEncoding(c, encoding);

    var result: [len]encoding.CharT() = undefined;
    var idx: usize = 0;
    for (str) |c| {
        switch (encoding) {
            .ascii => {
                result[idx] = @truncate(c);
                idx += 1;
            },
            .utf8 => idx += std.unicode.utf8Encode(c, result[idx..]) catch unreachable,
            .utf16le => {
                const utf8_c = ctUtf8EncodeChar(c);
                idx += std.unicode.utf8ToUtf16Le(result[idx..], utf8_c) catch unreachable;
            },
            .codepoint => unreachable,
        }
    }
    return &result;
}

/// This function is responsible for converting a compile-time integer value
/// (int) into a string representation ([]const u8) using compile-time
/// evaluation and formatting.
///
/// This function is a compile-time utility used within the regular expression
/// module to convert compile-time integer values into string representations.
/// It leverages the Zig formatting capabilities (std.fmt.bufPrint) to perform
/// the integer-to-string conversion during compile-time evaluation.
fn ctIntStr(comptime int: anytype) []const u8 {
    var buf: [16]u8 = undefined;
    return std.fmt.bufPrint(&buf, "{}", .{int}) catch unreachable;
}

/// Regex grammar
/// ```
/// root ::= expr?
/// expr ::= subexpr ('|' expr)?
/// subexpr ::= atom ('*' | '+' | '?' | ('{' digit+ (',' (digit+)?)? '}'))? subexpr?
/// atom ::= grouped | brackets | '.' | char_class | '\' special | '\' | rest_char
/// grouped ::= '(' ('?' (':' | ('<' ascii_ident '>'))? expr ')'
/// brackets ::= '[' '^'? (brackets_rule)+ ']'
/// brackets_rule ::= brackets_atom | brackets_atom '-' brackets_atom
/// brackets_atom ::= ('\' special_brackets | '\' | rest_brackets)+
/// special_brackets ::= '-' | ']' | '^'
/// rest_brackets ::=  <char>-special_brackets
/// special ::= '.' | '[' | ']'| '(' | ')' | '|' | '*' | '+' | '?' | '^' | '{' | '}'
/// rest_char ::= <char>-special
/// char_class ::= '\d' | '\s'
/// ```
const RegexParser = struct {
    iterator: std.unicode.Utf8Iterator,
    captures: []const *const Grouped = &[0]*const Grouped{},
    curr_capture: usize = 0,

    /// The init method is used to initialize a RegexParser instance with an
    /// input source string (source) containing UTF-8 encoded characters.
    ///
    /// This init method serves as a constructor for the RegexParser struct,
    /// allowing the creation of a RegexParser instance with an initialized
    /// UTF-8 iterator based on the provided source string. This initialized
    /// parser can then be used for parsing and processing regular expressions.
    fn init(comptime source: []const u8) RegexParser {
        const view = comptime std.unicode.Utf8View.initComptime(source);
        return .{
            .iterator = comptime view.iterator(),
        };
    }

    /// The parse method serves as an interface function that parses the
    /// provided input source string (source) using the RegexParser instance.
    ///
    /// This parse method encapsulates the process of parsing a given input
    /// source string using the RegexParser struct by initializing the parser
    /// and initiating the parsing operation. It acts as a convenient entry
    /// point to kickstart the parsing process for regular expressions based on
    /// the provided input source.
    fn parse(comptime source: []const u8) ?ParseResult {
        var parser = RegexParser.init(source);
        return parser.parseRoot();
    }

    /// The skipWhitespace method is designed to advance the parser's iterator
    /// past any whitespace characters (space or tab) in the input stream.
    ///
    /// Overall, this method assists in advancing the parser's iterator past
    /// any whitespace characters encountered in the input stream to ensure
    /// parsing continues from the first non-whitespace character.
    fn skipWhitespace(comptime parser: *RegexParser) void {
        while (parser.iterator.i < parser.iterator.bytes.len and
            (parser.iterator.bytes[parser.iterator.i] == ' ' or
            parser.iterator.bytes[parser.iterator.i] == '\t')) : (parser.iterator.i += 1)
        {}
    }

    /// The peek method aims to provide a preview or "peek" at the next Unicode
    /// code point in the input stream without consuming it, using the parser's
    /// iterator.
    ///
    /// This allows the parser to examine the next Unicode code point in the
    /// input stream without advancing the iterator, providing a way to inspect
    /// upcoming characters without consuming them (e.g., `lookahead`).
    fn peek(comptime parser: *RegexParser) ?u21 {
        if (parser.atEnd()) return null;

        const curr_i = parser.iterator.i;
        const next = parser.iterator.nextCodepoint() orelse @compileError("Incomplete codepoint at the end of the regex string");
        parser.iterator.i = curr_i;
        return next;
    }

    /// The peekOneOf method is designed to peek at the next Unicode code point
    /// in the input stream and check if it matches any of the specified
    /// characters provided in the chars parameter.
    ///
    /// This enables the parser to peek at the next Unicode code point in the
    /// input stream and check if it matches any of the specified characters
    /// provided in the chars collection without consuming the code point,
    /// offering a way to selectively identify certain expected characters in
    /// the input stream.
    fn peekOneOf(comptime parser: *RegexParser, chars: anytype) ?u21 {
        const c = parser.peek() orelse return null;
        for (chars) |candidate| {
            if (c == candidate) return c;
        }
        return null;
    }

    /// The atEnd method is a utility function used to determine whether the
    /// parser's iterator has reached the end of the input stream.
    ///
    /// This method serves as a check within the RegexParser struct to
    /// ascertain whether the parser has consumed all characters in the input
    /// stream. It's useful for controlling loops or termination conditions
    /// during parsing to prevent attempts to parse beyond the available input
    /// characters.
    fn atEnd(comptime parser: RegexParser) bool {
        return parser.iterator.i >= parser.iterator.bytes.len;
    }

    /// The consumeNotOneOf method aims to consume and return the next Unicode
    /// code point from the input stream if it does not match any of the
    /// specified characters provided in the chars collection.
    ///
    /// This allows the parser to consume the next Unicode code point from the
    /// input stream if it doesn’t match any of the specified characters
    /// provided in the chars collection, allowing selective consumption based
    /// on character exclusion.
    fn consumeNotOneOf(comptime parser: *RegexParser, chars: anytype) ?u21 {
        const c = parser.peek() orelse return null;
        for (chars) |candidate| {
            if (c == candidate) return null;
        }
        return parser.iterator.nextCodepoint().?;
    }

    /// The consumeOneOf method aims to consume and return the next Unicode
    /// code point from the input stream if it matches any of the specified
    /// characters provided in the chars collection.
    ///
    /// This allows the parser to consume the next Unicode code point from the
    /// input stream if it matches any of the specified characters provided in
    /// the chars collection, facilitating selective consumption based on
    /// character inclusion.
    fn consumeOneOf(comptime parser: *RegexParser, chars: anytype) ?u21 {
        const c = parser.peek() orelse return null;
        for (chars) |candidate| {
            if (c == candidate) {
                return parser.iterator.nextCodepoint().?;
            }
        }
        return null;
    }

    /// The consumeChar method aims to consume the next Unicode code point from
    /// the input stream if it matches the specified Unicode character (char).
    ///
    /// This allows the parser to attempt to consume the next Unicode code
    /// point from the input stream if it matches the specified Unicode
    /// character, providing a mechanism for character-based consumption and
    /// validation during parsing operations.
    fn consumeChar(comptime parser: *RegexParser, char: u21) bool {
        const c = parser.peek() orelse return false;
        if (c == char) {
            _ = parser.iterator.nextCodepoint().?;
            return true;
        }
        return false;
    }

    /// The raiseError method within the RegexParser struct is a comprehensive
    /// error reporting mechanism used to generate detailed error messages when
    /// an issue is encountered during parsing.
    ///
    /// In essence, this method assists in generating highly informative and
    /// detailed compile-time error messages with context, aiding developers in
    /// understanding and addressing issues encountered during regular
    /// expression parsing within Zig.
    fn raiseError(comptime parser: *RegexParser, comptime fmt: []const u8, args: anytype) void {
        var start_idx: usize = 0;
        while (parser.iterator.i - start_idx >= 40) {
            start_idx += std.unicode.utf8ByteSequenceLength(parser.iterator.bytes[start_idx]) catch unreachable;
        }
        var start_spaces: usize = 0;
        {
            var idx: usize = start_idx;
            while (idx < parser.iterator.i) {
                const n = std.unicode.utf8ByteSequenceLength(parser.iterator.bytes[idx]) catch unreachable;
                idx += n;
                if (n > 1) {
                    start_spaces += 2;
                } else {
                    start_spaces += 1;
                }
            }
        }
        var end_idx: usize = parser.iterator.i;
        while (end_idx - parser.iterator.i <= 40 and end_idx < parser.iterator.bytes.len) {
            end_idx += std.unicode.utf8ByteSequenceLength(parser.iterator.bytes[end_idx]) catch unreachable;
        }

        const line_prefix = if (start_idx == 0) "\n" else "\n[...] ";
        const line_suffix = if (end_idx == parser.iterator.bytes.len) "\n" else " [...]\n";

        var error_buf1: [128]u8 = undefined;
        var error_buf2: [128]u8 = undefined;
        const error_slice1 = std.fmt.bufPrint(&error_buf1, "error: {}: ", .{parser.iterator.i - 1}) catch unreachable;
        const error_slice2 = std.fmt.bufPrint(&error_buf2, fmt, args) catch unreachable;
        @compileError("\n" ++ error_slice1 ++ error_slice2 ++ line_prefix ++ parser.iterator.bytes[start_idx..end_idx] ++ line_suffix ++ " " ** (start_spaces + line_prefix.len - 2) ++ "^");
    }

    /// Encapsulates a partial parse endstate from a root expression by
    /// aggregating a set of capture groups.
    const ParseResult = struct {
        root: Expr,
        captures: []const *const Grouped,
    };

    // Implements `root ::= expr?`
    fn parseRoot(comptime parser: *RegexParser) ?ParseResult {
        comptime {
            if (parser.parseExpr()) |expr| {
                if (!parser.atEnd())
                    parser.raiseError("Invalid regex, stopped parsing here", .{});
                return ParseResult{ .root = expr, .captures = parser.captures };
            }
            return null;
        }
    }

    // Implements `expr ::= subexpr ('|' expr)?`
    fn parseExpr(comptime parser: *RegexParser) ?Expr {
        const sub_expr = parser.parseSubExpr() orelse return null;
        parser.skipWhitespace();

        if (parser.consumeChar('|')) {
            const rhs = parser.parseExpr() orelse parser.raiseError("Expected expression after '|'", .{});
            return Expr{ .lhs = sub_expr, .rhs = &rhs };
        }

        return Expr{ .lhs = sub_expr, .rhs = null };
    }

    /// Modifiers extend the meaning of the top-most sequence
    const modifiers = .{ '*', '+', '?' };

    /// Special characters are non-literal matches and delimiters, including modifiers
    const special_chars = .{ '.', '[', ']', '(', ')', '|', '*', '+', '?', '^', '{', '}' };

    // Implements `subexpr ::= atom ('*' | '+' | '?' | ('{' digit+ (',' (digit+)?)? '}'))? subexpr?`
    fn parseSubExpr(comptime parser: *RegexParser) ?SubExpr {
        const atom = parser.parseAtom() orelse return null;
        parser.skipWhitespace();

        var lhs = SubExpr{ .atom = .{ .data = atom } };
        if (parser.consumeOneOf(modifiers)) |mod| {
            lhs.atom.mod = .{ .char = mod };
            parser.skipWhitespace();
        } else if (parser.consumeChar('{')) {
            parser.skipWhitespace();
            const min_reps = parser.parseNaturalNum();
            parser.skipWhitespace();
            if (parser.consumeChar(',')) {
                parser.skipWhitespace();
                const max_reps = if (parser.maybeParseNaturalNum()) |reps| block: {
                    if (reps <= min_reps)
                        parser.raiseError("Expected repetition upper bound to be greater or equal to {}", .{min_reps});
                    break :block reps;
                } else 0;
                lhs.atom.mod = .{
                    .repetitions_range = .{
                        .min = min_reps,
                        .max = max_reps,
                    },
                };
            } else {
                if (min_reps == 0) parser.raiseError("Exactly zero repetitions requested...", .{});

                lhs.atom.mod = .{
                    .exact_repetitions = min_reps,
                };
            }
            parser.skipWhitespace();
            if (!parser.consumeChar('}'))
                parser.raiseError("Expected closing '}' after repetition modifier", .{});
        }

        if (parser.parseSubExpr()) |rhs| {
            const old_lhs = lhs;
            return SubExpr{ .concat = .{ .lhs = &old_lhs, .rhs = &rhs } };
        }
        return lhs;
    }

    // Implements `atom ::= grouped | brackets | '.' | char_class | '\' special | '\' | rest_char`
    fn parseAtom(comptime parser: *RegexParser) ?Atom {
        parser.skipWhitespace();

        if (parser.parseGrouped()) |grouped| {
            return Atom{ .grouped = grouped };
        }

        if (parser.parseBrackets()) |brackets| {
            return Atom{ .brackets = brackets };
        }

        if (parser.consumeChar('.')) {
            return Atom.any;
        }

        var str: []const u21 = &[0]u21{};
        // char_class | ('\' special | '\\' | rest_char)+
        if (parser.consumeChar('\\')) block: {
            // char_class := '\d' | '\s'
            if (parser.consumeOneOf(char_classes)) |class| {
                return Atom{ .char_class = class };
            }

            // special := '.' | '[' | ']'| '(' | ')' | '|' | '*' | '+' | '?' | '^' | '{' | '}'
            if (parser.consumeOneOf(special_chars ++ .{ ' ', '\t', '\\' })) |c| {
                str = str ++ &[1]u21{c};
                break :block;
            }
            parser.raiseError("Invalid character '{?}' after escape \\", .{parser.peek()});
        }

        charLoop: while (true) {
            parser.skipWhitespace();
            if (parser.consumeChar('\\')) {
                if (parser.consumeOneOf(special_chars ++ .{ ' ', '\t', '\\' })) |c| {
                    str = str ++ &[1]u21{c};
                    continue :charLoop;
                }
                if (parser.peekOneOf(char_classes) != null) {
                    // We know the backslash is 1 byte long
                    // So we can safely do this
                    parser.iterator.i -= 1;
                    break :charLoop;
                }
                parser.raiseError("Invalid character '{}' after escape \\", .{parser.peek()});
            } else if (parser.peekOneOf(modifiers ++ .{'{'}) != null) {
                if (str.len == 1) return Atom{ .literal = str };
                if (str.len == 0) parser.raiseError("Stray modifier character '{u}' applies to no expression", .{parser.peek()});
                parser.iterator.i -= std.unicode.utf8CodepointSequenceLength(str[str.len - 1]) catch unreachable;
                return Atom{ .literal = str[0 .. str.len - 1] };
            }
            // rest_char := <char>-special
            str = str ++ &[1]u21{parser.consumeNotOneOf(special_chars) orelse break :charLoop};
        }
        if (str.len == 0) return null;
        return Atom{ .literal = str };
    }

    /// The parseAsciiIdent method is responsible for parsing ASCII identifiers
    /// from the input stream and returning them as a []const u8.
    ///
    /// This method essentially reads and validates ASCII identifiers from the
    /// input stream, ensuring they start with either an underscore or an ASCII
    /// alphabetic character and consist of subsequent underscores or
    /// alphanumeric ASCII characters. If any violations occur, it raises
    /// specific errors to provide detailed feedback during the parsing
    /// process.
    fn parseAsciiIdent(comptime parser: *RegexParser) []const u8 {
        var c = parser.peek() orelse parser.raiseError("Expected ascii identifier", .{});
        if (c > 127) parser.raiseError("Expected ascii character in identifier, got '{}'", .{c});
        if (c != '_' and !std.ascii.isAlpha(@as(u8, @truncate(c)))) {
            parser.raiseError("Identifier must start with '_' or a letter, got '{}''", .{c});
        }
        var res: []const u8 = &[1]u8{@as(u8, @truncate(parser.iterator.nextCodepoint() orelse unreachable))};
        readChars: while (true) {
            c = parser.peek() orelse break :readChars;
            if (c > 127 or (c != '_' and !std.ascii.isAlNum(@as(u8, @truncate(c)))))
                break :readChars;
            res = res ++ &[1]u8{@as(u8, @truncate(parser.iterator.nextCodepoint() orelse unreachable))};
        }
        return res;
    }

    /// The parseNaturalNum method is designed to parse and return a natural
    /// number (non-negative integer) from the input stream.
    ///
    /// Essentially, this method serves as a higher-level interface for parsing
    /// a natural number from the input stream. It delegates the actual parsing
    /// logic to another method (maybeParseNaturalNum()) and handles potential
    /// errors by raising a descriptive error message if parsing fails.
    fn parseNaturalNum(comptime parser: *RegexParser) usize {
        return parser.maybeParseNaturalNum() orelse parser.raiseError("Expected natural number", .{});
    }

    /// The maybeParseNaturalNum method aims to parse and return a natural
    /// number (non-negative integer) from the input stream, or return null if
    /// a natural number cannot be parsed.
    ///
    /// This method attempts to parse a natural number from the input stream
    /// and returns the parsed number if successful, or null if it encounters a
    /// non-digit character or reaches the end of the input stream before
    /// parsing a complete natural number.
    fn maybeParseNaturalNum(comptime parser: *RegexParser) ?usize {
        var c = parser.peek() orelse return null;
        if (c > 127 or !std.ascii.isDigit(@as(u8, @truncate(c)))) return null;
        var res: usize = (parser.iterator.nextCodepoint() orelse unreachable) - '0';
        readChars: while (true) {
            c = parser.peek() orelse break :readChars;
            if (c > 127 or !std.ascii.isDigit(@as(u8, @truncate(c)))) break :readChars;
            res = res * 10 + ((parser.iterator.nextCodepoint() orelse unreachable) - '0');
        }
        return res;
    }

    // Implements `grouped := '(' expr ')'`
    fn parseGrouped(comptime parser: *RegexParser) ?Grouped {
        if (!parser.consumeChar('(')) return null;
        parser.skipWhitespace();

        var grouped_expr = Grouped{ .capture_info = .{ .idx = parser.curr_capture, .name = null }, .expr = undefined };

        if (parser.consumeChar('?')) {
            parser.skipWhitespace();
            if (parser.consumeChar(':')) {
                grouped_expr.capture_info = null;
            } else if (parser.consumeChar('<')) {
                // TODO Support unicode names?
                // TODO Check for name redefinition
                grouped_expr.capture_info.?.name = parser.parseAsciiIdent();
                if (!parser.consumeChar('>')) parser.raiseError("Expected > after grouped expression name", .{});
            } else {
                parser.raiseError("Expected : or < after ? at the start of a grouped expression.", .{});
            }
        }

        const expr = parser.parseExpr() orelse parser.raiseError("Expected expression after '('", .{});
        parser.skipWhitespace();
        if (!parser.consumeChar(')')) parser.raiseError("Expected ')' after expression", .{});
        grouped_expr.expr = &expr;

        if (grouped_expr.capture_info != null) {
            parser.captures = parser.captures ++ &[1]*const Grouped{&grouped_expr};
            parser.curr_capture += 1;
        }

        return grouped_expr;
    }

    // Implements `brackets ::= '[' '^'? (brackets_rule)+ ']'`
    fn parseBrackets(comptime parser: *RegexParser) ?Brackets {
        if (!parser.consumeChar('[')) return null;
        parser.skipWhitespace();

        const is_exclusive = parser.consumeChar('^');
        if (is_exclusive) parser.skipWhitespace();

        var brackets = Brackets{
            .rules = &[1]Brackets.Rule{
                parser.parseBracketsRule() orelse parser.raiseError("Expected at least one bracket rule", .{}),
            },
            .is_exclusive = is_exclusive,
        };

        while (parser.parseBracketsRule()) |rule| {
            brackets.rules = brackets.rules ++ &[1]Brackets.Rule{rule};
            parser.skipWhitespace();
        }
        if (!parser.consumeChar(']')) parser.raiseError("Missing matching closing bracket", .{});

        return brackets;
    }

    /// Implements a combination of bracket parsing rules:
    // `brackets_rule ::= brackets_atom | brackets_atom '-' brackets_atom`
    // `brackets_atom := '\' special_brackets | '\\' | rest_brackets`
    // `special_brackets := '-' | ']'`
    // `rest_brackets :=  <char>-special_brackets`
    fn parseBracketsRule(comptime parser: *RegexParser) ?Brackets.Rule {
        const special_brackets = .{ '-', ']', '^' };

        const first_char = if (parser.consumeChar('\\')) block: {
            if (parser.consumeOneOf(special_brackets ++ .{ ' ', '\t', '\\' })) |char| {
                break :block char;
            } else if (parser.consumeOneOf(char_classes)) |char| {
                return Brackets.Rule{ .char_class = char };
            }
            parser.raiseError("Invalid character '{}' after escape \\", .{parser.peek()});
        } else parser.consumeNotOneOf(special_brackets) orelse return null;

        parser.skipWhitespace();
        if (parser.consumeChar('-')) {
            parser.skipWhitespace();
            const second_char = if (parser.consumeChar('\\')) block: {
                if (parser.consumeOneOf(special_brackets ++ .{ ' ', '\t', '\\' })) |char| {
                    break :block char;
                }
                parser.raiseError("Invalid character '{}' after escape \\", .{parser.peek()});
            } else parser.consumeNotOneOf(special_brackets) orelse parser.raiseError("Expected a valid character after - in bracket rule, got character '{}'", .{parser.peek()});

            if (first_char >= second_char) {
                parser.raiseError("Invalid range '{}-{}', start should be smaller than end", .{ first_char, second_char });
            }
            // TODO Check if the char is already in some other rule and error?
            return Brackets.Rule{ .range = .{ .start = first_char, .end = second_char } };
        }
        return Brackets.Rule{ .char = first_char };
    }

    /// Defines an enum union for modeling a "subexpression" within the regexp,
    /// which consists of either an atomic elements or a concatenation of
    /// subexpressions.
    const SubExpr = union(enum) {
        atom: struct {
            data: Atom,
            mod: union(enum) {
                char: u8,
                exact_repetitions: usize,
                repetitions_range: struct {
                    min: usize,
                    /// Zero for max means unbounded
                    max: usize,
                },
                none,
            } = .none,
        },
        concat: struct {
            lhs: *const SubExpr,
            rhs: *const SubExpr,
        },

        /// The `ctStr` method aims to generate a compile-time string
        /// representation of the given SubExpr instance.
        ///
        /// In summary, this function traverses the SubExpr instance, generates
        /// string representations for atoms considering modifiers, and
        /// concatenates string representations of concatenated expressions,
        /// ultimately providing a representation of the entire expression as a
        /// compile-time string.
        fn ctStr(comptime self: SubExpr) []const u8 {
            switch (self) {
                .atom => |atom| {
                    const atom_str = atom.data.ctStr();
                    switch (atom.mod) {
                        .none => {},
                        .exact_repetitions => |reps| return atom_str ++ "{" ++ ctIntStr(reps) ++ "}",
                        .repetitions_range => |range| return atom_str ++ "{" ++ ctIntStr(range.min) ++ if (range.max == 0)
                            ",<inf>}"
                        else
                            (", " ++ ctIntStr(range.max) ++ "}"),
                        .char => |c| return atom_str ++ &[1]u8{c},
                    }
                    return atom_str;
                },
                .concat => |concat| {
                    return concat.lhs.ctStr() ++ " " ++ concat.rhs.ctStr();
                },
            }
            return "";
        }

        /// The minLen method calculates the minimum length of a given regular
        /// expression pattern.
        ///
        /// This method recursively calculates the minimum length of the
        /// regular expression pattern represented by the provided SubExpr
        /// instance, considering different modifiers and concatenations within
        /// the pattern, and returns the minimum length based on the provided
        /// encoding rules.
        fn minLen(comptime self: SubExpr, comptime encoding: Encoding) usize {
            switch (self) {
                .atom => |atom| {
                    const atom_min_len = atom.data.minLen(encoding);
                    switch (atom.mod) {
                        .char => |c| if (c == '*' or c == '?') return 0,
                        .exact_repetitions => |reps| return reps * atom_min_len,
                        .repetitions_range => |range| return range.min * atom_min_len,
                        .none => {},
                    }
                    return atom_min_len;
                },
                .concat => |concat| return concat.lhs.minLen(encoding) + concat.rhs.minLen(encoding),
            }
        }
    };

    /// Define key "shortcuts" for supported character classes
    const char_classes = .{ 'd', 's' };

    /// Maps a specific character class representation to its "expanded"
    /// (legible) representation.
    fn charClassToString(class: u21) []const u8 {
        return switch (class) {
            'd' => "<digit>",
            's' => "<whitespace>",
            else => unreachable,
        };
    }

    /// The charClassMinLen method provides a minimal length calculation for
    /// character classes based on the specified encoding.
    fn charClassMinLen(comptime class: u21, comptime encoding: Encoding) usize {
        _ = class;
        _ = encoding;
        return 1;
    }

    /// A "full" expression consists of a subexpression and another (optional)
    /// expression.
    const Expr = struct {
        lhs: SubExpr,
        rhs: ?*const Expr,

        /// Full expressions can be evaluated for expanded strict
        /// representations (set union of languages, e.g. `|`).
        fn ctStr(comptime self: Expr) []const u8 {
            var str: []const u8 = self.lhs.ctStr();
            if (self.rhs) |rhs| {
                str = str ++ " | " ++ rhs.ctStr();
            }
            return str;
        }

        /// Computing minimum length of a "full" expression is a recursive
        /// operation, which should not be surprising.
        fn minLen(comptime self: Expr, comptime encoding: Encoding) usize {
            const lhs_len = self.lhs.minLen(encoding);
            if (self.rhs) |rhs| {
                const rhs_len = rhs.minLen(encoding);
                return @min(lhs_len, rhs_len);
            }
            return lhs_len;
        }
    };

    /// An "atomic" element within an expression can be one of several
    /// candidates.
    const Atom = union(enum) {
        grouped: Grouped,
        brackets: Brackets,
        any,
        char_class: u21,
        literal: []const u21,

        /// Generates a legible string representation of the atomic.
        fn ctStr(comptime self: Atom) []const u8 {
            return switch (self) {
                .grouped => |grouped| grouped.ctStr(),
                .brackets => |bracks| bracks.ctStr(),
                .any => "<any_char>",
                .char_class => |class| charClassToString(class),
                .literal => |codepoint_str| block: {
                    var str: []const u8 = "literal<";
                    for (codepoint_str) |codepoint| {
                        str = str ++ ctUtf8EncodeChar(codepoint);
                    }
                    break :block str ++ ">";
                },
            };
        }

        /// Determines the minmum length of the atomic based on several
        /// branching possibilities and potential encodings.
        fn minLen(comptime self: Atom, comptime encoding: Encoding) usize {
            return switch (self) {
                .grouped => |grouped| grouped.minLen(encoding),
                .brackets => |brackets| brackets.minLen(encoding),
                .any => 1,
                .char_class => |class| charClassMinLen(class, encoding),
                .literal => |codepoint_str| block: {
                    var len: usize = 0;
                    for (codepoint_str) |cp| {
                        len += charLenInEncoding(cp, encoding);
                    }
                    break :block len;
                },
            };
        }
    };

    /// A "grouped" element within a regular expression consists of an
    /// expression and relevant capture information.
    const Grouped = struct {
        expr: *const Expr,
        capture_info: ?struct {
            idx: usize,
            name: ?[]const u8,
        },

        /// Generates a human-legible string representation of the capture
        /// group.
        fn ctStr(comptime self: Grouped) []const u8 {
            const str = "(" ++ self.expr.ctStr() ++ ")";
            if (self.capture_info) |info| {
                return "capture<" ++ (if (info.name) |n| n ++ ", " else "") ++ str ++ ">";
            }
            return str;
        }

        /// The minimum length of the capture group is effectively determined
        /// by the encoding of the relevant expression.
        fn minLen(comptime self: Grouped, comptime encoding: Encoding) usize {
            return self.expr.minLen(encoding);
        }
    };

    /// A bracketed element within a regular expression consits of a set of
    /// rules that are or are not exclusive.
    const Brackets = struct {
        is_exclusive: bool,
        rules: []const Rule,

        /// A rule in the context of a bracketed element can consist of a
        /// character, a range, or a character class.
        const Rule = union(enum) {
            char: u21,
            range: struct {
                start: u21,
                end: u21,
            },
            char_class: u21,
        };

        /// Generates a human-legible string representation of a bracketed
        /// element in a regular expression.
        fn ctStr(comptime self: Brackets) []const u8 {
            var str: []const u8 = "[";
            if (self.is_exclusive) str = str ++ "<not> ";
            for (self.rules, 0..) |rule, idx| {
                if (idx > 0) str = str ++ " ";
                str = str ++ switch (rule) {
                    .char => |c| ctUtf8EncodeChar(c),
                    .range => |r| ctUtf8EncodeChar(r.start) ++ "-" ++ ctUtf8EncodeChar(r.end),
                    .char_class => |class| charClassToString(class),
                };
            }

            return str ++ "]";
        }

        /// The minimum length of a bracketed group depends on the size and
        /// type of the rule.
        fn minLen(comptime self: Brackets, comptime encoding: Encoding) usize {
            if (self.is_exclusive) return 1;
            var min_len: usize = std.math.maxInt(usize);
            for (self.rules) |rule| {
                const curr_len: usize = switch (rule) {
                    .char => |c| charLenInEncoding(c, encoding),
                    .range => |range| charLenInEncoding(range.start, encoding),
                    .char_class => |class| charClassMinLen(class, encoding),
                };
                if (curr_len < min_len) min_len = curr_len;
                if (min_len == 1) return 1;
            }
            return min_len;
        }
    };
};

/// Defines several possible string encodings
pub const Encoding = enum {
    ascii,
    utf8,
    utf16le,
    codepoint,

    /// The potential size of a given character changes depending on the
    /// encoding.
    pub fn CharT(comptime self: Encoding) type {
        return switch (self) {
            .ascii, .utf8 => u8,
            .utf16le => u16,
            .codepoint => u21,
        };
    }
};

/// Examines the specified MatchOptions and encoding type within a switch
/// statement to extract a single character from the given string. For ASCII
/// and codepoint encodings, it returns a slice representing the first
/// character, considering 1 byte for ASCII or 1 codepoint for Unicode. In the
/// case of UTF-8 encoding, it retrieves a slice covering the entire UTF-8
/// character sequence by determining the byte length of the character based on
/// the initial byte. Similarly, for UTF-16LE encoding, it returns a slice
/// encompassing the complete UTF-16LE character sequence, calculated using the
/// utf16leCharSequenceLength function to determine the sequence length based
/// on the first byte in the sequence.
inline fn readOneChar(comptime options: MatchOptions, str: []const options.encoding.CharT()) !@TypeOf(str) {
    switch (options.encoding) {
        .ascii, .codepoint => return str[0..1],
        .utf8 => return str[0..try std.unicode.utf8ByteSequenceLength(str[0])],
        .utf16le => return str[0..try utf16leCharSequenceLength(str[0])],
    }
}

/// Validates whether a given Unicode code point (cp) belongs to a specific
/// character class denoted by a 21-bit integer (class). It utilizes a switch
/// statement based on class, handling cases for digit ('d') and whitespace
/// ('s') classes. For digits, it checks if cp falls between '0' and '9',
/// returning true if so. Regarding whitespaces ('s'), it currently includes
/// space and tab characters, aiming to align with PCRE definitions. If class
/// isn't 'd' or 's', the function reaches an else clause marked unreachable,
/// signifying an unexpected case.
inline fn inCharClass(comptime class: u21, cp: u21) bool {
    switch (class) {
        'd' => return cp >= '0' and cp <= '9',
        's' => {
            // TODO Include same chars as PCRE
            return cp == ' ' or cp == '\t';
        },
        else => unreachable,
    }
}

/// Extracts characters from a specified class within a string, considering a
/// 21-bit integer class, MatchOptions for encoding, and the input string str.
/// It uses nested switch statements to handle 'd' (digits) and 's'
/// (whitespace) classes. For digits ('d'), it employs different checks based
/// on ASCII/UTF-8 or codepoint/UTF-16LE encodings to return slices containing
/// the matched character or null. For whitespace ('s'), it identifies space
/// and tab characters, returning slices if the character matches or null
/// otherwise. If class doesn't match 'd' or 's', it hits an else clause marked
/// unreachable, signaling an unexpected scenario.
inline fn readCharClass(comptime class: u21, comptime options: MatchOptions, str: []const options.encoding.CharT()) ?@TypeOf(str) {
    switch (class) {
        'd' => {
            switch (options.encoding) {
                .ascii, .utf8 => return if (std.ascii.isDigit(str[0])) str[0..1] else null,
                .codepoint, .utf16le => return if (str[0] >= '0' and str[0] <= '9') str[0..1] else null,
            }
        },
        's' => {
            // TODO Include same chars as PCRE
            return if (str[0] == ' ' or str[0] == '\t') str[0..1] else null;
        },
        else => unreachable,
    }
}

/// The heart of the engine. Handles grouped, any, character class, literal,
/// and brackets atoms. It considers MatchOptions, input string str, and a
/// result placeholder. After ensuring the string length meets the minimum
/// required, it branches into handling specific atom types. For grouped atoms,
/// it triggers another matching function while managing capture group
/// information. For literals, it checks encodings for matches. With brackets,
/// it decodes characters based on encoding and evaluates against specified
/// rules (character, range, or character class) to determine matches or
/// exclusions within the string. Finally, it returns matched portions as
/// slices or null based on specified conditions.
inline fn matchAtom(comptime atom: RegexParser.Atom, comptime options: MatchOptions, str: []const options.encoding.CharT(), result: anytype) !?@TypeOf(str) {
    const min_len = comptime atom.minLen(options.encoding);
    if (str.len < min_len) return null;

    switch (atom) {
        .grouped => |grouped| {
            const ret = (try matchExpr(grouped.expr.*, options, str, result)) orelse return null;
            if (grouped.capture_info) |info| {
                result.captures[info.idx] = ret;
            }
            return ret;
        },
        .any => return try readOneChar(options, str),
        .char_class => |class| return readCharClass(class, options, str),
        .literal => |lit| {
            const encoded_lit = comptime ctEncode(lit, options.encoding);
            if (std.mem.eql(options.encoding.CharT(), encoded_lit, str[0..encoded_lit.len])) {
                return str[0..encoded_lit.len];
            }
            return null;
        },
        .brackets => |brackets| {
            var this_slice: @TypeOf(str) = undefined;

            const this_cp: u21 = switch (options.encoding) {
                .codepoint, .ascii => block: {
                    this_slice = str[0..1];
                    break :block str[0];
                },
                .utf8 => block: {
                    this_slice = str[0..try std.unicode.utf8ByteSequenceLength(str[0])];
                    break :block try std.unicode.utf8Decode(this_slice);
                },
                .utf16le => block: {
                    this_slice = str[0..try utf16leCharSequenceLength(str[0])];
                    break :block try utf16leDecode(this_slice);
                },
            };

            inline for (brackets.rules) |rule| {
                switch (rule) {
                    .char => |c| {
                        if (c == this_cp)
                            return if (brackets.is_exclusive) null else this_slice;
                    },
                    .range => |range| {
                        if (options.encoding == .ascii) {
                            checkAscii(range.start);
                            checkAscii(range.end);
                        }

                        if (this_cp >= range.start and this_cp <= range.end)
                            return if (brackets.is_exclusive) null else this_slice;
                    },
                    .char_class => |class| if (inCharClass(class, this_cp))
                        return if (brackets.is_exclusive) null else this_slice,
                }
            }
            return if (brackets.is_exclusive) try readOneChar(options, str) else null;
        },
    }
}

/// Handles regex subexpressions, parsing atoms with different modifiers (none,
/// char, exact repetitions, repetitions range) and concatenations. It
/// considers MatchOptions, the input string str, and a result placeholder.
/// After ensuring the string length meets the minimum requirement, it
/// evaluates specific subexpression types. For atoms, it manages modifiers by
/// matching characters iteratively, forming slices based on the specified
/// conditions. For concatenations, it recursively matches the left and right
/// sides of the expression, combining matched slices accordingly. The function
/// returns slices representing matched portions or null based on the defined
/// conditions within the regex subexpression.
inline fn matchSubExpr(comptime sub_expr: RegexParser.SubExpr, comptime options: MatchOptions, str: []const options.encoding.CharT(), result: anytype) !?@TypeOf(str) {
    const min_len = comptime sub_expr.minLen(options.encoding);
    if (str.len < min_len) return null;

    switch (sub_expr) {
        .atom => |atom| {
            switch (atom.mod) {
                .none => return try matchAtom(atom.data, options, str, result),
                .char => |c| switch (c) {
                    // TODO Abstract this somehow?
                    '*' => {
                        if (try matchAtom(atom.data, options, str, result)) |ret_slice| {
                            var curr_slice: @TypeOf(str) = str[0..ret_slice.len];
                            while (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                                curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                            }
                            return curr_slice;
                        } else {
                            return str[0..0];
                        }
                    },
                    '+' => {
                        const ret_slice = (try matchAtom(atom.data, options, str, result)) orelse return null;
                        var curr_slice: @TypeOf(str) = str[0..ret_slice.len];
                        while (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                            curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                        }
                        return curr_slice;
                    },
                    '?' => {
                        return (try matchAtom(atom.data, options, str, result)) orelse str[0..0];
                    },
                    else => unreachable,
                },
                .exact_repetitions => |reps| {
                    var curr_slice: @TypeOf(str) = str[0..0];
                    // TODO Using an inline while here crashes the compiler in codegen
                    var curr_rep: usize = reps;
                    while (curr_rep > 0) : (curr_rep -= 1) {
                        if (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                            curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                        } else return null;
                    }
                    return curr_slice;
                },
                .repetitions_range => |range| {
                    var curr_slice: @TypeOf(str) = str[0..0];
                    // Do minimum reps
                    // TODO Using an inline while here crashes the compiler in codegen
                    var curr_rep: usize = 0;
                    while (curr_rep < range.min) : (curr_rep += 1) {
                        if (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                            curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                        } else return null;
                    }

                    // 0 maximum reps means keep going on forever
                    if (range.max == 0) {
                        while (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                            curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                        }
                    } else {
                        // TODO Using an inline while here crashes the compiler in codegen
                        const curr_additional_rep: usize = 0;
                        _ = curr_additional_rep;
                        while (curr_rep < range.max) : (curr_rep += 1) {
                            if (try matchAtom(atom.data, options, str[curr_slice.len..], result)) |matched_slice| {
                                curr_slice = str[0 .. matched_slice.len + curr_slice.len];
                            } else return curr_slice;
                        }
                    }
                    return curr_slice;
                },
            }
        },
        .concat => |concat| {
            if (try matchSubExpr(concat.lhs.*, options, str, result)) |lhs_slice| {
                if (try matchSubExpr(concat.rhs.*, options, str[lhs_slice.len..], result)) |rhs_slice| {
                    return str[0 .. lhs_slice.len + rhs_slice.len];
                }
            }
            return null;
        },
    }

    return null;
}

/// Handles regex expressions by evaluating the left-hand side (lhs) and, if
/// present, the right-hand side (rhs). It considers MatchOptions, the input
/// string str, and a result placeholder. After ensuring the string length
/// meets the required minimum, it attempts to match the lhs using
/// matchSubExpr. If successful, it returns the matched slice. If there's a
/// rhs, it recursively invokes matchExpr to match it against the input string,
/// returning the corresponding slice if successful. The function returns
/// slices representing the matched portions or null based on the regex
/// expression evaluation.
inline fn matchExpr(comptime expr: RegexParser.Expr, comptime options: MatchOptions, str: []const options.encoding.CharT(), result: anytype) !?@TypeOf(str) {
    const min_len = comptime expr.minLen(options.encoding);
    if (str.len < min_len) return null;

    if (try matchSubExpr(expr.lhs, options, str, result)) |lhs_slice| {
        return lhs_slice;
    }
    if (expr.rhs) |rhs| {
        if (try matchExpr(rhs.*, options, str, result)) |rhs_slice| {
            return rhs_slice;
        }
    }
    return null;
}

/// Models match options for a given pass (at present, this only includes an
/// encoding indicator).
pub const MatchOptions = struct {
    encoding: Encoding = .utf8,
};

/// Generates a MatchResult type based on a given regex pattern and match
/// options. It verifies successful regex parsing via RegexParser.parse. Upon
/// success, it initializes the MatchResult structure with a slice representing
/// the match and potential capturing group information. The resulting
/// structure holds a slice, an array of captures, and a resetCaptures method
/// to reset captures. If named captures exist, it provides a capture method
/// to retrieve captures by name, cross-referencing names within the array and
/// returning the corresponding slice or triggering a compile error if the name
/// doesn't match. If parsing fails, the function returns void.
pub fn MatchResult(comptime regex: []const u8, comptime options: MatchOptions) type {
    const CharT = options.encoding.CharT();

    if (RegexParser.parse(regex)) |parsed| {
        const capture_len = parsed.captures.len;
        var capture_names: [capture_len]?[]const u8 = undefined;
        for (parsed.captures, 0..) |capt, idx| {
            if (capt.capture_info) |info| {
                capture_names[idx] = info.name;
            }
        }

        const capture_names2 = capture_names;

        return struct {
            const Self = @This();

            slice: []const CharT,
            captures: [capture_len]?[]const CharT = [1]?[]const CharT{null} ** capture_len,

            inline fn resetCaptures(self: *Self) void {
                self.captures = [1]?[]const CharT{null} ** capture_len;
            }

            pub usingnamespace if (capture_len != 0)
                struct {
                    pub fn capture(self: Self, comptime name: []const u8) ?[]const CharT {
                        inline for (capture_names2, 0..) |maybe_name, curr_idx| {
                            if (maybe_name) |curr_name| {
                                if (comptime std.mem.eql(u8, name, curr_name))
                                    return self.captures[curr_idx];
                            }
                        }
                        @compileError("No capture named '" ++ name ++ "'");
                    }
                }
            else
                struct {};
        };
    }
    return void;
}

/// Aims to match a given regex pattern against an input string, considering
/// match options. It starts by attempting to parse the regex pattern using
/// RegexParser.parse. Upon successful parsing, it initializes a MatchResult
/// structure and attempts to match the expression against the input string
/// using matchExpr. If a match is found, it checks if the matched slice length
/// equals the input string length; if so, it updates the MatchResult slice and
/// returns the result. If parsing fails, it returns an empty MatchResult.
pub fn match(comptime regex: []const u8, comptime options: MatchOptions, str: []const options.encoding.CharT()) !?MatchResult(regex, options) {
    if (comptime RegexParser.parse(regex)) |parsed| {
        var result: MatchResult(regex, options) = .{
            .slice = undefined,
        };
        if (try matchExpr(parsed.root, options, str, &result)) |slice| {
            // TODO More than just complete matches.
            if (slice.len != str.len) return null;
            result.slice = slice;
            return result;
        }
        return null;
    }

    return {};
}

/// Aims to locate occurrences of a given regex pattern within an input string,
/// considering match options. It begins by attempting to parse the regex
/// pattern using RegexParser.parse. Upon successful parsing, it initializes a
/// MatchResult structure and checks if the input string length satisfies the
/// minimum required for matching. It employs a strategy (currently a basic
/// strategy using a while loop) to traverse the input string while
/// incrementing the start index, attempting to match the regex pattern against
/// substrings of the input. If a match is found, it updates the MatchResult
/// slice and returns the result. If the parsing fails, it returns an empty
/// MatchResult. Additionally, it handles specific encoding-related errors by
/// continuing the search loop or returning the error encountered.
pub fn search(comptime regex: []const u8, comptime options: MatchOptions, str: []const options.encoding.CharT()) !?MatchResult(regex, options) {
    if (comptime RegexParser.parse(regex)) |parsed| {
        var result: MatchResult(regex, options) = .{
            .slice = undefined,
        };
        const min_len = comptime parsed.root.minLen(options.encoding);
        if (str.len < min_len) return null;
        // TODO Better strategy.
        var start_idx: usize = 0;
        while (start_idx <= (str.len - min_len)) : (start_idx += 1) {
            if (matchExpr(parsed.root, options, str[start_idx..], &result) catch |err| {
                if (options.encoding == .utf8 and err == error.Utf8InvalidStartByte) continue;
                if (options.encoding == .utf16le and err == error.UnexpectedSecondSurrogateHalf) continue;
                return err;
            }) |slice| {
                result.slice = slice;
                return result;
            }
            result.resetCaptures();
        }
        return null;
    }

    return {};
}
