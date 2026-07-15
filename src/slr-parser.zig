const std = @import("std");
const debug = std.debug;

const slr = @import("slr-table-generator.zig");

const LexError = error{
    UnexpectedToken,
    NoTokensFound,
};

pub const ParseError = error{
    InvalidSyntax,
    UnexpectedToken,
};

// Tokenize a string containing a WFF. Returns an ArrayList of Tokens if a valid
// string is passed, else a LexError. Caller must free the returned ArrayList.
fn testTokenize(allocator: std.mem.Allocator, wff_string: []const u8) !std.ArrayList(TestToken) {
    const State = enum {
        None,
        Cond,
        BicondBegin,
        BicondEnd,
    };

    var tokens = std.ArrayList(TestToken).init(allocator);
    errdefer {
        for (tokens.items) |tok| switch (tok) {
            .Proposition => |prop| allocator.free(prop.string),
            else => {},
        };
        tokens.deinit();
    }

    var state: State = State.None;
    for (wff_string) |c| {
        // errdefer {
        //     debug.print("\n\tInvalid token: {c}\n\tProcessed tokens: {any}\n", .{ c, tokens.items });
        // }

        if (std.ascii.isWhitespace(c)) {
            continue;
        }

        // This is the main tokenizing logic. There are 3 outcomes of this
        // block:
        // (1) A token is correctly processed => a lex.Token struct is assigned to
        //     tok, code flow continues normally
        // (2) An intermediate token is processed (e.g. '=' in the "<=>"
        //     operator) => state is changed appropriately (e.g. to BicondEnd)
        //     and we continue right away to the next loop iteration without
        //     assigning a value to tok.
        // (3) An unexpected token is encountered => we return an error.
        const tok = try switch (state) {
            .None => switch (c) {
                '~' => TestToken{ .Operator = TestToken.WffOperator.Not },
                'v' => TestToken{ .Operator = TestToken.WffOperator.Or },
                '^' => TestToken{ .Operator = TestToken.WffOperator.And },
                '=' => {
                    state = State.Cond;
                    continue;
                },
                '<' => {
                    state = State.BicondBegin;
                    continue;
                },

                '(' => TestToken.LParen,
                ')' => TestToken.RParen,

                'T' => TestToken.True,
                'F' => TestToken.False,

                // TODO: Include v, T, F as an allowable variable name (currently it
                // conflicts with OR operator, True, False tokens).
                'a'...'u', 'w'...'z', 'A'...'E', 'G'...'S', 'U'...'Z' => |val| ret: {
                    var str = try allocator.alloc(u8, 1);
                    str[0] = val;
                    break :ret TestToken{ .Proposition = TestToken.PropositionVar{ .string = str } };
                },

                else => LexError.UnexpectedToken,
            },
            .Cond => switch (c) {
                '>' => ret: {
                    state = State.None;
                    break :ret TestToken{ .Operator = TestToken.WffOperator.Cond };
                },
                else => LexError.UnexpectedToken,
            },
            .BicondBegin => switch (c) {
                '=' => {
                    state = State.BicondEnd;
                    continue;
                },
                else => LexError.UnexpectedToken,
            },
            .BicondEnd => switch (c) {
                '>' => ret: {
                    state = State.None;
                    break :ret TestToken{ .Operator = TestToken.WffOperator.Bicond };
                },
                else => LexError.UnexpectedToken,
            },
        };

        try tokens.append(tok);
    }
    if (tokens.items.len == 0) {
        return LexError.NoTokensFound;
    }
    return tokens;
}

const TestVariable = struct {
    const Self = @This();

    name: []const u8,

    fn fromString(string: []const u8) Self {
        return TestVariable{ .name = string };
    }

    fn getString(self: Self) []const u8 {
        return self.name;
    }

    pub fn eql(self: Self, other: Self) bool {
        return std.mem.eql(u8, self.name, other.name);
    }
};

const TestToken = union(enum) {
    pub const PropositionVar = struct {
        string: []const u8,

        pub fn equals(self: PropositionVar, other: PropositionVar) bool {
            return self.string[0] == other.string[0];
        }
    };

    pub const WffOperator = enum {
        Not, // '~'
        And, // '^'
        Or, // 'v'
        Cond, // Conditional: "=>"
        Bicond, // Biconditional: "<=>"

        pub fn getString(self: WffOperator) []const u8 {
            return switch (self) {
                .Not => "~",
                .And => "^",
                .Or => "v",
                .Cond => "=>",
                .Bicond => "<=>",
            };
        }
    };

    LParen,
    RParen,
    True,
    False,
    Proposition: PropositionVar,
    Operator: WffOperator,

    fn deinit(self: TestToken, allocator: std.mem.Allocator) void {
        switch (self) {
            .Proposition => |prop| allocator.free(prop.string),
            else => {},
        }
    }

    pub fn copy(self: TestToken, allocator: std.mem.Allocator) !TestToken {
        return switch (self) {
            .Proposition => |prop| TestToken{ .Proposition = PropositionVar{ .string = try allocator.dupe(u8, prop.string) } },
            else => self,
        };
    }

    /// Compare two Token instances. They are equal if they are of the same
    /// sub-type, and in the case of Proposition and Operator, if their stored
    /// values are equivalent.
    pub fn eql(self: TestToken, other: TestToken) bool {
        return switch (self) {
            .LParen => switch (other) {
                .LParen => true,
                else => false,
            },
            .RParen => switch (other) {
                .RParen => true,
                else => false,
            },
            .True => switch(other) {
                .True => true,
                else => false,
            },
            .False => switch(other) {
                .False => true,
                else => false,
            },
            .Proposition => |prop| switch (other) {
                .Proposition => |other_prop| prop.equals(other_prop),
                else => false,
            },
            .Operator => |op| switch (other) {
                .Operator => |other_op| op == other_op,
                else => false,
            },
        };
    }

    pub fn getString(self: TestToken) []const u8 {
        return switch (self) {
            .LParen => "(",
            .RParen => ")",
            .Proposition => |prop| prop.string,
            .Operator => |op| op.getString(),
            .True => "T",
            .False => "F",
        };
    }
};
const TestTerminal = enum {
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

    fn getString(self: Self) []const u8 {
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

fn oldTokenToTestTerminal(token: TestToken) ?TestTerminal {
    return switch (token) {
        .LParen => TestTerminal.LParen,
        .RParen => TestTerminal.RParen,
        .True, .False, .Proposition => TestTerminal.Proposition,
        .Operator => |op| switch (op) {
            .Not => TestTerminal.Not,
            .And => TestTerminal.And,
            .Or => TestTerminal.Or,
            .Cond => TestTerminal.Cond,
            .Bicond => TestTerminal.Bicond,
        },
    };
}

const test_grammar_old = ret: {
    const V = TestVariable.fromString;

    const G = slr.Grammar(TestVariable, TestTerminal);
    break :ret G.initFromTuples(
        .{
            .{ V("S"), .{V("wff")} },
            .{ V("wff"), .{ TestTerminal.Proposition} },
            .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
        },
        V("S"),
        TestTerminal.End,
    );
};

const TestParser = Parser(
    TestVariable,
    TestTerminal,
    TestToken,
    @typeInfo(@typeInfo(@TypeOf(testTokenize)).Fn.return_type.?).ErrorUnion.error_set,
    testTokenize,
    oldTokenToTestTerminal,
);

const test_parser = TestParser {
    .table = TestParser.ParseTable.initComptime(test_grammar_old),
};

const TestParseTree = ParseTree(TestToken);

//#####################################

pub fn ParseTreePreOrderIterator(comptime Token: type) type {
    return struct {
        const Self = @This();
        const ParseTreeType = ParseTree(Token);

        start: *const ParseTreeType.Node,
        current: ?[*]ParseTreeType.Node,

        fn backtrack(self: Self) ?[*]ParseTreeType.Node {
            var next_node = self.current.?;
            while (next_node[0].parent) |parent| {
                if (@as(@TypeOf(self.start), @ptrCast(next_node)) == self.start) return null;
                const siblings = parent.kind.nonleaf;
                if (&(next_node[0]) == &(siblings[siblings.len - 1])) {
                    next_node = @ptrCast(parent);
                } else {
                    return next_node + 1;
                }
            }
            return null;
        }

        pub fn next(self: *Self) ?*ParseTreeType.Node {
            const current_node = &(self.current orelse return null)[0];

            self.current = switch (current_node.kind) {
                .leaf => self.backtrack(),
                .nonleaf => |children| @ptrCast(&children[0]),
            };

            return current_node;
        }

        pub fn nextUnchecked(self: *Self) *ParseTreeType.Node {
            std.debug.assert(self.hasNext());
            return self.next().?;
        }

        pub fn peek(self: Self) ?*ParseTreeType.Node {
            if (self.current) |node| {
                return &node[0];
            } else {
                return null;
            }
        }

        pub fn hasNext(self: Self) bool {
            return self.peek() != null;
        }

        // This means we won't visit this node, its child nodes, nor their grandchildren etc.
        pub fn skipChildren(self: *Self) void {
            const current = &(self.current orelse return)[0];
            if (current.parent) |parent| {
                self.current = @ptrCast(parent);
                self.current = self.backtrack();
            } else {
                self.current = null;
            }
        }
    };
}

test "ParseTreePreOrderIterator" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "(p v q)");
    defer tree.deinit();

    try std.testing.expectEqual(tree.root, tree.root.kind.nonleaf[0].parent.?);
    const c: *TestParseTree.Node = tree.root.kind.nonleaf[1].parent.?;
    try std.testing.expectEqual(c, c.kind.nonleaf[0].parent.?);

    var it = tree.root.iterPreOrder();

    var t1 = TestParseTree.Kind{ .leaf = TestToken.LParen };
    var t2 = TestParseTree.Kind{ .leaf = TestToken{ .Proposition = .{ .string = try std.testing.allocator.dupe(u8, "p") } } };
    defer std.testing.allocator.free(t2.leaf.Proposition.string);
    var t3 = TestParseTree.Kind{ .leaf = TestToken{ .Operator = .Or } };
    var t4 = TestParseTree.Kind{ .leaf = TestToken{ .Proposition = .{ .string = try std.testing.allocator.dupe(u8, "q") } } };
    defer std.testing.allocator.free(t4.leaf.Proposition.string);
    var t5 = TestParseTree.Kind{ .leaf = TestToken.RParen };

    _ = it.next();
    try std.testing.expect(t1.leaf.eql(it.next().?.kind.leaf));
    _ = it.next();
    try std.testing.expect(t2.leaf.eql(it.next().?.kind.leaf));
    try std.testing.expect(t3.leaf.eql(it.next().?.kind.leaf));
    _ = it.next();
    try std.testing.expect(t4.leaf.eql(it.next().?.kind.leaf));
    try std.testing.expect(t5.leaf.eql(it.next().?.kind.leaf));
    try std.testing.expect((it.next()) == null);
}

// TODO: Include this in scope of ParseTree so we don't need Token arg
pub fn ParseTreePostOrderIterator(comptime Token: type) type {
    return struct {
        const Self = @This();
        const ParseTreeType = ParseTree(Token);

        root: *const ParseTreeType.Node,
        current: ?[*]ParseTreeType.Node,

        // if terminal, go to parent
        //      if came from last child, set next=parent
        //      else, set next to next deepest sibling
        // else, get parent
        //      if parent is null, set next=null
        //      else if came from last child, set next=parent
        //      else, set next to next deepest sibling
        pub fn next(self: *Self) ?*ParseTreeType.Node {
            const current_node = &(self.current orelse return null)[0];
            const parent = current_node.parent orelse {
                self.current = null;
                return current_node;
            };
            const siblings = parent.kind.nonleaf;

            if (current_node == self.root) {
                self.current = null;
                return current_node;
            } else if (current_node == &siblings[siblings.len - 1]) {
                self.current = @ptrCast(parent);
                return current_node;
            }

            var next_node = &(self.current.?[1]); // get sibling node
            while (true) {
                switch (next_node.kind) {
                    .leaf => break,
                    .nonleaf => |children| next_node = &children[0],
                }
            }
            self.current = @ptrCast(next_node);

            return current_node;
        }

        pub fn nextUnchecked(self: *Self) *ParseTreeType.Node {
            std.debug.assert(self.hasNext());
            return self.next().?;
        }

        pub fn peek(self: Self) ?*ParseTreeType.Node {
            if (self.current) |node| {
                return &node[0];
            } else {
                return null;
            }
        }

        pub fn hasNext(self: Self) bool {
            return self.peek() != null;
        }
    };
}

test "ParseTreePostOrderIterator" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "(p v q)");
    defer tree.deinit();

    var it = tree.root.iterPostOrder();

    var t1 = TestParseTree.Kind{ .leaf = TestToken.LParen };
    var t2 = TestParseTree.Kind{ .leaf = TestToken{ .Proposition = TestToken.PropositionVar{ .string = try std.testing.allocator.dupe(u8, "p") } } };
    defer std.testing.allocator.free(t2.leaf.Proposition.string);
    var t3 = TestParseTree.Kind{ .leaf = TestToken{ .Operator = TestToken.WffOperator.Or } };
    var t4 = TestParseTree.Kind{ .leaf = TestToken{ .Proposition = TestToken.PropositionVar{ .string = try std.testing.allocator.dupe(u8, "q") } } };
    defer std.testing.allocator.free(t4.leaf.Proposition.string);
    var t5 = TestParseTree.Kind{ .leaf = TestToken.RParen };

    try std.testing.expect(t1.leaf.eql(it.nextUnchecked().kind.leaf));
    try std.testing.expect(t2.leaf.eql(it.nextUnchecked().kind.leaf));
    _ = it.next();
    try std.testing.expect(t3.leaf.eql(it.nextUnchecked().kind.leaf));
    try std.testing.expect(t4.leaf.eql(it.nextUnchecked().kind.leaf));
    _ = it.next();
    try std.testing.expect(t5.leaf.eql(it.nextUnchecked().kind.leaf));
    _ = it.next();
    try std.testing.expect(it.next() == null);
}

pub fn ParseTree(comptime Token: type) type {
    return struct {
        const Self = @This();

        allocator: std.mem.Allocator,
        root: *Node,

        pub const Kind = union(enum) {
            leaf: Token,
            nonleaf: []Node,
        };

        // Note: Any time you deal with nodes, you should probably deal with
        // pointers. Nodes are stored in a way that makes using a local copy
        // incorrect for many things (such as iteration).
        pub const Node = struct {
            parent: ?*Node = null,
            kind: Kind,

            pub fn asString(self: Node) []const u8 {
                return switch (self.kind) {
                    .leaf => |t| t.getString(),
                    .nonleaf => "wff",
                };
            }

            pub fn copy(self: *Node, allocator: std.mem.Allocator) !*Node {
                var copy_root = try allocator.create(Node);
                copy_root.parent = null;

                var it = self.iterPreOrder();
                var copy_it = copy_root.iterPreOrder();

                while (it.hasNext()) {
                    const node = it.nextUnchecked();
                    var copy_node = copy_it.peek().?;

                    switch (node.kind) {
                        .leaf => |tok| copy_node.kind = Kind{ .leaf = try tok.copy(allocator) },
                        .nonleaf => |children| {
                            copy_node.kind = Kind{ .nonleaf = try allocator.alloc(Node, children.len) };
                            copy_node.kind.nonleaf.len = children.len;
                            for (copy_node.kind.nonleaf) |*child| {
                                child.parent = copy_node;
                            }
                        },
                    }
                    _ = copy_it.next();
                }

                return copy_root;
            }

            pub fn iterPreOrder(self: *Node) ParseTreePreOrderIterator(Token) {
                return ParseTreePreOrderIterator(Token){ .start = self, .current = @ptrCast(self) };
            }

            pub fn iterPostOrder(self: *Node) ParseTreePostOrderIterator(Token) {
                var start_node = self;
                while (true) {
                    switch (start_node.kind) {
                        .leaf => break,
                        .nonleaf => |children| start_node = &children[0],
                    }
                }
                return ParseTreePostOrderIterator(Token){ .root = self, .current = @ptrCast(start_node) };
            }

            // TODO: Specify *const here and in other places
            // We would need to differentiate between mutable and immutable
            // iteration to make this possible.
            pub fn eql(self: *Node, other: *Node) bool {
                var it = self.iterPostOrder();
                var other_it = other.iterPostOrder();

                while (it.hasNext() and other_it.hasNext()) {
                    const node = it.nextUnchecked();
                    const other_node = other_it.nextUnchecked();

                    switch (node.kind) {
                        .leaf => |tok| switch (other_node.kind) {
                            .leaf => |other_tok| if (!tok.eql(other_tok)) return false,
                            .nonleaf => return false,
                        },
                        .nonleaf => switch (other_node.kind) {
                            .leaf => return false,
                            .nonleaf => continue,
                        },
                    }
                }
                return true;
            }
        };

        pub fn init(allocator: std.mem.Allocator, root: *Node) !Self {
            return Self{ .allocator = allocator, .root = root };
        }

        pub fn deinit(self: Self) void {
            var it = self.iterPostOrder();
            while (it.next()) |node| {
                const n = node;
                switch (n.kind) {
                    .leaf => |tok| tok.deinit(self.allocator),
                    .nonleaf => |children| self.allocator.free(children),
                }
            }
            self.allocator.destroy(self.root);
        }

        pub fn copy(self: Self) !Self {
            return Self{ .root = try self.root.copy(self.allocator), .allocator = self.allocator };
        }

        /// Compare two ParseTree instances. They are equal if both have the same
        /// tree structure (determined by non-terminal nodes, which are the only
        /// nodes with children) and if each pair of corresponding terminal nodes
        /// have equivalent tokens (see lex.Token.equals).
        pub fn eql(self: Self, other: Self) bool {
            return self.root.eql(other.root);
        }

        pub fn iterPreOrder(self: Self) ParseTreePreOrderIterator(Token) {
            return self.root.iterPreOrder();
        }

        pub fn iterPostOrder(self: Self) ParseTreePostOrderIterator(Token) {
            return self.root.iterPostOrder();
        }

        pub fn debugPrint(self: Self) !void {
            const allocator = std.testing.allocator;
            var stack = std.ArrayList(std.ArrayList(Node)).init(allocator);
            try stack.append(std.ArrayList(Node).init(allocator));
            defer {
                for (stack.items) |layer| {
                    layer.deinit();
                }
                stack.deinit();
            }
            try stack.items[0].append(self.root.*);

            debug.print("\n", .{});
            while (stack.popOrNull()) |layer| {
                var next_layer = std.ArrayList(Node).init(allocator);
                var previous_parent: ?*Node = layer.items[0].parent;
                for (layer.items) |node| {
                    if (node.parent != previous_parent) {
                        debug.print("| ", .{});
                    }
                    switch(node.kind) {
                        .leaf => |token| debug.print("{s} ", .{token.getString()}),
                        .nonleaf => |children| {
                            try next_layer.appendSlice(children);

                            debug.print("var ", .{});
                        },
                    }       
                    previous_parent = node.parent;             
                }
                debug.print("\n", .{});
                layer.deinit();
                if (next_layer.items.len == 0) {
                    next_layer.deinit();
                    break;
                }
                try stack.append(next_layer);
            }
        }

        pub fn toString(self: Self, allocator: std.mem.Allocator) ![]u8 {
            var string_buf = std.ArrayList(u8).init(allocator);
            errdefer string_buf.deinit();

            var it = self.iterPreOrder();
            while (it.next()) |node| {
                switch (node.kind) {
                    .leaf => |*tok| {
                        switch (tok.*) {
                            .LParen => try string_buf.appendSlice(tok.getString()),
                            .RParen => {
                                _ = string_buf.pop();
                                try string_buf.appendSlice(tok.getString());
                                try string_buf.append(' ');
                            },
                            .Operator => |op| {
                                try string_buf.appendSlice(tok.getString());
                                switch (op) {
                                    .And, .Or, .Cond, .Bicond => try string_buf.append(' '),
                                    .Not => {},
                                }
                            },
                            .Proposition, .True, .False => {
                                try string_buf.appendSlice(tok.getString());
                                try string_buf.append(' ');
                            },
                        }
                    },
                    .nonleaf => {},
                }
            }
            _ = string_buf.pop(); // remove trailing space
            return string_buf.toOwnedSlice();
        }
    };
}

// TODO: fn to build trees more easily for testing larger expressions

// test "ParseTree.debugPrint: (p v q)" {
//     const allocator = std.testing.allocator;
//     const tree = try test_parser.parse(allocator, "(p v q)");
//     defer tree.deinit();

//     try tree.debugPrint();
// }

test "ParseTree.toString: (p v q)" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "(p v q)");
    defer tree.deinit();

    const string = try tree.toString(std.testing.allocator);
    defer std.testing.allocator.free(string);

    try std.testing.expectEqualStrings("(p v q)", string);
}

test "ParseTree.toString: ~((a ^ b) => (c ^ ~d))" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "~((a ^ b) => (c ^ ~d))");
    defer tree.deinit();

    const string = try tree.toString(std.testing.allocator);
    defer std.testing.allocator.free(string);

    try std.testing.expectEqualStrings("~((a ^ b) => (c ^ ~d))", string);
}

test "ParseTree.copy: (p v q)" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "(p v q)");
    defer tree.deinit();

    var copy = try tree.copy();
    defer copy.deinit();

    try std.testing.expect(tree.eql(copy));
}

test "ParseTree.copy: ((a ^ b) v (c ^ d))" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "((a ^ b) v (c ^ d))");
    defer tree.deinit();

    var copy = try tree.copy();
    defer copy.deinit();

    try std.testing.expect(tree.eql(copy));
}

test "ParseTree.copy: p" {
    const allocator = std.testing.allocator;

    const tree = try test_parser.parse(allocator, "p");
    defer tree.deinit();

    var copy = try tree.copy();
    defer copy.deinit();

    try std.testing.expect(tree.eql(copy));
}

// TODO: Define error set of tokenize_func
// T must have .eql, .deinit, ...
pub fn Parser(
    comptime Variable: type,
    comptime Terminal: type,
    comptime Token: type,
    comptime TokenizeErrorSet: type,
    comptime tokenize: fn (std.mem.Allocator, []const u8) TokenizeErrorSet!std.ArrayList(Token),
    comptime terminalFromToken: fn (Token) ?Terminal,
) type {
    return struct {
        const Self = @This();
        pub const Grammar = slr.Grammar(Variable, Terminal);
        pub const ParseTable = slr.ParseTable(Variable, Terminal);
        pub const ParseTreeType = ParseTree(Token);

        const StackItem = struct {
            state: ParseTable.StateIdx,
            node: ParseTreeType.Node,
        };

        table: ParseTable,

        pub fn init(allocator: std.mem.Allocator, grammar: Grammar) !Self {
            return Self{ .table = try ParseTable.init(allocator, grammar) };
        }

        pub fn initComptime(grammar: Grammar) Self {
            return Self{ .table = ParseTable.initComptime(grammar) };
        }

        /// Note: Does NOT free the memory associated with the grammar it was
        /// initialized with.
        pub fn deinit(self: Self) void {
            self.table.deinit();
        }

        /// Performs a reduction (modifies the stack) and returns true
        /// Returns false if no reduction is possible.
        fn reduce(self: Self, allocator: std.mem.Allocator, state_stack: *std.ArrayList(ParseTable.StateIdx), node_stack: *std.ArrayList(ParseTreeType.Node), terminal: Terminal) !bool {
            const top_state = state_stack.getLast();
            const rule_idx = switch (self.table.lookupTerminal(top_state, terminal) orelse return ParseError.UnexpectedToken) {
                .reduce => |idx| idx,
                else => return false,
            };
            const rule = self.table.grammar.getRule(rule_idx);

            var pushed_to_state_stack = false;
            var pushed_to_node_stack = false;
            var children = try allocator.alloc(ParseTreeType.Node, rule.rhs.len);
            errdefer {
                allocator.free(children);
                if (pushed_to_state_stack) {
                    _ = state_stack.pop();
                }
                if (pushed_to_node_stack) {
                    _ = node_stack.pop();
                }
            }

            // Insert nodes into children from right to left to maintain the
            // same order as the stack.
            var i: usize = children.len;
            while (i > 0) {
                i -= 1;
                const child = node_stack.pop();
                _ = state_stack.pop();
                children[i] = child;
                switch (child.kind) {
                    .leaf => {},
                    .nonleaf => |grandchildren| for (grandchildren) |*grandchild| {
                        grandchild.parent = &children[i];
                    },
                }
            }

            const new_parent = ParseTreeType.Node{ .kind = .{ .nonleaf = children } };

            const new_top_state = state_stack.getLast();
            const reduced_state = try switch (self.table.lookupSymbol(new_top_state, rule.lhs)) {
                .state => |state_num| state_num,
                else => ParseError.InvalidSyntax,
            };

            try state_stack.append(reduced_state);
            pushed_to_state_stack = true;
            try node_stack.append(new_parent);
            pushed_to_node_stack = true;

            return true;
        }

        // TODO: Change tokens to slice
        pub fn parse(self: Self, allocator: std.mem.Allocator, string: []const u8) !ParseTreeType {
            var tokens = try tokenize(allocator, string);
            defer tokens.deinit();
            errdefer {
                for (tokens.items) |tok| {
                    tok.deinit(allocator);
                }
            }

            // Initialize parsing stacks
            var state_stack = std.ArrayList(ParseTable.StateIdx).init(allocator);
            defer state_stack.deinit();
            try state_stack.append(self.table.getStartState());

            var node_stack = std.ArrayList(ParseTreeType.Node).init(allocator);
            defer node_stack.deinit();

            // Start parsing tokens
            for (tokens.items) |token| {
                // const next_token = if (i + 1 == tokens.items.len)
                //         self.table.grammar.terminals[self.table.grammar.getEndTerminal().terminal]
                //     else
                //         terminalFromToken(tokens.items[i + 1]) orelse return ParseError.UnexpectedToken;
                var current_state = state_stack.getLast();
                const terminal = terminalFromToken(token) orelse return ParseError.UnexpectedToken;

                while (try self.reduce(allocator, &state_stack, &node_stack, terminal)) {}

                // Current state may have changed during reduction.
                current_state = state_stack.getLast();

                const new_state: ParseTable.StateIdx = try switch (self.table.lookupTerminal(current_state, terminal) orelse return ParseError.UnexpectedToken) {
                    .state => |state_num| state_num,
                    else => ParseError.InvalidSyntax,
                };
                try state_stack.append(new_state);

                const new_node = ParseTreeType.Node{ .kind = .{ .leaf = token } };
                try node_stack.append(new_node);
            }

            // Perform any reductions possible once there are no more tokens.
            const end_terminal = self.table.grammar.terminals[self.table.grammar.getEndSymbol().terminal];
            while (try self.reduce(allocator, &state_stack, &node_stack, end_terminal)) {}

            // Verify that the final resulting state is accepting.
            switch (self.table.lookupTerminal(state_stack.getLast(), end_terminal).?) {
                .accept => {},
                else => return ParseError.InvalidSyntax,
            }

            const root = try allocator.create(ParseTreeType.Node);
            errdefer allocator.destroy(root);

            root.* = node_stack.pop();
            for (root.kind.nonleaf) |*child| {
                child.parent = root;
            }
            return ParseTreeType{ .allocator = allocator, .root = root };
        }

        fn debugPrintStacks(state_stack: std.ArrayList(ParseTable.StateIdx), node_stack: std.ArrayList(ParseTreeType.Node)) void {
            debug.print("S{d}", .{state_stack.items[0]});
            for (state_stack.items[1..], node_stack.items) |state, node| {
                debug.print("<{s}> S{d}", .{ node.asString(), state });
            }
            debug.print("\n", .{});
        }
    };
}

test "Parser.parse: ''" {
    const parser = try TestParser.init(std.testing.allocator, test_grammar_old);
    defer parser.deinit();

    try std.testing.expectError(LexError.NoTokensFound, parser.parse(std.testing.allocator, ""));
}

test "Parser.parse: '~)q p v('" {
    const parser = try TestParser.init(std.testing.allocator, test_grammar_old);
    defer parser.deinit();

    try std.testing.expectError(ParseError.InvalidSyntax, parser.parse(std.testing.allocator, "~)q p v ("));
}

test "Parser.parse: '(p v q)'" {
    const allocator = std.testing.allocator;

    const parser = try TestParser.init(allocator, test_grammar_old);
    defer parser.deinit();

    const tree = try parser.parse(allocator, "(p v q)");
    defer tree.deinit();

    // Build the expected tree manually... it's pretty messy
    const ParseTreeType = ParseTree(TestToken);

    var wff1: ParseTreeType.Node = undefined;
    var wff2: ParseTreeType.Node = undefined;
    var root: ParseTreeType.Node = undefined;

    var children1 = try allocator.alloc(ParseTreeType.Node, 1);
    defer allocator.free(children1);
    var children2 = try allocator.alloc(ParseTreeType.Node, 1);
    defer allocator.free(children2);
    var root_children = try allocator.alloc(ParseTreeType.Node, 5);
    defer allocator.free(root_children);

    var t1 = ParseTreeType.Node{ .parent = &root, .kind = .{ .leaf = TestToken{ .LParen = {} } } };
    var t2 = ParseTreeType.Node{ .parent = &(root_children[1]), .kind = .{ .leaf = TestToken{ .Proposition = TestToken.PropositionVar{ .string = try std.testing.allocator.dupe(u8, "p") } } } };
    var t3 = ParseTreeType.Node{ .parent = &root, .kind = .{ .leaf = TestToken{ .Operator = TestToken.WffOperator.Or } } };
    var t4 = ParseTreeType.Node{ .parent = &(root_children[3]), .kind = .{ .leaf = TestToken{ .Proposition = TestToken.PropositionVar{ .string = try std.testing.allocator.dupe(u8, "q") } } } };
    var t5 = ParseTreeType.Node{ .parent = &root, .kind = .{ .leaf = TestToken{ .RParen = {} } } };
    defer allocator.free(t2.kind.leaf.Proposition.string);
    defer allocator.free(t4.kind.leaf.Proposition.string);

    children1[0] = t2;
    children2[0] = t4;
    wff1 = ParseTreeType.Node{ .parent = &root, .kind = .{ .nonleaf = children1 } };
    wff2 = ParseTreeType.Node{ .parent = &root, .kind = .{ .nonleaf = children2 } };

    root_children[0] = t1;
    root_children[1] = wff1;
    root_children[2] = t3;
    root_children[3] = wff2;
    root_children[4] = t5;
    root = ParseTreeType.Node{ .kind = .{ .nonleaf = root_children } };

    // Hardcoded equality test of tree
    try std.testing.expect(t1.kind.leaf.eql(tree.root.kind.nonleaf[0].kind.leaf));
    try std.testing.expect(t2.kind.leaf.eql(tree.root.kind.nonleaf[1].kind.nonleaf[0].kind.leaf));
    try std.testing.expect(t3.kind.leaf.eql(tree.root.kind.nonleaf[2].kind.leaf));
    try std.testing.expect(t4.kind.leaf.eql(tree.root.kind.nonleaf[3].kind.nonleaf[0].kind.leaf));
    try std.testing.expect(t5.kind.leaf.eql(tree.root.kind.nonleaf[4].kind.leaf));

    // Function equality test of tree
    try std.testing.expect(tree.root.eql(&root));
}

test "ParseTree: ~p" {
    const allocator = std.testing.allocator;

    const parser = try TestParser.init(allocator, test_grammar_old);
    defer parser.deinit();

    const tree = try parser.parse(allocator, "~p");
    defer tree.deinit();

    var t1 = TestToken{ .Operator = TestToken.WffOperator.Not };
    var t2 = TestToken{ .Proposition = TestToken.PropositionVar{ .string = try std.testing.allocator.dupe(u8, "p") } };
    defer std.testing.allocator.free(t2.Proposition.string);

    var it = tree.iterPreOrder();
    _ = it.next();
    try std.testing.expect(t1.eql(it.next().?.kind.leaf));
    _ = it.next();
    try std.testing.expect(t2.eql(it.next().?.kind.leaf));
    try std.testing.expect(it.next() == null);
}
