const std = @import("std");
const debug = std.debug;

const utils = @import("utils.zig");

const stdout = std.io.getStdOut().writer();

pub const TableGeneratorError = error{
    shiftShiftError,
    shiftReduceError,
    shiftAcceptError,
    reduceReduceError,
    reduceAcceptError,
    acceptError,
};

/// Remove leading and trailing whitespace from a string.
/// (Does not modify given string, just returns a slice of it)
fn strStrip(ascii_string: []u8) []u8 {
    var start: usize = 0;
    for (ascii_string, 0..) |c, i| {
        if (!std.ascii.isWhitespace(c)) {
            start = i;
            break;
        }
    }
    var end: usize = start;
    for (ascii_string[start..], start..) |c, i| {
        if (!std.ascii.isWhitespace(c)) {
            end = i + 1;
        }
    }
    return ascii_string[start..end];
}

const SymbolId = union(enum) {
    const Self = @This();
    const VariableId = u16;
    const TerminalId = u16;

    variable_id: VariableId,
    terminal_id: TerminalId,

    fn eql(self: Self, other: Self) bool {
        return switch (self) {
            .variable_id => |id1| switch (other) {
                .variable_id => |id2| id1 == id2,
                .terminal_id => false,
            },
            .terminal_id => |id1| switch (other) {
                .variable_id => false,
                .terminal_id => |id2| id1 == id2,
            },
        };
    }
};

const Production = struct {
    // TODO: Both of these helper structs should probably have dynamically
    // allocated strings
    const Self = @This();

    lhs: SymbolId,
    rhs: []const SymbolId,

    fn eql(self: Self, other: Self) bool {
        if (!self.lhs.eql(other.lhs)) return false;
        if (self.rhs.len != other.rhs.len) return false;
        for (self.rhs, other.rhs) |sym1, sym2| {
            if (!sym1.eql(sym2)) return false;
        }

        return true;
    }
};

const ProductionInstance = struct {
    const Self = @This();

    production: Production,
    cursor: usize,

    fn fromProduction(production: Production) Self {
        return ProductionInstance{ .production = production, .cursor = 0 };
    }

    fn eql(self: Self, other: Self) bool {
        return self.cursor == other.cursor and self.production.eql(other.production);
    }

    fn readCursor(self: Self) ?SymbolId {
        if (self.cursor >= self.production.rhs.len) {
            return null;
        } else {
            return self.production.rhs[self.cursor];
        }
    }

    fn copyAdvanceCursor(self: Self) Self {
        return ProductionInstance{ .production = self.production, .cursor = self.cursor + 1 };
    }
};

// NOTE: variables ids MUST START AT 0 and MUST BE SMALLER THAN ALL TERMINAL IDS and MUST BE ORDERED
// NOTE: comparison of symbols is not always done using .eql in below functions, should try to make this consistent
// NOTE: FOLLOW and FIRST sets generation code is way too nested, should ideally
//       be broken down into smaller functions
pub fn Grammar(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const Self = @This();

        allocator: ?std.mem.Allocator, // TODO: Make this optional, remove initialized_at_comptime
        rules: []const Production,
        variables: []const Variable,
        terminals: []const Terminal,

        pub fn initFromTuples(comptime rule_tuples: anytype, comptime start_variable: Variable, comptime end_terminal: Terminal) Self {
            comptime {
                // Initialize a grammar struct to populate.
                var grammar = Self{
                    .allocator = null,
                    .rules = &[_]Production{},
                    .variables = &[_]Variable{start_variable},
                    .terminals = &[_]Terminal{},
                };

                // Throws a compiler error if the structure or types of the
                // given tuples are invalid.
                verifyTuples(rule_tuples);

                // Iterate over each rule tuple and populate our grammar rules.
                for (rule_tuples) |rule_tuple| {
                    // Initialize a rule struct to populate.
                    var rule = Production{
                        .lhs = undefined,
                        .rhs = &[_]SymbolId{},
                    };

                    // Unpack the left hand side of the rule. We have already
                    // checked that it is of type Variable.
                    const lhs = rule_tuple.@"0";
                    if (grammar.getSymbolIdFromVariable(lhs)) |id| {
                        rule.lhs = id;
                    } else {
                        // If we haven't seen this variable yet, append it to
                        // the variables list.
                        rule.lhs = SymbolId{ .variable_id = grammar.getVariableCount() };
                        grammar.variables = grammar.variables ++ &[_]Variable{lhs};
                    }

                    // Iterate over the symbols on the right hand side of the
                    // rule tuple and unpack each into the grammar rule.
                    const rhs = rule_tuple.@"1";
                    for (std.meta.fieldNames(@TypeOf(rhs))) |rhs_tuple_field_name| {
                        const var_or_terminal = @field(rhs, rhs_tuple_field_name);
                        if (@TypeOf(var_or_terminal) == Variable) {
                            if (grammar.getSymbolIdFromVariable(var_or_terminal)) |symbol| {
                                rule.rhs = rule.rhs ++ &[_]SymbolId{symbol};
                            } else {
                                // If we haven't seen this variable yet, append
                                // it to the variables list.
                                rule.rhs = rule.rhs ++ &[_]SymbolId{SymbolId{ .variable_id = grammar.getVariableCount() }};
                                grammar.variables = grammar.variables ++ &[_]Variable{var_or_terminal};
                            }
                        } else {
                            if (grammar.getSymbolIdFromTerminal(var_or_terminal)) |symbol| {
                                rule.rhs = rule.rhs ++ &[_]SymbolId{symbol};
                            } else {
                                // If we haven't seen this terminal yet, append
                                // it to the terminals list.
                                rule.rhs = rule.rhs ++ &[_]SymbolId{SymbolId{ .terminal_id = grammar.getTerminalCount() }};
                                grammar.terminals = grammar.terminals ++ &[_]Terminal{var_or_terminal};
                            }
                        }
                    }
                    // Append the populated rule.
                    grammar.rules = grammar.rules ++ &[_]Production{rule};
                }
                grammar.terminals = grammar.terminals ++ &[_]Terminal{end_terminal};
                return grammar;
            }
        }

        pub fn deinit(self: Self) void {
            if (self.allocator) |allocator| {
                allocator.free(self.rules);
                allocator.free(self.variables);
                allocator.free(self.terminals);
            }
        }

        /// Verify the structure and types of the given tuples. Return void
        /// since this will be done at comptime and all errors will be compiler
        /// errors.
        /// TODO: Consider removing
        fn verifyTuples(comptime rule_tuples: anytype) void {
            const RuleTuplesType = @TypeOf(rule_tuples);
            const rule_tuples_type_info = @typeInfo(RuleTuplesType);

            // Verify rule_tuples is a tuple (struct with no named fields)
            if (rule_tuples_type_info != .@"struct" or !rule_tuples_type_info.@"struct".is_tuple) {
                @compileError("Expected tuple of rules. Cannot use '" ++ @typeName(RuleTuplesType) ++ "'");
            }
            // Verify rule_tuples is not empty
            if (std.meta.fields(RuleTuplesType).len == 0) {
                @compileError("rule_tuples cannot be empty");
            }

            // Verify each field in rule_tuples is a valid grammar rule
            inline for (std.meta.fieldNames(RuleTuplesType), 0..) |rule_tuples_field_name, i| {
                const rule = @field(rule_tuples, rule_tuples_field_name);
                const RuleType = @TypeOf(rule);
                const rule_type_info = @typeInfo(RuleType);

                // Each rule should be a tuple
                if (rule_type_info != .@"struct" or !rule_type_info.@"struct".is_tuple) {
                    @compileError(std.fmt.comptimePrint("Each rule must be a tuple, found '" ++ @typeName(rule) ++ "' (rule {d})", .{i}));
                }
                // Each rule should have exactly 2 fields
                if (std.meta.fields(RuleType).len != 2) {
                    @compileError(std.fmt.comptimePrint("Each rule must have exactly 2 fields, found {d} fields (rule {d})", .{ rule_type_info.fields.len, i }));
                }

                // The first field of each rule should be of type V
                const lhs = rule.@"0";
                if (@TypeOf(lhs) != Variable) {
                    @compileError(std.fmt.comptimePrint("The first field in each rule tuple must be of type '" ++ @typeName(Variable) ++ "', found '" ++ @typeName(@TypeOf(rule.@"0")) ++ "' (rule {d})", .{i}));
                }

                // The second field of each rule should be a tuple with fields
                // of type V or T (the right hand side of a production).
                const rhs = rule.@"1";
                const RhsType = @TypeOf(rhs);
                const rhs_type_info = @typeInfo(RhsType);

                // Verify rhs is a tuple (struct with no named fields)
                if (rhs_type_info != .@"struct" or !rhs_type_info.@"struct".is_tuple) {
                    @compileError(std.fmt.comptimePrint("The second field in each rule tuple must be a tuple, found '" ++ @typeName(RuleTuplesType) ++ "' (rule {d})", .{i}));
                }
                // Verify rhs is not empty
                if (std.meta.fields(RuleTuplesType).len == 0) {
                    @compileError(std.fmt.comptimePrint("The second field (a tuple) in each rule tuple cannot be empty (rule {d})", .{i}));
                }

                // Verify each symbol in rhs is of type T or V
                inline for (std.meta.fieldNames(RhsType), 0..) |rhs_field_name, j| {
                    const rhs_symbol = @field(rhs, rhs_field_name);
                    const RhsSymbolType = @TypeOf(rhs_symbol);
                    if (RhsSymbolType != Variable and RhsSymbolType != Terminal) {
                        @compileError(std.fmt.comptimePrint("Expected field of type '" ++ @typeName(Variable) ++ "' or '" ++ @typeName(Terminal) ++ "', found '" ++ @typeName(RhsSymbolType) ++ "' (rule {d}, RHS symbol {d})", .{ i, j }));
                    }
                }
            }
        }

        pub fn getRuleId(self: Self, rule: Production) ?usize {
            for (self.rules, 0..) |known_rule, i| {
                if (known_rule.eql(rule)) {
                    return i;
                }
            }
            return null;
        }

        pub fn getVariableCount(self: Self) SymbolId.VariableId {
            return @intCast(self.variables.len);
        }

        pub fn getTerminalCount(self: Self) SymbolId.TerminalId {
            return @intCast(self.terminals.len);
        }

        pub fn getSymbolCount(self: Self) usize {
            return self.getVariableCount() + self.getTerminalCount();
        }

        pub fn getSymbolIdFromVariable(self: Self, variable: Variable) ?SymbolId {
            for (self.variables, 0..) |v, variable_id| {
                if (variable.eql(v)) {
                    return SymbolId{ .variable_id = @intCast(variable_id) };
                }
            }
            return null;
        }

        pub fn getSymbolIdFromTerminal(self: Self, terminal: Terminal) ?SymbolId {
            for (self.terminals, 0..) |t, terminal_id| {
                if (terminal.eql(t)) {
                    return SymbolId{ .terminal_id = @intCast(terminal_id) };
                }
            }
            return null;
        }

        /// Returns variable with index 0.
        pub fn getStartSymbolId(_: Self) SymbolId {
            return SymbolId{ .variable_id = 0 };
        }

        pub fn getEndSymbolId(self: Self) SymbolId {
            return SymbolId{ .terminal_id = @intCast(self.getTerminalCount() - 1) };
        }

        pub fn getStartRuleId(_: Self) usize {
            return 0;
        }

        pub fn getRule(self: Self, rule_id: usize) Production {
            return self.rules[rule_id];
        }

        /// Caller must provide buffers with the necessary room:
        /// * `first_set_table.slice: [self.getVariableCount() * self.getTerminalCount()]`
        /// * `first_var_edge_list: [self.rules.len]`
        /// * `first_var_edge_list_offsets: [self.getVariableCount() + 1]`
        /// * `populated: [self.getVariableCount()]`
        /// * `path: [self.getVariableCount()]`
        /// * `path_edges_explored: [self.getVariableCount()]`
        /// * `visited: [self.getVariableCount()]`
        ///
        /// `first_set_table` is populated with the resulting table, the other
        /// buffers can be freed immediately if they were dynamically allocated.
        fn computeFirstSet(
            self: Self,
            first_set_table: utils.Slice2d([]bool),
            first_var_edge_list: []utils.GraphEdge(SymbolId.VariableId),
            first_var_edge_list_offsets: []usize,
            populated: []bool,
            path: []SymbolId.VariableId,
            path_edges_explored: []usize,
            visited: []bool,
        ) void {
            const GraphEdgeType = utils.GraphEdge(SymbolId.VariableId);

            std.debug.assert(first_set_table.slice.len == self.getVariableCount() * self.getTerminalCount());
            std.debug.assert(first_var_edge_list.len == self.rules.len);
            std.debug.assert(first_var_edge_list_offsets.len == self.getVariableCount() + 1);
            std.debug.assert(populated.len == self.getVariableCount());
            std.debug.assert(path.len == self.getVariableCount());
            std.debug.assert(path_edges_explored.len == self.getVariableCount());
            std.debug.assert(visited.len == self.getVariableCount());

            @memset(first_set_table.slice, false);
            @memset(first_var_edge_list, .{ .from = 0, .to = 0 });
            @memset(first_var_edge_list_offsets, 0);
            @memset(populated, false);

            // First we want to create a directional graph. Each node represents
            // a variable, and an edge from nodes A to B exists if there is a
            // grammar rule where A produces B as the first symbol.
            // NOTE: From here on, grammar variables will be referred to as
            //       nodes in comments and variable names.
            // The graph is represented using a compressed sparse row format. In
            // other words:
            // - first_var_edge_list: Array of edges between nodes, sorted by
            //   origin node.
            // - first_var_edge_list_offsets: Index offset for the start of each
            //   group of nodes in first_var_edge_list.
            // So if first_var_edge_list_offsets[2] = 5, then the edges for the
            // node with ID 2 can be found starting at index 5 of
            // first_var_edge_list.

            // Populate first_set_table with terminals that appear as the first
            // symbol on the right side of a production. Populate
            // first_var_edge_list as described above.
            var first_var_edge_count: usize = 0;
            for (self.rules) |rule| {
                const var_id = rule.lhs.variable_id;
                const first_rule_symbol_id = rule.rhs[0];
                switch (first_rule_symbol_id) {
                    .terminal_id => |terminal_id| first_set_table.row(var_id)[terminal_id] = true,
                    .variable_id => |other_var_id| {
                        first_var_edge_list[first_var_edge_count].from = var_id;
                        first_var_edge_list[first_var_edge_count].to = other_var_id;
                        first_var_edge_count += 1;
                    },
                }
            }

            std.mem.sortUnstable(GraphEdgeType, first_var_edge_list[0..first_var_edge_count], {}, GraphEdgeType.lessThan);

            // Populate first_var_edge_list_offsets as described above now that
            // first_var_edge_list is sorted.
            {
                var current_key = first_var_edge_list[0].from;
                var offset: usize = 0;
                for (first_var_edge_list[0..first_var_edge_count], 0..) |entry, i| {
                    if (current_key != entry.from) {
                        offset = i;
                        current_key = entry.from;
                    }
                    first_var_edge_list_offsets[entry.from] = offset;
                }
            }

            // first_var_edge_list_offsets will be used to calculate the number
            // of edges from a given node like:
            // edges = offsets[i + 1] - offsets[i]
            // To avoid an edge case (heh) with the last node,
            // first_var_edge_list_offsets must be one longer than the number of
            // nodes, and the last entry must be the number of edges in the
            // graph.
            first_var_edge_list_offsets[first_var_edge_list_offsets.len - 1] = first_var_edge_count;

            // For the same reason, it is also helpful to propagate offsets
            // backwards for any nodes that don't have any edges.
            // So if node i has no edges originating from it, its offset will be
            // the same as node (i + 1), rather than 0.
            {
                var last_offset = first_var_edge_count;
                for (1..first_var_edge_list_offsets.len) |i| {
                    const node_id = first_var_edge_list_offsets.len - i - 1;
                    const offset = first_var_edge_list_offsets[node_id];
                    if (first_var_edge_list[offset].from != node_id) {
                        first_var_edge_list_offsets[node_id] = last_offset;
                    } else {
                        last_offset = offset;
                    }
                }
            }

            // Now to solve the actual problem at hand: computing the FIRST set.
            // - Starting from each node, we traverse the graph (depth first)
            //   copying the terminal symbols from each node (variable) that is
            //   reachable, and then mark the starting node as populated.
            // - If we come across a node that is already populated, we don't
            //   explore that path any farther, and instead just copy its
            //   terminals.
            // - We avoid visiting the same node twice in a path (to avoid
            //   infinite loops).
            // After all of the traversals are done, first_set_table will be
            // fully populated.
            for (0..self.getVariableCount()) |start_node| {
                // Initialize path with the starting node.
                var path_len: SymbolId.VariableId = 1;
                path[0] = @intCast(start_node);

                // Used to track how many edges we have already explored from
                // each node along the path.
                @memset(path_edges_explored, 0);

                // Used to track which nodes have already been visited.
                @memset(visited, false);
                visited[start_node] = true;

                // Perform a depth first traversal from the start node.
                var state: enum { backtracking, exploring } = .exploring;
                while (path_len > 0) switch (state) {
                    .exploring => {
                        const current_node = path[path_len - 1];
                        const edges_explored = path_edges_explored[current_node];
                        const edge_count = first_var_edge_list_offsets[@as(usize, current_node) + 1] - first_var_edge_list_offsets[current_node];

                        if (edges_explored < edge_count) {
                            // Get the node from the next unexplored edge.
                            const next_node = first_var_edge_list[first_var_edge_list_offsets[current_node] + edges_explored].to;
                            path_edges_explored[current_node] += 1;

                            // Avoid loops.
                            if (visited[next_node]) {
                                continue;
                            }

                            // Continue exploring.
                            visited[next_node] = true;
                            path[path_len] = next_node;
                            path_len += 1;

                            // Unless we've already explored this path.
                            if (populated[next_node]) {
                                state = .backtracking;
                            }
                        } else {
                            // We have explored this path fully, time to
                            // backtrack
                            state = .backtracking;
                        }
                    },
                    .backtracking => {
                        // Before we backtrack, copy terminals from the current
                        // node into the starting node.
                        const current_node = path[path_len - 1];
                        utils.rowUnion(first_set_table, start_node, current_node);

                        // Then move back one node and keep exploring.
                        path_len -= 1;
                        state = .exploring;
                    },
                };

                // The FIRST set for this node is now fully populated.
                populated[start_node] = true;
            }
        }

        /// Computes the FIRST set for the grammar as a table. Each row
        /// represents a grammar variable, each column a grammar terminal. If
        /// row x, column y is true, then the y'th terminal is in the x'th
        /// variable's FIRST set.
        ///
        /// The returned slice should be interpreted as a row-wise 2D array as
        /// described above. Caller must free.
        ///
        /// NOTE: $ (END character) can never be first
        pub fn getFirstSet(self: Self, allocator: std.mem.Allocator) ![]bool {
            const first_set_buffer = try allocator.alloc(bool, self.getVariableCount() * self.getTerminalCount());
            errdefer allocator.free(first_set_buffer);
            const first_var_edge_list_buffer = try allocator.alloc(utils.GraphEdge(SymbolId.VariableId), self.rules.len);
            defer allocator.free(first_var_edge_list_buffer);
            const first_var_edge_list_offsets_buffer = try allocator.alloc(usize, self.getVariableCount() + 1);
            defer allocator.free(first_var_edge_list_offsets_buffer);
            const populated_buffer = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(populated_buffer);
            const path_buffer = try allocator.alloc(SymbolId.VariableId, self.getVariableCount());
            defer allocator.free(path_buffer);
            const path_edges_explored_buffer = try allocator.alloc(usize, self.getVariableCount());
            defer allocator.free(path_edges_explored_buffer);
            const visited_buffer = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(visited_buffer);

            self.computeFirstSet(
                utils.Slice2d([]bool).init(first_set_buffer, self.getTerminalCount()),
                first_var_edge_list_buffer,
                first_var_edge_list_offsets_buffer,
                populated_buffer,
                path_buffer,
                path_edges_explored_buffer,
                visited_buffer,
            );
            return first_set_buffer;
        }

        /// Comptime version of `getFirstSet()`, no dynamic allocation needed.
        pub fn getFirstSetComptime(comptime self: Self) [self.getVariableCount() * self.getTerminalCount()]bool {
            comptime {
                var first_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;
                var first_var_edge_list_buffer: [self.rules.len]utils.GraphEdge(SymbolId.VariableId) = undefined;
                var first_var_edge_list_offsets_buffer: [self.getVariableCount() + 1]usize = undefined;
                var populated_buffer: [self.getVariableCount()]bool = undefined;
                var path_buffer: [self.getVariableCount()]SymbolId.VariableId = undefined;
                var path_edges_explored_buffer: [self.getVariableCount()]usize = undefined;
                var visited_buffer: [self.getVariableCount()]bool = undefined;

                self.computeFirstSet(
                    utils.Slice2d([]bool).init(&first_set_buffer, self.getTerminalCount()),
                    &first_var_edge_list_buffer,
                    &first_var_edge_list_offsets_buffer,
                    &populated_buffer,
                    &path_buffer,
                    &path_edges_explored_buffer,
                    &visited_buffer,
                );
                return first_set_buffer;
            }
        }

        /// Caller must provide buffers with the necessary room:
        /// * `follow_set: [self.getVariableCount() * self.getTerminalCount()]bool`
        /// * `seen: [self.getVariableCount()]bool`
        /// * `stack_buffer: [self.getVariableCount()]Symbol`
        ///
        /// Caller must also provide a **populated** `first_set` table.
        ///
        /// `follow_set` is populated with the resulting table, the other buffers
        /// can be freed immediately if they were dynamically allocated.
        fn computeFollowSet(
            self: Self,
            follow_set: []bool,
            seen: []bool,
            stack_buffer: []SymbolId,
            first_set: []const bool,
        ) void {
            std.debug.assert(follow_set.len >= self.getVariableCount() * self.getTerminalCount());
            std.debug.assert(seen.len >= self.getVariableCount());
            std.debug.assert(stack_buffer.len >= self.getVariableCount());
            std.debug.assert(first_set.len >= self.getVariableCount() * self.getTerminalCount());

            const first_set_2d_view = utils.Slice2d([]const bool).init(first_set, self.getTerminalCount());

            @memset(follow_set, false);
            var follow_set_2d_view = utils.Slice2d([]bool).init(follow_set, self.getTerminalCount());

            // Initialize FOLLOW(startsymbol) to include end of input symbol.
            follow_set_2d_view.row(0)[follow_set_2d_view.row_length - 1] = true;

            for (0..self.getVariableCount()) |v_id| {
                @memset(seen, false);
                seen[v_id] = true; // redundant?

                var stack = std.ArrayListUnmanaged(SymbolId).initBuffer(stack_buffer);
                stack.appendAssumeCapacity(SymbolId{ .variable_id = @intCast(v_id) });

                while (stack.pop()) |top_symbol| {
                    for (self.rules) |rule| {
                        for (rule.rhs[0 .. rule.rhs.len - 1], 0..) |rhs_symbol, i| {
                            if (!rhs_symbol.eql(top_symbol)) {
                                continue;
                            }

                            switch (rule.rhs[i + 1]) {
                                .terminal_id => |id| follow_set_2d_view.row(v_id)[id] = true,
                                // TODO: Make union function?
                                .variable_id => |id| for (first_set_2d_view.row(id), 0..) |is_first, terminal_id| {
                                    if (is_first) {
                                        follow_set_2d_view.row(v_id)[terminal_id] = true;
                                    }
                                },
                            }
                        }

                        // Handle the last RHS symbol separatly //

                        const last_rhs_symbol = rule.rhs[rule.rhs.len - 1];
                        if (!last_rhs_symbol.eql(top_symbol) or seen[rule.lhs.variable_id]) {
                            continue;
                        }
                        // Check if we already have the Follow set for this variable
                        // TODO: Make this more explicit?
                        if (rule.lhs.variable_id < v_id) {
                            for (follow_set_2d_view.row(rule.lhs.variable_id), 0..) |is_follow, terminal_id| {
                                if (is_follow) {
                                    follow_set_2d_view.row(v_id)[terminal_id] = true;
                                }
                            }
                        } else {
                            stack.appendAssumeCapacity(rule.lhs);
                        }
                        seen[rule.lhs.variable_id] = true;
                    }
                }
            }
        }

        /// Computes the FOLLOW set for the grammar as a table. Each row
        /// represents a grammar variable, each column a grammar terminal. If
        /// row x, column y is true, then the y'th terminal is in the x'th
        /// variable's FOLLOW set.
        ///
        /// The returned slice should be interpreted as a row-wise 2D array as
        /// described above. Caller must free.
        ///
        /// NOTE: Assumes $ is last terminal symbol ID and S' is the first
        ///       symbol ID (0). FOLLOW(S') will be initialized to {$}, which
        ///       will then be propogated as needed.
        pub fn getFollowSet(self: Self, allocator: std.mem.Allocator) ![]bool {
            const first_set_buffer = try allocator.alloc(bool, self.getVariableCount() * self.getTerminalCount());
            defer allocator.free(first_set_buffer);
            const first_var_edge_list_buffer = try allocator.alloc(utils.GraphEdge(SymbolId.VariableId), self.rules.len);
            defer allocator.free(first_var_edge_list_buffer);
            const first_var_edge_list_offsets_buffer = try allocator.alloc(usize, self.getVariableCount() + 1);
            defer allocator.free(first_var_edge_list_offsets_buffer);
            const populated_buffer = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(populated_buffer);
            const path_buffer = try allocator.alloc(SymbolId.VariableId, self.getVariableCount());
            defer allocator.free(path_buffer);
            const path_edges_explored_buffer = try allocator.alloc(usize, self.getVariableCount());
            defer allocator.free(path_edges_explored_buffer);
            const visited_buffer = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(visited_buffer);

            self.computeFirstSet(
                utils.Slice2d([]bool).init(first_set_buffer, self.getTerminalCount()),
                first_var_edge_list_buffer,
                first_var_edge_list_offsets_buffer,
                populated_buffer,
                path_buffer,
                path_edges_explored_buffer,
                visited_buffer,
            );

            const follow_set_buffer = try allocator.alloc(bool, self.getVariableCount() * self.getTerminalCount());
            errdefer allocator.free(follow_set_buffer);
            const stack_buffer = try allocator.alloc(SymbolId, self.getVariableCount());
            defer allocator.free(stack_buffer);

            self.computeFollowSet(follow_set_buffer, visited_buffer, stack_buffer, first_set_buffer);
            return follow_set_buffer;
        }

        /// Comptime version of `getFollowSet()`, no dynamic allocation needed.
        pub fn getFollowSetComptime(comptime self: Self) [self.getVariableCount() * self.getTerminalCount()]bool {
            comptime {
                var first_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;
                var first_var_edge_list_buffer: [self.rules.len]utils.GraphEdge(SymbolId.VariableId) = undefined;
                var first_var_edge_list_offsets_buffer: [self.getVariableCount() + 1]usize = undefined;
                var populated_buffer: [self.getVariableCount()]bool = undefined;
                var path_buffer: [self.getVariableCount()]SymbolId.VariableId = undefined;
                var path_edges_explored_buffer: [self.getVariableCount()]usize = undefined;
                var visited_buffer: [self.getVariableCount()]bool = undefined;

                self.computeFirstSet(
                    utils.Slice2d([]bool).init(&first_set_buffer, self.getTerminalCount()),
                    &first_var_edge_list_buffer,
                    &first_var_edge_list_offsets_buffer,
                    &populated_buffer,
                    &path_buffer,
                    &path_edges_explored_buffer,
                    &visited_buffer,
                );

                var follow_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;
                var stack_buffer: [self.getVariableCount()]SymbolId = undefined;

                self.computeFollowSet(&follow_set_buffer, &visited_buffer, &stack_buffer, &first_set_buffer);
                return follow_set_buffer;
            }
        }

        fn printDebugProductionInstance(_: Self, prod: ProductionInstance) !void {
            debug.print("({d})", .{prod.production.lhs.variable_id});
            debug.print(" ->", .{});
            for (prod.production.rhs[0..prod.cursor]) |sym| {
                switch (sym) {
                    .variable_id => |id| debug.print(" ({d})", .{id}),
                    .terminal_id => |id| debug.print(" {d}", .{id}),
                }
            }
            debug.print(" *", .{});
            for (prod.production.rhs[prod.cursor..]) |sym| {
                switch (sym) {
                    .variable_id => |id| debug.print(" ({d})", .{id}),
                    .terminal_id => |id| debug.print(" {d}", .{id}),
                }
            }
            debug.print("\n", .{});
        }
    };
}

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

    fn eql(self: Self, other: Self) bool {
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

const CustomTestTerminal = struct {
    const Self = @This();

    name: []const u8,

    fn fromString(string: []const u8) Self {
        return Self{ .name = string };
    }

    fn getString(self: Self) []const u8 {
        return self.name;
    }

    fn eql(self: Self, other: Self) bool {
        return std.mem.eql(u8, self.name, other.name);
    }
};

const TestVariable = struct {
    const Self = @This();

    name: []const u8,

    fn fromString(string: []const u8) Self {
        return TestVariable{ .name = string };
    }

    fn getString(self: Self) []const u8 {
        return self.name;
    }

    fn eql(self: Self, other: Self) bool {
        return std.mem.eql(u8, self.name, other.name);
    }
};

test "Grammar.initFromTuples [grammar1.0]" {
    // R0: S   -> wff
    // R1: wff -> Proposition
    // R2: wff -> Not    wff
    // R3: wff -> LParen wff And    wff RParen
    // R4: wff -> LParen wff Or     wff RParen
    // R5: wff -> LParen wff Cond   wff RParen
    // R6: wff -> LParen wff Bicond wff RParen
    //
    const V_S = 0;
    const V_WFF = 1;
    const T_PROPOSITION = 0;
    const T_NOT = 1;
    const T_LPAREN = 2;
    const T_AND = 3;
    const T_RPAREN = 4;
    const T_OR = 5;
    const T_COND = 6;
    const T_BICOND = 7;
    // $ = 10

    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);
    const actual_grammar = comptime G.initFromTuples(
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
    defer actual_grammar.deinit();

    const r0 = Production{ .lhs = .{ .variable_id = V_S }, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF }} };
    const r1 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{.{ .terminal_id = T_PROPOSITION }} };
    const r2 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_NOT }, .{ .variable_id = V_WFF } } };
    const r3 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_AND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r4 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_OR }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r5 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_COND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r6 = Production{ .lhs = .{ .variable_id = V_WFF }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_BICOND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };

    var expected_grammar = G{
        .allocator = null,
        .rules = &[_]Production{ r0, r1, r2, r3, r4, r5, r6 },
        .variables = &[_]TestVariable{ V("S"), V("wff") },
        .terminals = &[_]TestTerminal{ TestTerminal.Proposition, TestTerminal.Not, TestTerminal.LParen, TestTerminal.And, TestTerminal.RParen, TestTerminal.Or, TestTerminal.Cond, TestTerminal.Bicond, TestTerminal.End },
    };
    defer expected_grammar.deinit();

    try std.testing.expectEqualDeep(expected_grammar.rules, actual_grammar.rules);
    try std.testing.expectEqualDeep(expected_grammar.variables, actual_grammar.variables);
    try std.testing.expectEqualDeep(expected_grammar.terminals, actual_grammar.terminals);
}

test "Grammar.initFromTuples [grammar2.2]" {
    const V_S = 0;
    const V_WFF1 = 1;
    const V_WFF2 = 2;
    const V_WFF3 = 3;
    const V_WFF4 = 4;
    const V_PROP = 5;
    const T_BICOND = 0;
    const T_COND = 1;
    const T_OR = 2;
    const T_AND = 3;
    const T_NOT = 4;
    const T_LPAREN = 5;
    const T_RPAREN = 6;
    const T_PROPTOK = 7;

    // R0:  S -> wff1
    // R1:  wff1 -> wff2
    // R2:  wff1 -> wff1 <=> wff2
    // R3:  wff2 -> wff3
    // R4:  wff2 -> wff2 => wff3
    // R5:  wff3 -> wff4
    // R6:  wff3 -> wff3 v wff4
    // R7:  wff3 -> wff3 ^ wff4
    // R8:  wff4 -> prop
    // R9:  wff4 -> ~ wff4
    // R10: prop -> (wff1)
    // R11: prop -> PROPTOK

    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);

    const actual_grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{V("wff1")} },

            .{ V("wff1"), .{V("wff2")} },
            .{ V("wff1"), .{ V("wff1"), TestTerminal.Bicond, V("wff2") } },

            .{ V("wff2"), .{V("wff3")} },
            .{ V("wff2"), .{ V("wff2"), TestTerminal.Cond, V("wff3") } },

            .{ V("wff3"), .{V("wff4")} },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.Or, V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.And, V("wff4") } },

            .{ V("wff4"), .{V("prop")} },
            .{ V("wff4"), .{ TestTerminal.Not, V("wff4") } },

            .{ V("prop"), .{ TestTerminal.LParen, V("wff1"), TestTerminal.RParen } },
            .{ V("prop"), .{TestTerminal.Proposition} },
        },
        V("S"),
        TestTerminal.End,
    );
    defer actual_grammar.deinit();

    const r0 = Production{ .lhs = .{ .variable_id = V_S }, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF1 }} };
    const r1 = Production{ .lhs = .{ .variable_id = V_WFF1 }, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF2 }} };
    const r2 = Production{ .lhs = .{ .variable_id = V_WFF1 }, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF1 }, .{ .terminal_id = T_BICOND }, .{ .variable_id = V_WFF2 } } };
    const r3 = Production{ .lhs = .{ .variable_id = V_WFF2 }, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF3 }} };
    const r4 = Production{ .lhs = .{ .variable_id = V_WFF2 }, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF2 }, .{ .terminal_id = T_COND }, .{ .variable_id = V_WFF3 } } };
    const r5 = Production{ .lhs = .{ .variable_id = V_WFF3 }, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF4 }} };
    const r6 = Production{ .lhs = .{ .variable_id = V_WFF3 }, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF3 }, .{ .terminal_id = T_OR }, .{ .variable_id = V_WFF4 } } };
    const r7 = Production{ .lhs = .{ .variable_id = V_WFF3 }, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF3 }, .{ .terminal_id = T_AND }, .{ .variable_id = V_WFF4 } } };
    const r8 = Production{ .lhs = .{ .variable_id = V_WFF4 }, .rhs = &[_]SymbolId{.{ .variable_id = V_PROP }} };
    const r9 = Production{ .lhs = .{ .variable_id = V_WFF4 }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_NOT }, .{ .variable_id = V_WFF4 } } };
    const r10 = Production{ .lhs = .{ .variable_id = V_PROP }, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF1 }, .{ .terminal_id = T_RPAREN } } };
    const r11 = Production{ .lhs = .{ .variable_id = V_PROP }, .rhs = &[_]SymbolId{.{ .terminal_id = T_PROPTOK }} };

    var expected_grammar = G{
        .allocator = null,
        .rules = &[_]Production{ r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 },
        .variables = &[_]TestVariable{ V("S"), V("wff1"), V("wff2"), V("wff3"), V("wff4"), V("prop") },
        .terminals = &[_]TestTerminal{ .Bicond, .Cond, .Or, .And, .Not, .LParen, .RParen, .Proposition, .End },
    };
    defer expected_grammar.deinit();

    try std.testing.expectEqualDeep(expected_grammar.rules, actual_grammar.rules);
    try std.testing.expectEqualDeep(expected_grammar.variables, actual_grammar.variables);
    try std.testing.expectEqualDeep(expected_grammar.terminals, actual_grammar.terminals);
}

test "firsts_and_follows [grammar1.0]" {
    const V = TestVariable.fromString;
    const grammar = comptime Grammar(TestVariable, TestTerminal).initFromTuples(.{
        .{ V("S"), .{V("wff")} },
        .{ V("wff"), .{TestTerminal.Proposition} },
        .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
    }, V("S"), TestTerminal.End);
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_firsts = [_]bool{
        true, true, true, false, false, false, false, false, false,
        true, true, true, false, false, false, false, false, false,
    };

    try std.testing.expectEqualSlices(bool, &expected_firsts, first_set);
    try std.testing.expectEqualSlices(bool, &expected_firsts, &first_set_comptime);

    const follow_set = try grammar.getFollowSet(allocator);
    defer allocator.free(follow_set);

    const follow_set_comptime = comptime grammar.getFollowSetComptime();

    const expected_follow = [_]bool{
        false, false, false, false, false, false, false, false, true,
        false, false, false, true,  true,  true,  true,  true,  true,
    };

    try std.testing.expectEqualSlices(bool, &expected_follow, follow_set);
    try std.testing.expectEqualSlices(bool, &expected_follow, &follow_set_comptime);

    // debug.print("\n", .{});
    // for (follow, 0..) |list, i| {
    //     debug.print("({d}):", .{i});
    //     for (list, grammar.variables.len..) |isFollow, j| {
    //         if (isFollow) {
    //             debug.print(" {d}", .{j});
    //         }
    //     }
    //     debug.print("\n", .{});
    // }
}

test "firsts_and_follows [grammar2.2]" {
    // R0:  S -> wff1
    // R1:  wff1 -> wff2
    // R2:  wff1 -> wff1 <=> wff2
    // R3:  wff2 -> wff3
    // R4:  wff2 -> wff2 => wff3
    // R5:  wff3 -> wff4
    // R6:  wff3 -> wff3 v wff4
    // R7:  wff3 -> wff3 ^ wff4
    // R8:  wff4 -> prop
    // R9:  wff4 -> ~ wff4
    // R10: prop -> (wff1)
    // R11: prop -> PROPTOK
    @setEvalBranchQuota(10000);

    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{V("wff1")} },

            .{ V("wff1"), .{V("wff2")} },
            .{ V("wff1"), .{ V("wff1"), TestTerminal.Bicond, V("wff2") } },

            .{ V("wff2"), .{V("wff3")} },
            .{ V("wff2"), .{ V("wff2"), TestTerminal.Cond, V("wff3") } },

            .{ V("wff3"), .{V("wff4")} },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.Or, V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.And, V("wff4") } },

            .{ V("wff4"), .{V("prop")} },
            .{ V("wff4"), .{ TestTerminal.Not, V("wff4") } },

            .{ V("prop"), .{ TestTerminal.LParen, V("wff1"), TestTerminal.RParen } },
            .{ V("prop"), .{TestTerminal.Proposition} },
        },
        V("S"),
        TestTerminal.End,
    );
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_firsts = [_]bool{
        false, false, false, false, true,  true, false, true, false,
        false, false, false, false, true,  true, false, true, false,
        false, false, false, false, true,  true, false, true, false,
        false, false, false, false, true,  true, false, true, false,
        false, false, false, false, true,  true, false, true, false,
        false, false, false, false, false, true, false, true, false,
    };
    try std.testing.expectEqualSlices(bool, &expected_firsts, first_set);
    try std.testing.expectEqualSlices(bool, &expected_firsts, &first_set_comptime);

    const follow_set = try grammar.getFollowSet(allocator);
    defer allocator.free(follow_set);

    const follow_set_comptime = comptime grammar.getFollowSetComptime();

    const expected_follow = [_]bool{
        false, false, false, false, false, false, false, false, true,
        true,  false, false, false, false, false, true,  false, true,
        true,  true,  false, false, false, false, true,  false, true,
        true,  true,  true,  true,  false, false, true,  false, true,
        true,  true,  true,  true,  false, false, true,  false, true,
        true,  true,  true,  true,  false, false, true,  false, true,
    };
    try std.testing.expectEqualSlices(bool, &expected_follow, follow_set);
    try std.testing.expectEqualSlices(bool, &expected_follow, &follow_set_comptime);

    // debug.print("\n", .{});
    // for (follow, 0..) |list, i| {
    //     debug.print("({d}):", .{i});
    //     for (list, grammar.variables.len..) |isFollow, j| {
    //         if (isFollow) {
    //             debug.print(" {d}", .{j});
    //         }
    //     }
    //     debug.print("\n", .{});
    // }
}

fn tableFromTuples(
    comptime tuples: anytype,
    comptime Variable: type,
    comptime Terminal: type,
    grammar: Grammar(Variable, Terminal),
) [grammar.getVariableCount() * grammar.getTerminalCount()]bool {
    comptime {
        var first_set = [_]bool {false} ** (grammar.getVariableCount() * grammar.getTerminalCount());
        var first_set_2d_view = utils.Slice2d([]bool).init(&first_set, grammar.getTerminalCount());

        for (tuples) |tuple| {
            const variable = tuple.@"0";
            const v_id = grammar.getSymbolIdFromVariable(variable).?.variable_id;

            const terminals = tuple.@"1";
            for (std.meta.fieldNames(@TypeOf(terminals))) |rhs_tuple_field_name| {
                const terminal = @field(terminals, rhs_tuple_field_name);
                if (@TypeOf(terminal) != Terminal) {
                    @compileError("rhs of tuple must only contain Terminals");
                }

                const t_id = grammar.getSymbolIdFromTerminal(terminal).?.terminal_id;

                first_set_2d_view.row(v_id)[t_id] = true;
            }
        }
        return first_set;
    }
}

test "first_and_follows [custom1]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const T = CustomTestTerminal.fromString;
    const G = Grammar(TestVariable, CustomTestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("B"), .{ T("#") } },
            .{ V("B"), .{ T("("), V("A"), T(")") } },
            .{ V("A"), .{ V("B") } },
            .{ V("A"), .{ T("~"), V("A") } },
            .{ V("S"), .{ V("A") } },
        },
        V("S"),
        T("$"),
    );
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime tableFromTuples(
        .{
            .{ V("S"), .{ T("("), T("#"), T("~") } },
            .{ V("A"), .{ T("("), T("#"), T("~") } },
            .{ V("B"), .{ T("("), T("#") } },
        },
        TestVariable,
        CustomTestTerminal,
        grammar
    );

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom2]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const T = CustomTestTerminal.fromString;
    const G = Grammar(TestVariable, CustomTestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("A") } },

            .{ V("A"), .{ T("c"), V("B") } },
            .{ V("A"), .{ T("a") } },

            .{ V("B"), .{ V("C"), T("b") } },

            .{ V("C"), .{ V("D") } },
            .{ V("C"), .{ V("A"), T("d") } },

            .{ V("D"), .{ T("q") } },
        },
        V("S"),
        T("$"),
    );
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime tableFromTuples(
        .{
            .{ V("S"), .{ T("c"), T("a") } },
            .{ V("A"), .{ T("c"), T("a") } },
            .{ V("B"), .{ T("c"), T("a"), T("q") } },
            .{ V("C"), .{ T("c"), T("a"), T("q") } },
            .{ V("D"), .{ T("q") } },
        },
        TestVariable,
        CustomTestTerminal,
        grammar
    );

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom3]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const T = CustomTestTerminal.fromString;
    const G = Grammar(TestVariable, CustomTestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{V("A")} },

            .{ V("A"), .{ T("c"), V("B") } },
            .{ V("A"), .{V("Q")} },
            .{ V("A"), .{T("a")} },

            .{ V("B"), .{ V("C"), T("b") } },

            .{ V("C"), .{ V("A"), T("d") } },
            .{ V("C"), .{V("D")} },

            .{ V("D"), .{T("q")} },
            .{ V("Q"), .{T("z")} },
        },
        V("S"),
        T("$"),
    );
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime tableFromTuples(.{
        .{ V("S"), .{ T("c"), T("a"), T("z") } },
        .{ V("A"), .{ T("c"), T("a"), T("z") } },
        .{ V("B"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("C"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("D"), .{T("q")} },
        .{ V("Q"), .{T("z")} },
    }, TestVariable, CustomTestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom4]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const T = CustomTestTerminal.fromString;
    const G = Grammar(TestVariable, CustomTestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{V("A")} },
            .{ V("A"), .{ T("c"), V("B") } },
            .{ V("A"), .{V("Q")} },
            .{ V("A"), .{T("a")} },

            .{ V("B"), .{ V("C"), T("b") } },

            .{ V("C"), .{ V("A"), T("d") } },
            .{ V("C"), .{V("D")} },

            .{ V("D"), .{T("q")} },
            .{ V("Q"), .{T("z")} },
        },
        V("S"),
        T("$"),
    );
    defer grammar.deinit();

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime tableFromTuples(.{
        .{ V("S"), .{ T("a"), T("z") } },
        .{ V("A"), .{ T("a"), T("z") } },
        .{ V("S"), .{ T("c"), T("a"), T("z") } },
        .{ V("A"), .{ T("c"), T("a"), T("z") } },
        .{ V("B"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("C"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("D"), .{T("q")} },
        .{ V("Q"), .{T("z")} },
    }, TestVariable, CustomTestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

pub fn ParseTable(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const Self = @This();
        const GrammarType = Grammar(Variable, Terminal);
        const Action = union(enum) {
            state: StateIdx,
            reduce: usize, // index of grammar.rules
            invalid,
            accept,
        };

        pub const StateIdx = usize;

        allocator: ?std.mem.Allocator,
        grammar: GrammarType,
        goto_table: []const []const Action,
        action_table: []const []const Action,

        pub fn init(allocator: std.mem.Allocator, grammar: GrammarType) !Self {
            const goto_table, const action_table = try generateTables(allocator, grammar);
            return Self{
                .allocator = allocator,
                .grammar = grammar,
                .goto_table = goto_table,
                .action_table = action_table,
            };
        }

        pub fn initComptime(comptime grammar: GrammarType) Self {
            comptime {
                @setEvalBranchQuota(10000);
                const goto_table, const action_table = generateTablesComptime(grammar);
                return Self{
                    .allocator = null,
                    .grammar = grammar,
                    .goto_table = goto_table,
                    .action_table = action_table,
                };
            }
        }

        /// Note: Does NOT free the memory associated with the grammar
        pub fn deinit(self: Self) void {
            if (self.allocator) |allocator| {
                for (self.goto_table, self.action_table) |goto_row, action_row| {
                    allocator.free(goto_row);
                    allocator.free(action_row);
                }
                allocator.free(self.goto_table);
                allocator.free(self.action_table);
            }
        }

        pub fn getStartState(_: Self) StateIdx {
            return 0;
        }

        // pub fn lookupTerminal(self: Self, state: StateIdx, terminal: Terminal) Action {
        //     const terminal_idx = self.grammar.getSymbolFromTerminal(terminal).?.terminal;
        //     return self.action_table[state][terminal_idx];
        // }

        pub fn lookupSymbol(self: Self, state: StateIdx, symbol: SymbolId) Action {
            return switch (symbol) {
                .terminal_id => |t_id| self.action_table[state][t_id],
                .variable_id => |v_id| self.goto_table[state][v_id],
            };
        }

        pub fn lookupVariable(self: Self, state: StateIdx, variable: Variable) ?Action {
            const symbol = self.grammar.getSymbolIdFromVariable(variable) orelse return null;
            return self.lookupSymbol(state, symbol);
        }

        pub fn lookupTerminal(self: Self, state: StateIdx, terminal: Terminal) ?Action {
            const symbol = self.grammar.getSymbolIdFromTerminal(terminal) orelse return null;
            return self.lookupSymbol(state, symbol);
        }

        fn printDebugTable(self: Self) void {
            const COL_SPACE = "4";
            debug.print("\n{s: ^" ++ COL_SPACE ++ "} ||", .{""});
            for (self.grammar.terminals) |t| {
                debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{t.getString()});
            }
            debug.print("|", .{});
            for (self.grammar.variables) |v| {
                debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{v.getString()});
            }
            debug.print("|", .{});

            for (self.action_table, self.goto_table, 0..) |action_row, goto_row, s| {
                debug.print("\n{d: >" ++ COL_SPACE ++ "} ||", .{s});
                for (action_row) |entry| switch (entry) {
                    .state => |state_num| debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                debug.print("|", .{});
                for (goto_row) |entry| switch (entry) {
                    .state => |state_num| debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                debug.print("| {d: <" ++ COL_SPACE ++ "}", .{s});
            }
            debug.print("\n", .{});
        }

        fn expandProductions(allocator: std.mem.Allocator, grammar: GrammarType, productions: []const ProductionInstance) !struct { []std.ArrayList(ProductionInstance), []std.ArrayList(ProductionInstance) } {
            // const?
            var variable_branches = try allocator.alloc(std.ArrayList(ProductionInstance), grammar.getVariableCount());
            errdefer allocator.free(variable_branches);

            for (0..variable_branches.len) |i| {
                variable_branches[i] = std.ArrayList(ProductionInstance).empty;
            }
            errdefer {
                for (0..variable_branches.len) |i| {
                    variable_branches[i].deinit(allocator);
                }
                allocator.free(variable_branches);
            }

            var terminal_branches = try allocator.alloc(std.ArrayList(ProductionInstance), grammar.getTerminalCount());
            errdefer allocator.free(terminal_branches);

            for (0..terminal_branches.len) |i| {
                terminal_branches[i] = std.ArrayList(ProductionInstance).empty;
            }
            errdefer {
                for (0..terminal_branches.len) |i| {
                    terminal_branches[i].deinit(allocator);
                }
                allocator.free(terminal_branches);
            }

            var stack = std.ArrayList(ProductionInstance).empty;
            defer stack.deinit(allocator);

            try stack.appendSlice(allocator, productions);

            // Expand all given ProductionInstances and track all of the symbols
            // currently being read.
            while (stack.pop()) |prod| {
                if (prod.readCursor()) |sym| {
                    switch (sym) {
                        .variable_id => |id| {
                            // If the variable has not been encountered yet,
                            // expand it by pushing any productions from it onto
                            // the stack.
                            if (variable_branches[id].items.len == 0) {
                                for (grammar.rules) |rule| {
                                    if (sym.eql(rule.lhs)) {
                                        try stack.append(allocator, ProductionInstance.fromProduction(rule));
                                    }
                                }
                            }
                            // Add the variable as a branch.
                            try variable_branches[id].append(allocator, prod.copyAdvanceCursor());
                        },
                        .terminal_id => |id| try terminal_branches[id].append(allocator, prod.copyAdvanceCursor()),
                    }
                }
            }

            return .{ variable_branches, terminal_branches };
        }

        fn expandProductionsComptime(comptime grammar: GrammarType, comptime productions: []const ProductionInstance) !struct { []const []const ProductionInstance, []const []const ProductionInstance } {
            var variable_branches = [_][]const ProductionInstance {
                &[_]ProductionInstance {},
            } ** grammar.getVariableCount();

            var terminal_branches = [_][]const ProductionInstance {
                &[_]ProductionInstance {},
            } ** grammar.getTerminalCount();

            var stack: []const ProductionInstance = &[_]ProductionInstance{};

            for (productions) |instance| {
                stack = stack ++ &[_]ProductionInstance {instance};
            }

            // Expand all given ProductionInstances and track all of the symbols
            // currently being read.
            while (stack.len > 0) {
                const prod = stack[stack.len - 1];
                stack = stack[0 .. stack.len - 1];

                if (prod.readCursor()) |sym| {
                    switch (sym) {
                        .variable_id => |id| {
                            // If the variable has not been encountered yet,
                            // expand it by pushing any productions from it onto
                            // the stack.
                            if (variable_branches[id].len == 0) {
                                for (grammar.rules) |rule| {
                                    if (sym.eql(rule.lhs)) {
                                        stack = stack ++ &[_]ProductionInstance {ProductionInstance.fromProduction(rule)};
                                    }
                                }
                            }
                            // Add the variable as a branch.
                            // const new = variable_branches[idx] ++ &[_]ProductionInstance {prod.copyAdvanceCursor()};
                            // variable_branches = variable_branches[0..idx] ++ &[_][]const ProductionInstance {new} ++ variable_branches[(idx + 1)..variable_branches.len];
                            variable_branches[id] = variable_branches[id] ++ &[_]ProductionInstance {prod.copyAdvanceCursor()};
                        },
                        .terminal_id => |id| terminal_branches[id] = terminal_branches[id] ++ &[_]ProductionInstance {prod.copyAdvanceCursor()},
                    }
                }
            }

            return .{ &variable_branches, &terminal_branches };
        }

        fn checkStateAlreadyExists(starting_productions_table: []const []const ProductionInstance, productions: []const ProductionInstance) ?usize {
            for (starting_productions_table, 0..) |start_prod_list, state| {
                for (productions) |prod| {
                    for (start_prod_list) |start_prod| {
                        if (prod.eql(start_prod)) break;
                    } else {
                        break;
                    }
                } else {
                    return state;
                }
            }

            return null;
        }

        fn generateTables(allocator: std.mem.Allocator, grammar: GrammarType) !struct { [][]Action, [][]Action } {
            var goto_table = std.ArrayList([]Action).empty;
            defer goto_table.deinit(allocator);
            errdefer for (goto_table.items) |row| {
                allocator.free(row);
            };
            var action_table = std.ArrayList([]Action).empty;
            defer action_table.deinit(allocator);
            errdefer for (action_table.items) |row| {
                allocator.free(row);
            };
            var primary_productions_table = std.ArrayList([]ProductionInstance).empty;
            defer {
                for (primary_productions_table.items) |row| {
                    allocator.free(row);
                }
                primary_productions_table.deinit(allocator);
            }

            try goto_table.append(allocator, try allocator.alloc(Action, grammar.getVariableCount()));
            try action_table.append(allocator, try allocator.alloc(Action, grammar.getTerminalCount()));
            try primary_productions_table.append(allocator, try allocator.alloc(ProductionInstance, 1));
            primary_productions_table.items[0][0] = ProductionInstance.fromProduction(grammar.rules[grammar.getStartRuleId()]);

            var state: usize = 0;
            while (state < goto_table.items.len) : (state += 1) {
                const variable_branches, const terminal_branches = try expandProductions(allocator, grammar, primary_productions_table.items[state]);
                defer {
                    for (0..variable_branches.len) |i| {
                        variable_branches[i].deinit(allocator);
                    }
                    for (0..terminal_branches.len) |i| {
                        terminal_branches[i].deinit(allocator);
                    }
                    allocator.free(variable_branches);
                    allocator.free(terminal_branches);
                }

                for (variable_branches, 0..) |*prod_list, v_id| {
                    // If there are no transitions from this variable, mark
                    // this cell as invalid.
                    if (prod_list.items.len == 0) {
                        goto_table.items[state][v_id] = Action.invalid;
                        // If expanding these productions would result in a state
                        // that already exists,
                    } else if (checkStateAlreadyExists(primary_productions_table.items, prod_list.items)) |existing_state| {
                        goto_table.items[state][v_id] = try switch (goto_table.items[state][v_id]) {
                            .invalid => Action{ .state = existing_state },
                            .state => TableGeneratorError.shiftShiftError,
                            .reduce => TableGeneratorError.shiftReduceError,
                            .accept => TableGeneratorError.shiftAcceptError,
                        };
                    } else {
                        try goto_table.append(allocator, try allocator.alloc(Action, grammar.getVariableCount()));
                        try action_table.append(allocator, try allocator.alloc(Action, grammar.getTerminalCount()));
                        try primary_productions_table.append(allocator, try prod_list.toOwnedSlice(allocator));
                        goto_table.items[state][v_id] = Action{ .state = goto_table.items.len - 1 };
                    }
                }
                for (terminal_branches, 0..) |*prod_list, t_id| {
                    // If there are no transitions from this variable, mark
                    // this cell as invalid.
                    if (prod_list.items.len == 0) {
                        action_table.items[state][t_id] = Action.invalid;
                    // If expanding these productions would result in a state
                    // that already exists,
                    } else if (checkStateAlreadyExists(primary_productions_table.items, prod_list.items)) |existing_state| {
                        action_table.items[state][t_id] = try switch (action_table.items[state][t_id]) {
                            .invalid => Action{ .state = existing_state },
                            .state => TableGeneratorError.shiftShiftError,
                            .reduce => TableGeneratorError.shiftReduceError,
                            .accept => TableGeneratorError.shiftAcceptError,
                        };
                    } else {
                        try goto_table.append(allocator, try allocator.alloc(Action, grammar.getVariableCount()));
                        try action_table.append(allocator, try allocator.alloc(Action, grammar.getTerminalCount()));
                        try primary_productions_table.append(allocator, try prod_list.toOwnedSlice(allocator));
                        action_table.items[state][t_id] = Action{ .state = action_table.items.len - 1 };
                    }
                }
            }

            const follow_set = try grammar.getFollowSet(allocator);
            defer allocator.free(follow_set);

            // Populate reductions
            // For each completed primary production in each state, identify the
            // production rule's index and insert a reduction on each of the LHS's
            // follow set
            for (primary_productions_table.items, 0..) |row, state_num| {
                for (row) |instance| {
                    if (instance.readCursor() != null) continue;

                    const rule_id = grammar.getRuleId(instance.production).?;
                    for (0..grammar.getTerminalCount()) |t_id| {
                        if (!follow_set[instance.production.lhs.variable_id * grammar.getTerminalCount() + t_id]) continue;

                        action_table.items[state_num][t_id] = try switch (action_table.items[state_num][t_id]) {
                            .invalid => Action{ .reduce = rule_id },
                            .state => TableGeneratorError.shiftReduceError,
                            .reduce => TableGeneratorError.reduceReduceError,
                            .accept => TableGeneratorError.reduceAcceptError,
                        };
                    }

                    // TODO: hardcoded 0 kinda yucky
                    if (instance.production.lhs.variable_id == grammar.getStartSymbolId().variable_id) {
                        switch (action_table.items[state_num][grammar.getEndSymbolId().terminal_id]) {
                            .invalid => return TableGeneratorError.acceptError,
                            .state => return TableGeneratorError.shiftAcceptError,
                            .reduce => |reduction_rule_id| {
                                if (reduction_rule_id == grammar.getStartRuleId()) {
                                    action_table.items[state_num][grammar.getEndSymbolId().terminal_id] = Action.accept;
                                } else {
                                    return TableGeneratorError.acceptError;
                                }
                            },
                            .accept => {},
                        }
                    }
                }
            }
            return .{ try goto_table.toOwnedSlice(allocator), try action_table.toOwnedSlice(allocator) };
        }

        fn generateTablesComptime(comptime grammar: GrammarType) struct { []const []const Action, []const []const Action } {
            comptime {
                var goto_table: []const []const Action = &[_][]const Action {
                    &[_]Action {Action {.invalid = {}}} ** grammar.getVariableCount(),
                };

                var action_table: []const []const Action = &[_][]const Action {
                    &[_]Action {Action {.invalid = {}}} ** grammar.getTerminalCount(),
                };

                var primary_productions_table: []const []const ProductionInstance = &[_][]const ProductionInstance {
                    &[_]ProductionInstance{ProductionInstance.fromProduction(grammar.rules[grammar.getStartRuleId()])},
                };

                var state_num: usize = 0;
                while (state_num < goto_table.len) : (state_num += 1) {
                    const variable_branches, const terminal_branches = try expandProductionsComptime(grammar, primary_productions_table[state_num]);

                    for (variable_branches, 0..) |prod_list, v_id| {
                        // If there are no transitions from this variable, move on
                        // (cell is initialized to invalid so we don't need to set
                        // it here)
                        if (prod_list.len == 0) {
                            continue;
                        }

                        // If expanding these productions would result in a state
                        // that already exists,
                        else if (checkStateAlreadyExists(primary_productions_table, prod_list)) |existing_state| {
                            const new_action = switch (goto_table[state_num][v_id]) {
                                .invalid => Action{ .state = existing_state },
                                .state => @compileError("Parsing error: shift shift conflict"),
                                .reduce => @compileError("Parsing error: shift reduce conflict"),
                                .accept => @compileError("Parsing error: shift accept error"),
                            };

                            // Gross horrible disgusting pattern so that we can
                            // "assign" new values to the entries of the table.
                            // Essentially recreating the table with the entry
                            // to be assigned replaced with the desired new
                            // entry. Probably very inefficient but it's
                            // comptime so who cares.
                            const new_row = goto_table[state_num][0..v_id] ++ [_]Action { new_action } ++ goto_table[state_num][(v_id + 1)..goto_table[state_num].len];
                            goto_table = goto_table[0..state_num] ++ [_][]const Action {new_row} ++ goto_table[(state_num + 1)..goto_table.len];
                        } else {
                            goto_table = goto_table ++ [_][]const Action{ &[_]Action {Action{.invalid = {}}} ** grammar.getVariableCount() };
                            action_table = action_table ++ [_][]const Action{ &[_]Action {Action{.invalid = {}}} ** grammar.getTerminalCount() };
                            primary_productions_table = primary_productions_table ++ [_][]const ProductionInstance{ prod_list };

                            const new_row = goto_table[state_num][0..v_id] ++ [_]Action {Action {.state = goto_table.len - 1 } } ++ goto_table[state_num][(v_id + 1)..goto_table[state_num].len];
                            goto_table = goto_table[0..state_num] ++ [_][]const Action {new_row} ++ goto_table[(state_num + 1)..goto_table.len];
                        }
                    }
                    // @compileLog(goto_table);
                    for (terminal_branches, 0..) |prod_list, t_id| {
                        // If there are no transitions from this variable, move on
                        // (cell is initialized to invalid so we don't need to set
                        // it here)
                        if (prod_list.len == 0) {
                            continue;
                        }

                        // If expanding these productions would result in a state
                        // that already exists,
                        if (checkStateAlreadyExists(primary_productions_table, prod_list)) |existing_state| {
                            const new_action = switch (action_table[state_num][t_id]) {
                                .invalid => Action{ .state = existing_state },
                                .state => @compileError("Parsing error: shift shift conflict"),
                                .reduce => @compileError("Parsing error: shift reduce conflict"),
                                .accept => @compileError("Parsing error: shift accept error"),
                            };
                            const new_row = action_table[state_num][0..t_id] ++ [_]Action { new_action } ++ action_table[state_num][(t_id + 1)..action_table[state_num].len];
                            action_table = action_table[0..state_num] ++ [_][]const Action {new_row} ++ action_table[(state_num + 1)..action_table.len];
                        } else {
                            goto_table = goto_table ++ [_][]const Action{ &[_]Action {Action{.invalid = {}}} ** grammar.getVariableCount() };
                            action_table = action_table ++ [_][]const Action{ &[_]Action {Action{.invalid = {}}} ** grammar.getTerminalCount() };
                            primary_productions_table = primary_productions_table ++ [_][]const ProductionInstance{ prod_list };

                            const new_row = action_table[state_num][0..t_id] ++ [_]Action {Action {.state = action_table.len - 1 } } ++ action_table[state_num][(t_id + 1)..action_table[state_num].len];
                            action_table = action_table[0..state_num] ++ [_][]const Action {new_row} ++ action_table[(state_num + 1)..action_table.len];
                        }
                    }
                }

                const follow_set = grammar.getFollowSetComptime();

                // Populate reductions
                // For each completed primary production in each state, identify the
                // production rule's index and insert a reduction on each of the LHS's
                // follow set
                // TODO: Make separate function so we can use state_num instead of state_num_
                for (primary_productions_table, 0..) |row, state_num_| {
                    for (row) |instance| {
                        if (instance.readCursor() != null) continue;

                        const rule_id = grammar.getRuleId(instance.production).?;
                        for (0..grammar.getTerminalCount()) |t_id| {
                            if (!follow_set[instance.production.lhs.variable_id * grammar.getTerminalCount() + t_id]) continue;

                            const new_action = switch (action_table[state_num_][t_id]) {
                                .invalid => Action{ .reduce = rule_id },
                                .state => @compileError("Parsing error: shift reduce error"),
                                .reduce => @compileError("Parsing error: reduce reduce error"),
                                .accept => @compileError("Parsing error: reduce accept error"),
                            };
                            const new_row = action_table[state_num_][0..t_id] ++ [_]Action { new_action } ++ action_table[state_num_][(t_id + 1)..action_table[state_num_].len];
                            action_table = action_table[0..state_num_] ++ [_][]const Action {new_row} ++ action_table[(state_num_ + 1)..action_table.len];
                        }

                        // TODO: hardcoded 0 kinda yucky
                        if (instance.production.lhs.variable_id == grammar.getStartSymbolId().variable_id) {
                            switch (action_table[state_num_][grammar.getEndSymbolId().terminal_id]) {
                                .invalid => @compileError("Parsing error: missing accepting reduction"),
                                .state => @compileError("Parsing error: shift accept error"),
                                .reduce => |reduction_rule_id| {
                                    if (reduction_rule_id == grammar.getStartRuleId()) {
                                        const t_id = grammar.getEndSymbolId().terminal_id;
                                        const new_row = action_table[state_num_][0..t_id] ++ [_]Action { Action {.accept = {}} } ++ action_table[state_num_][(t_id + 1)..action_table[state_num_].len];
                                        action_table = action_table[0..state_num_] ++ [_][]const Action {new_row} ++ action_table[(state_num_ + 1)..action_table.len];
                                    } else {
                                        @compileError("Parsing error: the accepting state can only replace the starting production rule, found a different rule instead");
                                    }
                                },
                                .accept => {},
                            }
                        }
                    }
                }
                return .{ goto_table, action_table };
            }
        }
    };
}

test "ParseTable.expandProductions [grammar1.0]" {
    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);
    const grammar = comptime G.initFromTuples(.{
        .{ V("S"), .{V("wff")} },
        .{ V("wff"), .{TestTerminal.Proposition} },
        .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
    }, V("S"), TestTerminal.End);
    defer grammar.deinit();

    const P = ParseTable(TestVariable, TestTerminal);

    const expected_variable_branches = &[_][]const ProductionInstance {
        &[_]ProductionInstance {},
        &[_]ProductionInstance { .{.production = grammar.rules[0], .cursor = 1} },
    };

    const expected_terminal_branches = &[_][]const ProductionInstance {
        &[_]ProductionInstance { .{.production = grammar.rules[1], .cursor = 1} },
        &[_]ProductionInstance { .{.production = grammar.rules[2], .cursor = 1} },
        &[_]ProductionInstance {
            .{.production = grammar.rules[6], .cursor = 1},
            .{.production = grammar.rules[5], .cursor = 1},
            .{.production = grammar.rules[4], .cursor = 1},
            .{.production = grammar.rules[3], .cursor = 1},
        },
        &[_]ProductionInstance {},
        &[_]ProductionInstance {},
        &[_]ProductionInstance {},
        &[_]ProductionInstance {},
        &[_]ProductionInstance {},
        &[_]ProductionInstance {},
    };

    const start_productions = [_]ProductionInstance{ProductionInstance.fromProduction(grammar.rules[0])};
    const variable_branches, const terminal_branches = try P.expandProductions(std.testing.allocator, grammar, &start_productions);
    defer {
        for (0..variable_branches.len) |i| {
            variable_branches[i].deinit(std.testing.allocator);
        }
        for (0..terminal_branches.len) |i| {
            terminal_branches[i].deinit(std.testing.allocator);
        }
        std.testing.allocator.free(variable_branches);
        std.testing.allocator.free(terminal_branches);
    }
    for (expected_variable_branches, variable_branches) |expected, actual| {
        try std.testing.expectEqualSlices(ProductionInstance, expected, actual.items);
    }
    for (expected_terminal_branches, terminal_branches) |expected, actual| {
        try std.testing.expectEqualSlices(ProductionInstance, expected, actual.items);
    }

    // debug.print("\nVARIABLES:\n", .{});
    // for (variable_branches, 0..) |variable_prods, i| {
    //     debug.print("{d}\n", .{i});
    //     for (variable_prods.items) |p| {
    //         try grammar.printDebugProductionInstance(p);
    //     }
    // }
    // debug.print("\nTERMINALS:\n", .{});
    // for (terminal_branches, 0..) |terminal_prods, i| {
    //     debug.print("{d}\n", .{i});
    //     for (terminal_prods.items) |p| {
    //         try grammar.printDebugProductionInstance(p);
    //     }
    // }
}

test "Create parse table [grammar1.0]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);
    const grammar = comptime G.initFromTuples(.{
        .{ V("S"), .{V("wff")} },
        .{ V("wff"), .{TestTerminal.Proposition} },
        .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
    }, V("S"), TestTerminal.End);
    defer grammar.deinit();

    const P = ParseTable(TestVariable, TestTerminal);

    const expected_table = P {
        .allocator = null,
        .grammar = grammar,
        .goto_table = &[_][]const P.Action {
            &[_]P.Action { .{.invalid = {}}, .{.state = 1} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.state = 5} },
            &[_]P.Action { .{.invalid = {}}, .{.state = 6} },

            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.state = 11} },
            &[_]P.Action { .{.invalid = {}}, .{.state = 12} },
            &[_]P.Action { .{.invalid = {}}, .{.state = 13} },

            &[_]P.Action { .{.invalid = {}}, .{.state = 14} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },

            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}} },
        },
        .action_table = &[_][]const P.Action {
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.accept = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1} },
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },

            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 7}, .{.invalid = {}}, .{.state = 8}, .{.state = 9}, .{.state = 10},  .{.invalid = {}} },
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },

            &[_]P.Action { .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 15}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 16}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 17}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 18}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}} },

            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5} },
            &[_]P.Action { .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6} },
        }
    };

    const table = try P.init(std.testing.allocator, grammar);
    defer table.deinit();

    const table_comptime = comptime P.initComptime(grammar);
    defer table_comptime.deinit();

    try std.testing.expectEqualDeep(expected_table.goto_table, table.goto_table);
    try std.testing.expectEqualDeep(expected_table.action_table, table.action_table);

    try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);
}

test "Create parse table [grammar2.0]" {
    @setEvalBranchQuota(10000);
    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);
    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("wff1")} },

            .{ V("wff1"), .{ V("wff2")} },
            .{ V("wff1"), .{ V("wff1"), TestTerminal.Bicond, V("wff2") } },

            .{ V("wff2"), .{ V("wff3")} },
            .{ V("wff2"), .{ V("wff2"), TestTerminal.Cond, V("wff3") } },

            .{ V("wff3"), .{ V("wff4")} },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.Or, V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.And, V("wff4") } },

            .{ V("wff4"), .{ V("prop")} },
            .{ V("wff4"), .{ TestTerminal.Not, V("wff4") } },

            .{ V("prop"), .{ TestTerminal.LParen, V("wff1"), TestTerminal.RParen } },
            .{ V("prop"), .{ TestTerminal.Proposition} },
        },
        V("S"),
        TestTerminal.End,
    );
    defer grammar.deinit();

    const P = ParseTable(TestVariable, TestTerminal);

    const table = try P.init(std.testing.allocator, grammar);
    defer table.deinit();

    const table_comptime = comptime P.initComptime(grammar);
    defer table_comptime.deinit();

    // table.printDebugTable();

    try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);
}
