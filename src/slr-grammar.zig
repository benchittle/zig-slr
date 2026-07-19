const std = @import("std");

const test_common = @import("test-common.zig");
const utils = @import("utils.zig");

/// A numerical ID associated with a symbol in a formal grammar (a variable or a
/// terminal).
pub const SymbolId = union(enum) {
    const Self = @This();
    const VariableId = u16;
    const TerminalId = u16;

    variable_id: VariableId,
    terminal_id: TerminalId,

    pub fn eql(self: Self, other: Self) bool {
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

    pub fn eqlVariable(self: Self, other: VariableId) bool {
        return switch (self) {
            .variable_id => |id| id == other,
            .terminal_id => false,
        };
    }
};

/// A single rule / production in a formal grammar.
/// * `lhs` is the grammar variable on the left side of the production,
/// * `rhs` is the sequence of grammar variables and/or terminals on the right
///   side of the production (produced by the production)
pub const Production = struct {
    const Self = @This();

    lhs: SymbolId.VariableId,
    rhs: []const SymbolId,

    pub fn eql(self: Self, other: Self) bool {
        if (self.lhs != other.lhs) return false;
        if (self.rhs.len != other.rhs.len) return false;
        for (self.rhs, other.rhs) |sym1, sym2| {
            if (!sym1.eql(sym2)) return false;
        }

        return true;
    }

    /// Used for sorting productions so that those with a variable as the first
    /// symbol on the right of the production appear before those with a
    /// terminal as the first symbol. Each group is then also ordered by ID of
    /// the variable on the left side.
    fn lessThan(_: void, this: Self, other: Self) bool {
        return switch(this.rhs[0]) {
            .variable_id => switch (other.rhs[0]) {
                .variable_id => this.lhs < other.lhs,
                .terminal_id => true,
            },
            .terminal_id => switch(other.rhs[0]) {
                .variable_id => false,
                .terminal_id => this.lhs < other.lhs,
            }
        };
    }
};

// NOTE: variables ids MUST START AT 0 and MUST BE SMALLER THAN ALL TERMINAL IDS and MUST BE ORDERED
// NOTE: comparison of symbols is not always done using .eql in below functions, should try to make this consistent
// NOTE: FOLLOW and FIRST sets generation code is way too nested, should ideally
//       be broken down into smaller functions

/// Representation of a formal grammar for a language.
///
/// * `Variable` is the type that will be used to specify grammar variables /
///   non-terminals.
/// * `Terminal` is the type that will be used to specify grammar terminals.
///
/// Both types must define an equality function of the form
/// `pub fn eql(@This(), @This()) bool`
///
/// The returned struct has the following fields:
/// * `rules` is a slice of `Production`s (the rules of the grammar). It must be
///   sorted such that rules with a variable as the first symbol on the rhs
///   appear before those with a terminal. Within each group they must then be
///   sorted by symbol ID.
/// * `variables` is a slice containing all of the user defined `Variable`
///   objects found in the grammar rules. Each `Variable`'s symbol ID is its
///   index in the slice.
///   The start symbol will always be assigned variable symbol ID 0.
/// * `terminals` is the same idea as `variables` but for all of the user
///   defined `Terminal` objects found in the grammar rules.
///   The end terminal will always be assigned the final terminal symbol ID.
pub fn Grammar(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const Self = @This();

        rules: []const Production,
        variables: []const Variable,
        terminals: []const Terminal,

        /// Initialize a formal grammar at comptime using tuples.
        /// * `rule_tuples` is a nested tuple containing the productions of the
        ///   grammar. See the tests in this file for usage examples.
        /// * `start_variable` is the start variable of the grammar.
        /// * `end_terminal` is the terminal that will be used to mark the
        ///   end of a string during parsing.
        pub fn initFromTuples(
            comptime rule_tuples: anytype,
            comptime start_variable: Variable,
            comptime end_terminal: Terminal
        ) Self {
            comptime {
                // Initialize a grammar struct to populate.
                var grammar = Self{
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
                        rule.lhs = id.variable_id;
                    } else {
                        // If we haven't seen this variable yet, append it to
                        // the variables list.
                        rule.lhs = grammar.getVariableCount();
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

                // Kind of hacky workaround to be able to sort the rules after
                // we have them.
                var rules: [grammar.rules.len]Production = undefined;
                std.mem.copyForwards(Production, &rules, grammar.rules);
                std.mem.sortUnstable(Production, &rules, {}, Production.lessThan);
                const sorted_rules = rules;
                grammar.rules = &sorted_rules;

                return grammar;
            }
        }

        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.rules);
            allocator.free(self.variables);
            allocator.free(self.terminals);
        }

        /// Verify the structure and types of the given tuples. Return void
        /// since this will be done at comptime and all errors will be compiler
        /// errors.
        /// TODO: Consider removing
        fn verifyTuples(comptime rule_tuples: anytype) void {
            const RuleTuplesType = @TypeOf(rule_tuples);
            const rule_tuples_type_info = @typeInfo(RuleTuplesType);

            // Verify rule_tuples is a tuple (struct with no named fields).
            if (rule_tuples_type_info != .@"struct" or !rule_tuples_type_info.@"struct".is_tuple) {
                @compileError("Expected tuple of rules. Cannot use '" ++ @typeName(RuleTuplesType) ++ "'");
            }
            // Verify rule_tuples is not empty.
            if (std.meta.fields(RuleTuplesType).len == 0) {
                @compileError("rule_tuples cannot be empty");
            }

            // Verify each field in rule_tuples is a valid grammar rule.
            inline for (std.meta.fieldNames(RuleTuplesType), 0..) |rule_tuples_field_name, i| {
                const rule = @field(rule_tuples, rule_tuples_field_name);
                const RuleType = @TypeOf(rule);
                const rule_type_info = @typeInfo(RuleType);

                // Each rule should be a tuple.
                if (rule_type_info != .@"struct" or !rule_type_info.@"struct".is_tuple) {
                    @compileError(std.fmt.comptimePrint("Each rule must be a tuple, found '" ++ @typeName(rule) ++ "' (rule {d})", .{i}));
                }
                // Each rule should have exactly 2 fields.
                if (std.meta.fields(RuleType).len != 2) {
                    @compileError(std.fmt.comptimePrint("Each rule must have exactly 2 fields, found {d} fields (rule {d})", .{ rule_type_info.fields.len, i }));
                }

                // The first field of each rule should be of type Variable.
                const lhs = rule.@"0";
                if (@TypeOf(lhs) != Variable) {
                    @compileError(std.fmt.comptimePrint("The first field in each rule tuple must be of type '" ++ @typeName(Variable) ++ "', found '" ++ @typeName(@TypeOf(rule.@"0")) ++ "' (rule {d})", .{i}));
                }

                // The second field of each rule should be a tuple with fields
                // of type Variable or Terminal (the right hand side of a
                // production).
                const rhs = rule.@"1";
                const RhsType = @TypeOf(rhs);
                const rhs_type_info = @typeInfo(RhsType);

                // Verify rhs is a tuple (struct with no named fields).
                if (rhs_type_info != .@"struct" or !rhs_type_info.@"struct".is_tuple) {
                    @compileError(std.fmt.comptimePrint("The second field in each rule tuple must be a tuple, found '" ++ @typeName(RuleTuplesType) ++ "' (rule {d})", .{i}));
                }
                // Verify rhs is not empty
                if (std.meta.fields(RuleTuplesType).len == 0) {
                    @compileError(std.fmt.comptimePrint("The second field (a tuple) in each rule tuple cannot be empty (rule {d})", .{i}));
                }

                // Verify each symbol in rhs is of type Terminal or Variable.
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

        pub fn getStartSymbolId(_: Self) SymbolId {
            return SymbolId{ .variable_id = 0 };
        }

        pub fn getEndSymbolId(self: Self) SymbolId {
            return SymbolId{ .terminal_id = self.getTerminalCount() - 1 };
        }

        pub fn getStartRuleId(_: Self) usize {
            return 0;
        }

        pub fn getRule(self: Self, rule_id: usize) Production {
            return self.rules[rule_id];
        }

        /// Caller must provide buffers with the necessary room:
        /// * `first_set_table.slice: [self.getVariableCount() * self.getTerminalCount()]`
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
            first_var_edge_list_offsets: []usize,
            populated: []bool,
            path: []SymbolId.VariableId,
            path_edges_explored: []usize,
            visited: []bool,
        ) void {
            std.debug.assert(first_set_table.slice.len == self.getVariableCount() * self.getTerminalCount());
            std.debug.assert(first_var_edge_list_offsets.len == self.getVariableCount() + 1);
            std.debug.assert(populated.len == self.getVariableCount());
            std.debug.assert(path.len == self.getVariableCount());
            std.debug.assert(path_edges_explored.len == self.getVariableCount());
            std.debug.assert(visited.len == self.getVariableCount());

            @memset(first_set_table.slice, false);
            @memset(first_var_edge_list_offsets, 0);
            @memset(populated, false);

            // In this function, we want to think about our rules as a
            // directional graph. Each node represents a variable, and an edge
            // from nodes A to B exists if there is a grammar rule where
            // variable A produces symbol B as the first symbol.
            //
            // NOTE: From here on, grammar variables will be referred to as
            //       nodes in comments and variable names.
            //
            // The graph is represented using a pseudo compressed sparse row
            // format. In other words:
            // - self.rules: The edge list. It tells us which nodes are
            //   connected to which other nodes -- just look at the lhs and the
            //   first symbol on the rhs. To make look ups quick, they are
            //   assumed to be sorted in a specific way -- see the comments for
            //   Grammar().
            // - first_var_edge_list_offsets: Index offset for the start of each
            //   group of nodes in self.rules. We have to build this here.
            //
            // So if first_var_edge_list_offsets[2] = 5, then the edges for the
            // node with ID 2 can be found starting at index 5 of self.rules.

            // Since self.rules is sorted, we can get the number of edges in our
            // graph simply by iterating until we reach the first rule whose rhs
            // starts with a terminal (guaranteeing we've passed all rules whose
            // rhs starts with a variable).
            const total_edge_count = ret: for (self.rules, 0..) |rule, i| {
                switch (rule.rhs[0]) {
                    .terminal_id => break :ret i,
                    .variable_id => continue,
                }
            } else 0;

            // Populate first_var_edge_list_offsets as described above.
            {
                var current_key = self.rules[0].lhs;
                var offset: usize = 0;
                for (self.rules[0..total_edge_count], 0..) |rule, i| {
                    if (current_key != rule.lhs) {
                        offset = i;
                        current_key = rule.lhs;
                    }
                    first_var_edge_list_offsets[rule.lhs] = offset;
                }
            }

            // first_var_edge_list_offsets will be used to calculate the number
            // of edges from a given node like:
            // edges = offsets[i + 1] - offsets[i]
            // To avoid an edge case (heh) with the last node,
            // first_var_edge_list_offsets must be one longer than the number of
            // nodes, and the last entry must be the number of edges in the
            // graph.
            first_var_edge_list_offsets[first_var_edge_list_offsets.len - 1] = total_edge_count;

            // For the same reason, it is also helpful to propagate offsets
            // backwards for any nodes that don't have any edges.
            // So if node i has no edges originating from it, its offset will be
            // the same as node (i + 1), rather than 0.
            {
                var last_offset = total_edge_count;
                for (1..first_var_edge_list_offsets.len) |i| {
                    const node_id = first_var_edge_list_offsets.len - i - 1;
                    const offset = first_var_edge_list_offsets[node_id];
                    if (self.rules[offset].lhs != node_id) {
                        first_var_edge_list_offsets[node_id] = last_offset;
                    } else {
                        last_offset = offset;
                    }
                }
            }

            // Initialize first_set_table with terminals that appear as the
            // first symbol on the right side of a production. We will propagate
            // these in the next step.
            // (Start iterating from total_edge_count to skip past all the rules
            // whose rhs starts with a variable)
            for (self.rules[total_edge_count..]) |rule| {
                const var_id = rule.lhs;
                const first_rule_symbol_id = rule.rhs[0].terminal_id;
                first_set_table.row(var_id)[first_rule_symbol_id] = true;
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
            // fully propagated / populated.
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
                            const next_index = first_var_edge_list_offsets[current_node] + edges_explored;
                            const next_node = self.rules[next_index].rhs[0].variable_id;
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
                var first_var_edge_list_offsets_buffer: [self.getVariableCount() + 1]usize = undefined;
                var populated_buffer: [self.getVariableCount()]bool = undefined;
                var path_buffer: [self.getVariableCount()]SymbolId.VariableId = undefined;
                var path_edges_explored_buffer: [self.getVariableCount()]usize = undefined;
                var visited_buffer: [self.getVariableCount()]bool = undefined;

                self.computeFirstSet(
                    utils.Slice2d([]bool).init(&first_set_buffer, self.getTerminalCount()),
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
        ///
        /// Caller must also provide a **populated** `first_set` table.
        ///
        /// `follow_set` is populated with the resulting table, the other buffers
        /// can be freed immediately if they were dynamically allocated.
        fn computeFollowSet(
            self: Self,
            follow_set: utils.Slice2d([]bool),
            first_set: utils.Slice2d([]const bool),
        ) void {
            std.debug.assert(follow_set.slice.len >= self.getVariableCount() * self.getTerminalCount());
            std.debug.assert(first_set.slice.len >= self.getVariableCount() * self.getTerminalCount());

            @memset(follow_set.slice, false);

            // Initialize FOLLOW(startsymbol) to include the end terminal.
            follow_set.row(0)[follow_set.row_length - 1] = true;

            // Iterate through each rhs of each grammar rule. Whenever we come
            // across, a variable, look at the next symbol: if its a terminal,
            // add it to the variable's FOLLOW set; if it's another variable,
            // union its FIRST set into the current variable's FOLLOW set.
            for (self.rules) |rule| {
                for (rule.rhs[0..(rule.rhs.len - 1)], rule.rhs[1..rule.rhs.len]) |symbol_id, next_symbol_id| {
                    switch (symbol_id) {
                        .terminal_id => continue,
                        .variable_id => |v_id| switch (next_symbol_id) {
                            .terminal_id => |next_t_id| follow_set.row(v_id)[next_t_id] = true,
                            .variable_id => |next_v_id| utils.sliceUnion(follow_set.row(v_id), first_set.row(next_v_id)),
                        }
                    }
                }
            }

            // Propagate FOLLOW sets for any productions whose rhs ends with a
            // variable.
            for (self.rules) |rule| {
                const end_v_id = switch (rule.rhs[rule.rhs.len - 1]) {
                    .terminal_id => continue,
                    .variable_id => |v_id| v_id,
                };

                utils.rowUnion(follow_set, end_v_id, rule.lhs);
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
                first_var_edge_list_offsets_buffer,
                populated_buffer,
                path_buffer,
                path_edges_explored_buffer,
                visited_buffer,
            );

            const follow_set_buffer = try allocator.alloc(bool, self.getVariableCount() * self.getTerminalCount());
            errdefer allocator.free(follow_set_buffer);

            self.computeFollowSet(
                utils.Slice2d([]bool).init(follow_set_buffer, self.getTerminalCount()),
                utils.Slice2d([]const bool).init(first_set_buffer, self.getTerminalCount()),
            );
            return follow_set_buffer;
        }

        /// Comptime version of `getFollowSet()`, no dynamic allocation needed.
        pub fn getFollowSetComptime(comptime self: Self) [self.getVariableCount() * self.getTerminalCount()]bool {
            comptime {
                var first_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;
                var first_var_edge_list_offsets_buffer: [self.getVariableCount() + 1]usize = undefined;
                var populated_buffer: [self.getVariableCount()]bool = undefined;
                var path_buffer: [self.getVariableCount()]SymbolId.VariableId = undefined;
                var path_edges_explored_buffer: [self.getVariableCount()]usize = undefined;
                var visited_buffer: [self.getVariableCount()]bool = undefined;

                self.computeFirstSet(
                    utils.Slice2d([]bool).init(&first_set_buffer, self.getTerminalCount()),
                    &first_var_edge_list_offsets_buffer,
                    &populated_buffer,
                    &path_buffer,
                    &path_edges_explored_buffer,
                    &visited_buffer,
                );

                var follow_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;

                self.computeFollowSet(
                    utils.Slice2d([]bool).init(&follow_set_buffer, self.getTerminalCount()),
                    utils.Slice2d([]const bool).init(&first_set_buffer, self.getTerminalCount()),
                );
                return follow_set_buffer;
            }
        }
    };
}

test "Grammar.initFromTuples [grammar1.0]" {
    // R0: S   -> wff
    // R1: wff -> Proposition
    // R2: wff -> Not    wff
    // R3: wff -> LParen wff And    wff RParen
    // R4: wff -> LParen wff Or     wff RParen
    // R5: wff -> LParen wff Cond   wff RParen
    // R6: wff -> LParen wff Bicond wff RParen

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

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

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

    const r0 = Production{ .lhs = V_S, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF }} };
    const r1 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{.{ .terminal_id = T_PROPOSITION }} };
    const r2 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{ .{ .terminal_id = T_NOT }, .{ .variable_id = V_WFF } } };
    const r3 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_AND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r4 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_OR }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r5 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_COND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };
    const r6 = Production{ .lhs = V_WFF, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_BICOND }, .{ .variable_id = V_WFF }, .{ .terminal_id = T_RPAREN } } };

    const expected_grammar = G{
        .rules = &[_]Production{ r0, r1, r2, r3, r4, r5, r6 },
        .variables = &[_]TestVariable{ V("S"), V("wff") },
        .terminals = &[_]TestTerminal{ TestTerminal.Proposition, TestTerminal.Not, TestTerminal.LParen, TestTerminal.And, TestTerminal.RParen, TestTerminal.Or, TestTerminal.Cond, TestTerminal.Bicond, TestTerminal.End },
    };

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

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

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

    const r0 = Production{ .lhs = V_S, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF1 }} };
    const r1 = Production{ .lhs = V_WFF1, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF2 }} };
    const r2 = Production{ .lhs = V_WFF1, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF1 }, .{ .terminal_id = T_BICOND }, .{ .variable_id = V_WFF2 } } };
    const r3 = Production{ .lhs = V_WFF2, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF3 }} };
    const r4 = Production{ .lhs = V_WFF2, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF2 }, .{ .terminal_id = T_COND }, .{ .variable_id = V_WFF3 } } };
    const r5 = Production{ .lhs = V_WFF3, .rhs = &[_]SymbolId{.{ .variable_id = V_WFF4 }} };
    const r6 = Production{ .lhs = V_WFF3, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF3 }, .{ .terminal_id = T_OR }, .{ .variable_id = V_WFF4 } } };
    const r7 = Production{ .lhs = V_WFF3, .rhs = &[_]SymbolId{ .{ .variable_id = V_WFF3 }, .{ .terminal_id = T_AND }, .{ .variable_id = V_WFF4 } } };
    const r8 = Production{ .lhs = V_WFF4, .rhs = &[_]SymbolId{.{ .variable_id = V_PROP }} };
    const r9 = Production{ .lhs = V_WFF4, .rhs = &[_]SymbolId{ .{ .terminal_id = T_NOT }, .{ .variable_id = V_WFF4 } } };
    const r10 = Production{ .lhs = V_PROP, .rhs = &[_]SymbolId{ .{ .terminal_id = T_LPAREN }, .{ .variable_id = V_WFF1 }, .{ .terminal_id = T_RPAREN } } };
    const r11 = Production{ .lhs = V_PROP, .rhs = &[_]SymbolId{.{ .terminal_id = T_PROPTOK }} };

    const expected_grammar = G{
        .rules = &[_]Production{ r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11 },
        .variables = &[_]TestVariable{ V("S"), V("wff1"), V("wff2"), V("wff3"), V("wff4"), V("prop") },
        .terminals = &[_]TestTerminal{ .Bicond, .Cond, .Or, .And, .Not, .LParen, .RParen, .Proposition, .End },
    };

    try std.testing.expectEqualDeep(expected_grammar.rules, actual_grammar.rules);
    try std.testing.expectEqualDeep(expected_grammar.variables, actual_grammar.variables);
    try std.testing.expectEqualDeep(expected_grammar.terminals, actual_grammar.terminals);
}

test "firsts_and_follows [grammar1.0]" {
    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

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

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

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

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

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
        TestTerminal,
        grammar
    );

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom2]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

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
        TestTerminal,
        grammar
    );

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom3]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

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
    }, TestVariable, TestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}

test "first_and_follows [custom4]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

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
    }, TestVariable, TestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    try std.testing.expectEqualSlices(bool, &expected_first_set, &first_set_comptime);
}
