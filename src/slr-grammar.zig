const std = @import("std");

const comptime_allocator = @import("comptime-allocator.zig");
const test_common = @import("test-common.zig");
const utils = @import("utils.zig");

// TODO: model performance with tools from https://youtu.be/UJ_W0O3sFnY?si=Oo2_ld5CdcuyUFpu

/// A numerical ID associated with a symbol in a formal grammar (a variable or a
/// terminal).
pub const SymbolId = union(enum) {
    const Self = @This();
    // TODO: make this a single ID type
    const VariableId = u16;
    const TerminalId = u16;

    pub const ID_MAX = std.math.maxInt(VariableId);

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
///   side of the production (produced by the production).
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
};

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
/// * `rules` is a slice of `Production` objects (the rules of the grammar). It
///   must be sorted such that every rule with a variable as the first symbol on
///   the rhs appears before those with a terminal. Within each group they must
///   then be sorted by symbol ID.
/// * `state_count` is the number of states in the epsilon-NFA associated with
///   this grammar.
/// * `variables` is a slice containing all of the user defined `Variable`
///   objects found in the grammar rules. Each `Variable` object's symbol ID is
///   its index in the slice.
///   The start symbol will always be assigned variable symbol ID 0.
/// * `terminals` is the same idea as `variables` but for all of the user
///   defined `Terminal` objects found in the grammar rules.
///   The end terminal will always be assigned the final terminal symbol ID.
pub fn Grammar(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const GrammarType = @This();

        pub const NfaView = struct {
            pub const State = usize;

            grammar: *const GrammarType,

            /// Returns the number of states in the grammar's e-NFA
            /// representation.
            pub fn stateCount(self: NfaView) usize {
                return self.grammar.rules_rhs.data.len;
            }

            /// Returns the SymbolId being read in the given e-NFA state, or
            /// null if the state is the last state in a rule.
            pub fn symbolIdFromState(self: NfaView, state: State) ?SymbolId {
                const symbol_id = self.grammar.rules_rhs.data[state];
                if (GrammarType.SENTINEL.eql(symbol_id)) {
                    return null;
                }
                return symbol_id;
            }

            /// Finds the rule containing the given state and returns its ID.
            pub fn ruleIdFromState(self: NfaView, state: State) usize {
                return self.grammar.rules_rhs.findRow(state);
            }

            /// Returns the first e-NFA state for the given rule.
            pub fn firstStateFromRuleId(self: NfaView, rule_id: usize) State {
                return self.grammar.rules_rhs.row_offsets[rule_id];
            }
        };

        // TODO: If we could encode the row number into the sentinel values,
        // we could skip the reverse index on the ragged array
        pub const SENTINEL = SymbolId{ .variable_id = SymbolId.ID_MAX };

        rules_lhs: []const SymbolId.VariableId,
        // NOTE: there is a gap of size SymbolId between each rule so that this
        //       lines up with the NFA states
        rules_rhs: utils.RaggedArray(SymbolId, true),
        variables: []const Variable,
        terminals: []const Terminal,

        /// Initialize a formal grammar at comptime using tuples.
        /// * `rule_tuples` is a nested tuple containing the productions of the
        ///   grammar. See the tests in this file for usage examples.
        /// * `start_variable` is the start variable of the grammar.
        /// * `end_terminal` is the terminal that will be used to mark the
        ///   end of a string during parsing.
        pub fn initFromTuples(
            // TODO: make `start_variable` `start_rule` instead
            // to guqrantee no multiple start paths
            comptime rule_tuples: anytype,
            comptime start_variable: Variable,
            comptime end_terminal: Terminal,
        ) GrammarType {
            comptime {
                // Throws a compiler error if the structure or types of the
                // given tuples are invalid.
                verifyTuples(rule_tuples);

                var rules_lhs: [rule_tuples.len]SymbolId.VariableId = undefined;
                var rules_rhs: [rule_tuples.len][]const SymbolId = undefined;
                var variables: []const Variable = &[_]Variable{start_variable};
                var terminals: []const Terminal = &[_]Terminal{};
                var nfa_state_count = 0;

                // Iterate over each rule tuple and populate our grammar rules.
                for (rule_tuples, 0..) |rule_tuple, i| {
                    // Unpack the left hand side of the rule. We have already
                    // checked that it is of type Variable.
                    const lhs = rule_tuple.@"0";
                    if (getSymbolIdFromVariableSlice(lhs, variables)) |v| {
                        rules_lhs[i] = v.variable_id;
                    } else {
                        // If we haven't seen this variable yet, append it to
                        // the variables list.
                        rules_lhs[i] = @intCast(variables.len);
                        variables = variables ++ &[_]Variable{lhs};
                        if (variables.len == SymbolId.ID_MAX) {
                            @compileError("Too many variables");
                        }
                    }

                    // Iterate over the symbols on the right hand side of the
                    // rule tuple and unpack each into the grammar rule.
                    const rhs = rule_tuple.@"1";
                    var rhs_symbols: [rhs.len + 1]SymbolId = undefined;
                    for (std.meta.fieldNames(@TypeOf(rhs)), 0..) |rhs_tuple_field_name, j| {
                        const var_or_terminal = @field(rhs, rhs_tuple_field_name);
                        if (@TypeOf(var_or_terminal) == Variable) {
                            if (getSymbolIdFromVariableSlice(var_or_terminal, variables)) |v| {
                                rhs_symbols[j] = v;
                            } else {
                                // If we haven't seen this variable yet, append
                                // it to the variables list.
                                rhs_symbols[j] = .{ .variable_id = variables.len };
                                variables = variables ++ &[_]Variable{var_or_terminal};
                                if (variables.len == SymbolId.ID_MAX) {
                                    @compileError("Too many variables");
                                }
                            }
                        } else if (@TypeOf(var_or_terminal) == Terminal) {
                            if (getSymbolIdFromTerminalSlice(var_or_terminal, terminals)) |t| {
                                rhs_symbols[j] = t;
                            } else {
                                // If we haven't seen this terminal yet, append
                                // it to the terminals list.
                                rhs_symbols[j] = .{ .terminal_id = terminals.len };
                                terminals = terminals ++ &[_]Terminal{var_or_terminal};
                                if (terminals.len > SymbolId.ID_MAX) {
                                    @compileError("Too many terminals");
                                }
                            }
                        } else {
                            @compileError("Unexpected type in rhs (expected Variable or Terminal)");
                        }
                    }
                    nfa_state_count += rhs.len + 1;
                    rhs_symbols[rhs_symbols.len - 1] = SENTINEL;
                    rules_rhs[i] = &rhs_symbols;
                }
                terminals = terminals ++ &[_]Terminal{end_terminal};
                if (terminals.len > SymbolId.ID_MAX) {
                    @compileError("Too many terminals");
                }

                // Sort rules
                const SortContext = struct {
                    rules_lhs_: []SymbolId.VariableId,
                    rules_rhs_: [][]const SymbolId,

                    /// Productions with a variable as the first symbol on the
                    /// right of the production should appear before those with
                    /// a terminal as the first symbol. Each group should then
                    /// be ordered by ID of the variable on the left side.
                    pub fn lessThan(self: @This(), a: usize, b: usize) bool {
                        return switch (self.rules_rhs_[a][0]) {
                            .variable_id => switch (self.rules_rhs_[b][0]) {
                                .variable_id => self.rules_lhs_[a] < self.rules_lhs_[b],
                                .terminal_id => true,
                            },
                            .terminal_id => switch (self.rules_rhs_[b][0]) {
                                .variable_id => false,
                                .terminal_id => self.rules_lhs_[a] < self.rules_lhs_[b],
                            },
                        };
                    }

                    pub fn swap(self: @This(), a: usize, b: usize) void {
                        std.mem.swap(SymbolId.VariableId, &self.rules_lhs_[a], &self.rules_lhs_[b]);
                        std.mem.swap([]const SymbolId, &self.rules_rhs_[a], &self.rules_rhs_[b]);
                    }
                };
                std.sort.pdqContext(0, rule_tuples.len, SortContext{ .rules_lhs_ = &rules_lhs, .rules_rhs_ = &rules_rhs });

                // Convert the rhs array of slices to a ragged array.
                const RaggedArrayBuilder = utils.RaggedArray(SymbolId, true).RaggedArrayBuilder;
                var builder = RaggedArrayBuilder.initWithCapacityComptime(nfa_state_count, rule_tuples.len);
                for (rules_rhs) |rhs| {
                    for (rhs) |symbol| {
                        builder.appendAssumeCapacity(symbol);
                    }
                    builder.startNextRowAssumeCapacity();
                }

                const rules_lhs_final = rules_lhs;
                return .{
                    .rules_lhs = &rules_lhs_final,
                    .rules_rhs = builder.build(),
                    .terminals = terminals,
                    .variables = variables,
                };
            }
        }

        pub fn deinit(self: GrammarType, allocator: std.mem.Allocator) void {
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

        pub fn nfa(self: *const GrammarType) NfaView {
            return NfaView{ .grammar = self };
        }

        // TODO: enforce maximums based on SymbolId.type
        // TODO: remove "get" from some of these
        pub fn getVariableCount(self: GrammarType) SymbolId.VariableId {
            return @intCast(self.variables.len);
        }

        pub fn getTerminalCount(self: GrammarType) SymbolId.TerminalId {
            return @intCast(self.terminals.len);
        }

        pub fn getSymbolCount(self: GrammarType) usize {
            return self.getVariableCount() + self.getTerminalCount();
        }

        // HashMap for this? Parser will need it anyway...
        fn getSymbolIdFromVariableSlice(variable: Variable, slice: []const Variable) ?SymbolId {
            for (slice, 0..) |other_variable, v_id| {
                if (variable.eql(other_variable)) {
                    return SymbolId{ .variable_id = @intCast(v_id) };
                }
            }
            return null;
        }

        pub fn getSymbolIdFromVariable(self: GrammarType, variable: Variable) ?SymbolId {
            return getSymbolIdFromVariableSlice(variable, self.variables);
        }

        fn getSymbolIdFromTerminalSlice(terminal: Terminal, slice: []const Terminal) ?SymbolId {
            for (slice, 0..) |t, terminal_id| {
                if (terminal.eql(t)) {
                    return SymbolId{ .terminal_id = @intCast(terminal_id) };
                }
            }
            return null;
        }

        pub fn getSymbolIdFromTerminal(self: GrammarType, terminal: Terminal) ?SymbolId {
            return getSymbolIdFromTerminalSlice(terminal, self.terminals);
        }

        pub fn getStartSymbolId(_: GrammarType) SymbolId {
            return SymbolId{ .variable_id = 0 };
        }

        pub fn getEndSymbolId(self: GrammarType) SymbolId {
            return SymbolId{ .terminal_id = self.getTerminalCount() - 1 };
        }

        // TODO: Need to make sure things still work if we have multiple start
        // rules (e.g. S->A|B) OR limit to a single production for start rule
        // TODO: define RuleId type alias, make it u16 or something reasonable,
        //       reject bigger
        pub fn getStartRuleId(_: GrammarType) usize {
            return 0;
        }

        // TODO: individual field access would probably be faster than assembling
        //   a temp rule here (maybe look at disassembly and see what optimizer does?)
        pub fn getRule(self: GrammarType, rule_id: usize) Production {
            std.debug.assert(rule_id < self.rules_lhs.len);
            const row = self.rules_rhs.row(rule_id);
            return .{ .lhs = self.rules_lhs[rule_id], .rhs = row[0 .. row.len - 1] };
        }

        pub fn ruleCount(self: GrammarType) usize {
            return self.rules_lhs.len;
        }

        // TODO: optimize: use tarjan's scc algorithm

        // TODO: Is there a way to make rowUnion more efficient? Maybe keep a
        // second stack or map maintained or sth?

        // TODO: FOR DFS: theoretically only rquires one Symbol.VariableType
        // to store path_branches  === std.BITSTACK
        // e.g. for a flat tree it would be 1|11111...11111
        //    or for a larger graph it might be 1111|1111|11111...
        // and for a line it would be 1|1|1|1|...|1
        // where each |x| is the child index

        // TODO: some of this could be abstracted to NFA or Graph specific
        // helper functions, which would help make this function shorter
        // and also reduce some wasted allocations (e.g. populated does not
        // still need to be allocated when assembling the final closure lists)

        /// Caller must free returned RaggedArray
        pub fn computeEpsilonClosures(
            self: GrammarType,
            allocator: std.mem.Allocator,
        ) !utils.RaggedArray(NfaView.State, false) {
            var first_var_edge_list_offsets = try allocator.alloc(
                usize,
                self.getVariableCount() + 1,
            );
            defer allocator.free(first_var_edge_list_offsets);
            @memset(first_var_edge_list_offsets, 0);

            // In this function, we want to think about our rules as a
            // directional graph. Each node represents a variable, and an edge
            // from nodes A to B exists if there is a grammar rule where
            // variable A produces symbol B as the first symbol.
            //
            // NOTE: From here on, grammar symbols will be referred to as
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
            const total_edge_count = ret: for (0..self.ruleCount()) |i| {
                const rule = self.getRule(i);
                switch (rule.rhs[0]) {
                    .terminal_id => break :ret i,
                    .variable_id => continue,
                }
            } else 0;

            // Populate first_var_edge_list_offsets as described above.
            {
                var current_key = self.getRule(0).lhs;
                var offset: usize = 0;
                for (1..total_edge_count) |i| {
                    const rule = self.getRule(i);
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
                    if (self.getRule(offset).lhs != node_id) {
                        first_var_edge_list_offsets[node_id] = last_offset;
                    } else {
                        last_offset = offset;
                    }
                }
            }

            // Stores the e-NFA states reachable when reading a given grammar
            // variable. Each row represents a grammar variable, and each column
            // represents an e-NFA state (only the states stored in
            // rule_first_state_map are considered).
            var closure_table = utils.Slice2d([]bool).init(
                try allocator.alloc(bool, self.getVariableCount() * self.ruleCount()),
                self.ruleCount(),
            );
            defer allocator.free(closure_table.slice);
            @memset(closure_table.slice, false);

            // Seed first_closure_table with the state(s) directly reachable
            // from each grammar variable.
            for (0..self.ruleCount()) |i| {
                const rule = self.getRule(i);
                closure_table.row(rule.lhs)[i] = true;
            }

            var path = std.ArrayList(SymbolId.VariableId).empty;
            defer path.deinit(allocator);
            var path_edges_explored = try allocator.alloc(usize, self.getVariableCount());
            defer allocator.free(path_edges_explored);
            var visited = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(visited);
            var populated = try allocator.alloc(bool, self.getVariableCount());
            defer allocator.free(populated);
            @memset(populated, false);
            const nfa_view = self.nfa();

            // Now to solve the actual problem at hand: computing the epsilon
            // closure for each grammar variable.
            // - Starting from each node, we traverse the graph (depth first)
            //   copying the closure states from each node that is reachable,
            //   and then mark the starting node as populated.
            // - If we come across a node that is already populated, we don't
            //   explore that path any farther, and instead just copy its
            //   closure.
            // - We avoid visiting the same node twice in a path (to avoid
            //   infinite loops).
            for (0..self.getVariableCount()) |start_node| {
                path.items.len = 0;
                try path.append(allocator, @intCast(start_node));

                // Used to track how many edges we have already explored from
                // each node along the path.
                @memset(path_edges_explored, 0);

                @memset(visited, false);
                visited[start_node] = true;

                // Perform a depth first traversal from the start node.
                var state: enum { backtracking, exploring } = .exploring;
                while (path.getLastOrNull()) |current_node| switch (state) {
                    .exploring => {
                        const edges_explored = path_edges_explored[current_node];
                        const edge_count = first_var_edge_list_offsets[@as(usize, current_node) + 1] - first_var_edge_list_offsets[current_node];

                        if (edges_explored < edge_count) {
                            // Get the node from the next unexplored edge.
                            const next_index = first_var_edge_list_offsets[current_node] + edges_explored;
                            const next_node = self.getRule(next_index).rhs[0].variable_id;
                            path_edges_explored[current_node] += 1;

                            // Avoid loops.
                            if (visited[next_node]) {
                                continue;
                            }

                            // Continue exploring.
                            visited[next_node] = true;
                            try path.append(allocator, next_node);

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
                        // Before we backtrack, copy reachable states from the
                        // current node into the starting node.
                        utils.rowUnion(closure_table, start_node, current_node);

                        // Then move back one node and keep exploring.
                        path.items.len -= 1;
                        state = .exploring;
                    },
                };

                // The set of reachable states for this node is now fully
                // populated.
                populated[start_node] = true;
            }

            // Convert closure_table to a ragged array. //
            // TODO: consider doing this without iterating everything twice?
            //       could track size earlier, or add dynamic appends to builder
            var it = closure_table.iterRows();
            const element_count = ret: {
                var count: usize = 0;
                while (it.next()) |row| {
                    for (row) |is_in_table| {
                        count += @intFromBool(is_in_table);
                    }
                }
                break :ret count;
            };
            const RaggedArrayBuilder = utils.RaggedArray(NfaView.State, false).RaggedArrayBuilder;
            var builder = switch (@inComptime()) {
                true => RaggedArrayBuilder.initWithCapacityComptime(element_count, closure_table.rowCount()),
                false => try RaggedArrayBuilder.initWithCapacity(allocator, element_count, closure_table.rowCount()),
            };
            errdefer if (@inComptime()) builder.deinit(allocator);

            it.reset();
            while (it.next()) |row| {
                for (row, 0..) |is_in_table, i| {
                    if (is_in_table) {
                        const state = nfa_view.firstStateFromRuleId(i);
                        builder.appendAssumeCapacity(state);
                    }
                }
                builder.startNextRowAssumeCapacity();
            }

            return builder.build();
        }

        /// Caller must free the returned slice.
        fn computeFirstSet(
            self: GrammarType,
            allocator: std.mem.Allocator,
        ) ![]bool {
            var first_set_table = utils.Slice2d([]bool).init(
                try allocator.alloc(
                    bool,
                    self.getVariableCount() * self.getTerminalCount(),
                ),
                self.getTerminalCount(),
            );
            errdefer allocator.free(first_set_table.slice);
            @memset(first_set_table.slice, false);

            var closures = try self.computeEpsilonClosures(allocator);
            defer if (!@inComptime()) closures.deinit(allocator);

            const nfa_view = self.nfa();
            for (0..self.getVariableCount()) |var_id| {
                for (closures.row(var_id)) |nfa_state| {
                    const rule_id = nfa_view.ruleIdFromState(nfa_state);
                    const first_symbol = self.getRule(rule_id).rhs[0];
                    switch (first_symbol) {
                        .terminal_id => |id| first_set_table.row(var_id)[id] = true,
                        .variable_id => {},
                    }
                }
            }

            return first_set_table.slice;
        }

        /// Computes the FIRST set for the grammar as a table. Each row
        /// represents a grammar variable, each column a grammar symbol (a
        /// column for each terminal first, followed by a column for each
        /// variable). If row x, column y is true, then
        /// if y < self.getTerminalCount(), the *terminal* with ID y is in
        ///   the FIRST set of the variable with ID x;
        /// otherwise, the *variable* with ID (self.getTerminalCount() - y) is
        ///   in the FIRST set of the variable with ID x.
        ///
        /// The returned slice should be interpreted as a row-wise 2D array as
        /// described above. Caller must free.
        ///
        /// NOTE: $ (END character) can never be first
        pub fn getFirstSet(self: GrammarType, allocator: std.mem.Allocator) ![]bool {
            return self.computeFirstSet(allocator);
        }

        /// Comptime version of `getFirstSet()`, no dynamic allocation needed.
        pub fn getFirstSetComptime(comptime self: GrammarType) []bool {
            comptime return self.computeFirstSet(comptime_allocator.comptime_allocator) catch unreachable;
        }

        /// Caller must provide buffers with the necessary room:
        /// * `follow_set: [self.getVariableCount() * self.getTerminalCount()]bool`
        ///
        /// Caller must also provide a **populated** `first_set` table.
        ///
        /// `follow_set` is populated with the resulting table, the other buffers
        /// can be freed immediately if they were dynamically allocated.
        fn computeFollowSet(
            self: GrammarType,
            follow_set: utils.Slice2d([]bool),
            first_set: utils.Slice2d([]const bool),
        ) void {
            std.debug.assert(follow_set.slice.len >= self.getVariableCount() * self.getTerminalCount());
            std.debug.assert(first_set.slice.len >= self.getVariableCount() * self.getTerminalCount());

            @memset(follow_set.slice, false);

            // Initialize FOLLOW(startsymbol) to include the end terminal.
            follow_set.row(0)[follow_set.row_length - 1] = true;

            // Iterate through each rhs of each grammar rule. Whenever we come
            // across a variable, look at the next symbol: if its a terminal,
            // add it to the variable's FOLLOW set; if it's another variable,
            // union its FIRST set into the current variable's FOLLOW set.
            for (0..self.ruleCount()) |i| {
                const rule = self.getRule(i);
                for (rule.rhs[0..(rule.rhs.len - 1)], rule.rhs[1..rule.rhs.len]) |symbol_id, next_symbol_id| {
                    switch (symbol_id) {
                        .terminal_id => continue,
                        .variable_id => |v_id| switch (next_symbol_id) {
                            .terminal_id => |next_t_id| follow_set.row(v_id)[next_t_id] = true,
                            // TODO: first set is now different row length, should add a check for this in sliceUnion!!!
                            .variable_id => |next_v_id| utils.sliceUnion(follow_set.row(v_id), first_set.row(next_v_id)),
                        },
                    }
                }
            }

            // Propagate FOLLOW sets for any productions whose rhs ends with a
            // variable.
            for (0..self.ruleCount()) |i| {
                const rule = self.getRule(i);
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
        pub fn getFollowSet(self: GrammarType, allocator: std.mem.Allocator, first_set: utils.Slice2d([]const bool)) ![]bool {
            const follow_set_buffer = try allocator.alloc(bool, self.getVariableCount() * self.getTerminalCount());
            errdefer allocator.free(follow_set_buffer);

            self.computeFollowSet(
                utils.Slice2d([]bool).init(follow_set_buffer, self.getTerminalCount()),
                first_set,
            );
            return follow_set_buffer;
        }

        /// Comptime version of `getFollowSet()`, no dynamic allocation needed.
        pub fn getFollowSetComptime(comptime self: GrammarType, first_set: utils.Slice2d([]const bool)) [self.getVariableCount() * self.getTerminalCount()]bool {
            comptime {
                var follow_set_buffer: [self.getVariableCount() * self.getTerminalCount()]bool = undefined;

                self.computeFollowSet(
                    utils.Slice2d([]bool).init(&follow_set_buffer, self.getTerminalCount()),
                    first_set,
                );
                return follow_set_buffer;
            }
        }
    };
}

test "Grammar.initFromTuples [grammar1.0]" {
    // R0: S   ->  (0) wff (1)
    // R1: wff ->  (2) Proposition (3)
    // R2: wff ->  (4) Not     (5) wff  (6)
    // R3: wff ->  (7) LParen  (8) wff  (9) And    (10) wff (11) RParen (12)
    // R4: wff -> (13) LParen (14) wff (15) Or     (16) wff (17) RParen (18)
    // R5: wff -> (19) LParen (20) wff (21) Cond   (22) wff (23) RParen (24)
    // R6: wff -> (25) LParen (26) wff (27) Bicond (28) wff (29) RParen (30)

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);
    const actual_grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("wff") } },
            .{ V("wff"), .{ TestTerminal.Proposition } },
            .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
            .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
        },
        V("S"),
        TestTerminal.End,
    );

    const V_S = SymbolId{ .variable_id = 0 };
    const V_WFF = SymbolId{ .variable_id = 1 };
    const V_SENTINEL = G.SENTINEL;
    const T_PROPOSITION = SymbolId{ .terminal_id = 0 };
    const T_NOT = SymbolId{ .terminal_id = 1 };
    const T_LPAREN = SymbolId{ .terminal_id = 2 };
    const T_AND = SymbolId{ .terminal_id = 3 };
    const T_RPAREN = SymbolId{ .terminal_id = 4 };
    const T_OR = SymbolId{ .terminal_id = 5 };
    const T_COND = SymbolId{ .terminal_id = 6 };
    const T_BICOND = SymbolId{ .terminal_id = 7 };
    // $ = 10

    const rules_lhs = [_]SymbolId.VariableId{
        V_S.variable_id,
        V_WFF.variable_id,
        V_WFF.variable_id,
        V_WFF.variable_id,
        V_WFF.variable_id,
        V_WFF.variable_id,
        V_WFF.variable_id,
    };

    const rules_rhs = [_]SymbolId{
        V_WFF, V_SENTINEL,
        T_PROPOSITION, V_SENTINEL,
        T_NOT, V_WFF, V_SENTINEL,
        T_LPAREN, V_WFF, T_AND, V_WFF, T_RPAREN,V_SENTINEL,
        T_LPAREN, V_WFF, T_OR, V_WFF, T_RPAREN, V_SENTINEL,
        T_LPAREN, V_WFF, T_COND, V_WFF, T_RPAREN, V_SENTINEL,
        T_LPAREN, V_WFF, T_BICOND, V_WFF, T_RPAREN, V_SENTINEL,
    };

    const offsets = [_]usize{ 0, 2, 4, 7, 13, 19, 25, 31 };

    const index_to_row_map = [_]usize{
        0, 0,
        1, 1,
        2, 2, 2,
        3, 3, 3, 3, 3, 3,
        4, 4, 4, 4, 4, 4,
        5, 5, 5, 5, 5, 5,
        6, 6, 6, 6, 6, 6,
    };

    const expected_grammar = G{
        .rules_lhs = &rules_lhs,
        .rules_rhs = utils.RaggedArray(SymbolId, true){
            .data = &rules_rhs,
            .row_offsets = &offsets,
            .index_to_row_map = &index_to_row_map,
        },
        .variables = &[_]TestVariable{ V("S"), V("wff") },
        .terminals = &[_]TestTerminal{
            TestTerminal.Proposition, TestTerminal.Not,    TestTerminal.LParen,
            TestTerminal.And,         TestTerminal.RParen, TestTerminal.Or,
            TestTerminal.Cond,        TestTerminal.Bicond, TestTerminal.End
        },
    };

    try std.testing.expectEqualDeep(expected_grammar.rules_lhs, actual_grammar.rules_lhs);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.data, actual_grammar.rules_rhs.data);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.row_offsets, actual_grammar.rules_rhs.row_offsets);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.index_to_row_map, actual_grammar.rules_rhs.index_to_row_map);
    try std.testing.expectEqualDeep(expected_grammar.variables, actual_grammar.variables);
    try std.testing.expectEqualDeep(expected_grammar.terminals, actual_grammar.terminals);
}

test "Grammar.initFromTuples [grammar2.2]" {
    // R0:     S ->  (0) wff1  (1)
    // R1:  wff1 ->  (2) wff2  (3)
    // R2:  wff1 ->  (4) wff1  (5) <=> (6) wff2 (7)
    // R3:  wff2 ->  (8) wff3  (9)
    // R4:  wff2 -> (10) wff2 (11) => (12) wff3 (13)
    // R5:  wff3 -> (14) wff4 (15)
    // R6:  wff3 -> (16) wff3 (17) v (18) wff4 (19)
    // R7:  wff3 -> (20) wff3 (21) ^ (22) wff4 (23)
    // R8:  wff4 -> (24) prop (25)
    // R9:  wff4 -> (26) ~    (27) wff4 (28)
    // R10: prop -> (29) ( (30) wff1 (31) )  (32)
    // R11: prop -> (33) PROPTOK (34)

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

    const V = TestVariable.fromString;
    const G = Grammar(TestVariable, TestTerminal);

    const actual_grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("wff1") } },

            .{ V("wff1"), .{ V("wff2") } },
            .{ V("wff1"), .{ V("wff1"), TestTerminal.Bicond, V("wff2") } },

            .{ V("wff2"), .{ V("wff3") } },
            .{ V("wff2"), .{ V("wff2"), TestTerminal.Cond, V("wff3") } },

            .{ V("wff3"), .{ V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.Or, V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.And, V("wff4") } },

            .{ V("wff4"), .{ V("prop") } },
            .{ V("wff4"), .{ TestTerminal.Not, V("wff4") } },

            .{ V("prop"), .{ TestTerminal.LParen, V("wff1"), TestTerminal.RParen } },
            .{ V("prop"), .{ TestTerminal.Proposition } },
        },
        V("S"),
        TestTerminal.End,
    );

    const V_S = SymbolId{ .variable_id = 0 };
    const V_WFF1 = SymbolId{ .variable_id = 1 };
    const V_WFF2 = SymbolId{ .variable_id = 2 };
    const V_WFF3 = SymbolId{ .variable_id = 3 };
    const V_WFF4 = SymbolId{ .variable_id = 4 };
    const V_PROP = SymbolId{ .variable_id = 5 };
    const SENTINEL = G.SENTINEL;
    const T_BICOND = SymbolId{ .terminal_id = 0 };
    const T_COND = SymbolId{ .terminal_id = 1 };
    const T_OR = SymbolId{ .terminal_id = 2 };
    const T_AND = SymbolId{ .terminal_id = 3 };
    const T_NOT = SymbolId{ .terminal_id = 4 };
    const T_LPAREN = SymbolId{ .terminal_id = 5 };
    const T_RPAREN = SymbolId{ .terminal_id = 6 };
    const T_PROPTOK = SymbolId{ .terminal_id = 7 };

    const rules_lhs = [_]SymbolId.VariableId{
        V_S.variable_id,
        V_WFF1.variable_id,
        V_WFF1.variable_id,
        V_WFF2.variable_id,
        V_WFF2.variable_id,
        V_WFF3.variable_id,
        V_WFF3.variable_id,
        V_WFF3.variable_id,
        V_WFF4.variable_id,
        V_WFF4.variable_id,
        V_PROP.variable_id,
        V_PROP.variable_id,
    };

    const rules_rhs = [_]SymbolId{
        V_WFF1, SENTINEL,

        V_WFF2, SENTINEL,
        V_WFF1, T_BICOND, V_WFF2, SENTINEL,

        V_WFF3, SENTINEL,
        V_WFF2, T_COND, V_WFF3, SENTINEL,

        V_WFF4, SENTINEL,
        V_WFF3, T_OR, V_WFF4, SENTINEL,
        V_WFF3, T_AND, V_WFF4, SENTINEL,

        V_PROP, SENTINEL,
        T_NOT, V_WFF4, SENTINEL,
        T_LPAREN, V_WFF1, T_RPAREN, SENTINEL,
        T_PROPTOK, SENTINEL,
    };

    const offsets = [_]usize{ 0, 2, 4, 8, 10, 14, 16, 20, 24, 26, 29, 33, 35 };

    const index_to_row_map = [_]usize{
        0, 0,
        1, 1,
        2, 2, 2, 2,
        3, 3,
        4, 4, 4, 4,
        5, 5,
        6, 6, 6, 6,
        7, 7, 7, 7,
        8, 8,
        9, 9, 9,
        10, 10, 10, 10,
        11, 11,
    };

    const expected_grammar = G{
        .rules_lhs = &rules_lhs,
        .rules_rhs = utils.RaggedArray(SymbolId, true){
            .data = &rules_rhs,
            .row_offsets = &offsets,
            .index_to_row_map = &index_to_row_map,
        },
        .variables = &[_]TestVariable{ V("S"), V("wff1"), V("wff2"), V("wff3"), V("wff4"), V("prop") },
        .terminals = &[_]TestTerminal{ .Bicond, .Cond, .Or, .And, .Not, .LParen, .RParen, .Proposition, .End },
    };

    try std.testing.expectEqualDeep(expected_grammar.rules_lhs, actual_grammar.rules_lhs);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.data, actual_grammar.rules_rhs.data);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.row_offsets, actual_grammar.rules_rhs.row_offsets);
    try std.testing.expectEqualDeep(expected_grammar.rules_rhs.index_to_row_map, actual_grammar.rules_rhs.index_to_row_map);
    try std.testing.expectEqualDeep(expected_grammar.variables, actual_grammar.variables);
    try std.testing.expectEqualDeep(expected_grammar.terminals, actual_grammar.terminals);
}

test "epsilonClosures [custom5]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("A") } },
            .{ V("A"), .{ V("A"), V("B"), T("c") } },
            .{ V("A"), .{ V("B"), T("b") } },

            .{ V("B"), .{ V("A"), T("c") } },
            .{ V("B"), .{ T("q") } },
        },
        V("S"),
        T("$"),
    );

    const allocator = std.testing.allocator;

    const closures = try grammar.computeEpsilonClosures(allocator);
    defer closures.deinit(allocator);

    // S ->  (0) A  (1)
    // A ->  (2) A  (3) B  (4) c (5)
    // A ->  (6) B  (7) b  (8)
    // B ->  (9) A (10) c (11)
    // B -> (12) q
    const expected_closures = [_]G.NfaView.State{
        0, 2, 6, 9, 12, // S
        2, 6, 9, 12,    // A
        2, 6, 9, 12,    // B
    };

    try std.testing.expectEqualSlices(G.NfaView.State, &expected_closures, closures.data);
}

test "firsts_and_follows [grammar1.0]" {
    @setEvalBranchQuota(10000);
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
    comptime try std.testing.expectEqualSlices(bool, &expected_firsts, first_set_comptime);

    const follow_set = try grammar.getFollowSet(
        allocator,
        utils.Slice2d([]const bool).init(first_set, grammar.getSymbolCount()),
    );
    defer allocator.free(follow_set);

    const follow_set_comptime = comptime grammar.getFollowSetComptime(
        utils.Slice2d([]const bool).init(first_set_comptime, grammar.getSymbolCount()),
    );

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
    comptime try std.testing.expectEqualSlices(bool, &expected_firsts, first_set_comptime);

    const follow_set = try grammar.getFollowSet(
        allocator,
        utils.Slice2d([]const bool).init(first_set, grammar.getSymbolCount()),
    );
    defer allocator.free(follow_set);

    const follow_set_comptime = comptime grammar.getFollowSetComptime(
        utils.Slice2d([]const bool).init(first_set_comptime, grammar.getSymbolCount()),
    );

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

fn followTableFromTuples(
    comptime tuples: anytype,
    comptime Variable: type,
    comptime Terminal: type,
    grammar: Grammar(Variable, Terminal),
) [grammar.getVariableCount() * grammar.getTerminalCount()]bool {
    comptime {
        var follow_set = [_]bool{false} ** (grammar.getVariableCount() * grammar.getTerminalCount());
        var follow_set_2d_view = utils.Slice2d([]bool).init(&follow_set, grammar.getTerminalCount());

        for (tuples) |tuple| {
            const variable = tuple.@"0";
            const v_id = grammar.getSymbolIdFromVariable(variable).?.variable_id;

            const terminals = tuple.@"1";
            for (std.meta.fieldNames(@TypeOf(terminals))) |rhs_tuple_field_name| {
                const terminal = @field(terminals, rhs_tuple_field_name);
                if (@TypeOf(terminal) == Terminal) {
                    const t_id = grammar.getSymbolIdFromTerminal(terminal).?.terminal_id;
                    follow_set_2d_view.row(v_id)[t_id] = true;
                } else {
                    @compileError("rhs of tuple must only contain Terminals");
                }
            }
        }
        return follow_set;
    }
}

fn firstTableFromTuples(
    comptime tuples: anytype,
    comptime Variable: type,
    comptime Terminal: type,
    grammar: Grammar(Variable, Terminal),
) [grammar.getVariableCount() * grammar.getSymbolCount()]bool {
    comptime {
        var first_set = [_]bool{false} ** (grammar.getVariableCount() * grammar.getSymbolCount());
        var first_set_2d_view = utils.Slice2d([]bool).init(&first_set, grammar.getSymbolCount());

        for (tuples) |tuple| {
            const variable = tuple.@"0";
            const v_id = grammar.getSymbolIdFromVariable(variable).?.variable_id;

            const terminals = tuple.@"1";
            for (std.meta.fieldNames(@TypeOf(terminals))) |rhs_tuple_field_name| {
                const terminal = @field(terminals, rhs_tuple_field_name);
                if (@TypeOf(terminal) == Terminal) {
                    const t_id = grammar.getSymbolIdFromTerminal(terminal).?.terminal_id;
                    first_set_2d_view.row(v_id)[t_id] = true;
                } else if (@TypeOf(terminal) == Variable) {
                    const other_v_id = grammar.getSymbolIdFromVariable(terminal).?.variable_id;
                    first_set_2d_view.row(v_id)[grammar.getTerminalCount() + other_v_id] = true;
                } else {
                    @compileError("rhs of tuple must only contain Terminals and Variables");
                }
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

    const expected_first_set = comptime followTableFromTuples(
        .{
            .{ V("S"), .{ T("("), T("#"), T("~") } },
            .{ V("A"), .{ T("("), T("#"), T("~") } },
            .{ V("B"), .{ T("("), T("#") } },
        },
        TestVariable,
        TestTerminal,
        grammar,
    );
    // TODO: how to make comptime tests fail nicer (avoid compile error, or
    //       make more descriptive)
    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    comptime try std.testing.expectEqualSlices(bool, &expected_first_set, first_set_comptime);
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

    const expected_first_set = comptime followTableFromTuples(
        .{
            .{ V("S"), .{ T("c"), T("a") } },
            .{ V("A"), .{ T("c"), T("a") } },
            .{ V("B"), .{ T("c"), T("a"), T("q") } },
            .{ V("C"), .{ T("c"), T("a"), T("q") } },
            .{ V("D"), .{ T("q") } },
        },
        TestVariable,
        TestTerminal,
        grammar,
    );

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    comptime try std.testing.expectEqualSlices(bool, &expected_first_set, first_set_comptime);
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
            .{ V("S"), .{ V("A") } },

            .{ V("A"), .{ T("c"), V("B") } },
            .{ V("A"), .{ V("Q") } },
            .{ V("A"), .{ T("a") } },

            .{ V("B"), .{ V("C"), T("b") } },

            .{ V("C"), .{ V("A"), T("d") } },
            .{ V("C"), .{ V("D") } },

            .{ V("D"), .{ T("q") } },
            .{ V("Q"), .{ T("z") } },
        },
        V("S"),
        T("$"),
    );

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime followTableFromTuples(.{
        .{ V("S"), .{ T("c"), T("a"), T("z") } },
        .{ V("A"), .{ T("c"), T("a"), T("z") } },
        .{ V("B"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("C"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("D"), .{ T("q") } },
        .{ V("Q"), .{ T("z") } },
    }, TestVariable, TestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    comptime try std.testing.expectEqualSlices(bool, &expected_first_set, first_set_comptime);
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
            .{ V("S"), .{ V("A") } },
            .{ V("A"), .{ T("c"), V("B") } },
            .{ V("A"), .{ V("Q") } },
            .{ V("A"), .{ T("a") } },

            .{ V("B"), .{ V("C"), T("b") } },

            .{ V("C"), .{ V("A"), T("d") } },
            .{ V("C"), .{ V("D") } },

            .{ V("D"), .{ T("q") } },
            .{ V("Q"), .{ T("z") } },
        },
        V("S"),
        T("$"),
    );

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime followTableFromTuples(.{
        .{ V("S"), .{ T("c"), T("a"), T("z") } },
        .{ V("A"), .{ T("c"), T("a"), T("z") } },
        .{ V("B"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("C"), .{ T("c"), T("a"), T("z"), T("q") } },
        .{ V("D"), .{ T("q") } },
        .{ V("Q"), .{ T("z") } },
    }, TestVariable, TestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    comptime try std.testing.expectEqualSlices(bool, &expected_first_set, first_set_comptime);
}

test "first_and_follows [custom5]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = Grammar(TestVariable, TestTerminal);

    const grammar = comptime G.initFromTuples(
        .{
            .{ V("S"), .{ V("A") } },
            .{ V("A"), .{ V("A"), V("B"), T("c") } },
            .{ V("A"), .{ V("B"), T("b") } },

            .{ V("B"), .{ V("A"), T("c") } },
            .{ V("B"), .{ T("q") } },
        },
        V("S"),
        T("$"),
    );

    var allocator = std.testing.allocator;

    const first_set = try grammar.getFirstSet(allocator);
    defer allocator.free(first_set);

    const first_set_comptime = comptime grammar.getFirstSetComptime();

    const expected_first_set = comptime followTableFromTuples(.{
        .{ V("S"), .{ T("q") } },
        .{ V("A"), .{ T("q") } },
        .{ V("B"), .{ T("q") } },
    }, TestVariable, TestTerminal, grammar);

    try std.testing.expectEqualSlices(bool, &expected_first_set, first_set);
    comptime try std.testing.expectEqualSlices(bool, &expected_first_set, first_set_comptime);
}
