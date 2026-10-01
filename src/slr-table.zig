const std = @import("std");

const slr_grammar = @import("slr-grammar.zig");
const test_common = @import("test-common.zig");
const utils = @import("utils.zig");

pub const TableGeneratorError = error{
    shiftShiftError,
    shiftReduceError,
    shiftAcceptError,
    reduceReduceError,
    reduceAcceptError,
    acceptError,
};

const ProductionInstance = struct {
    const Self = @This();

    production: slr_grammar.Production,
    cursor: usize,

    fn fromProduction(production: slr_grammar.Production) Self {
        return ProductionInstance{ .production = production, .cursor = 0 };
    }

    fn eql(self: Self, other: Self) bool {
        return self.cursor == other.cursor and self.production.eql(other.production);
    }

    fn readCursor(self: Self) ?slr_grammar.SymbolId {
        if (self.cursor >= self.production.rhs.len) {
            return null;
        } else {
            return self.production.rhs[self.cursor];
        }
    }

    fn copyAdvanceCursor(self: Self) Self {
        return ProductionInstance{ .production = self.production, .cursor = self.cursor + 1 };
    }

    fn printDebug(self: Self) !void {
        std.debug.print("({d})", .{self.production.lhs.variable_id});
        std.debug.print(" ->", .{});
        for (self.production.rhs[0..self.cursor]) |sym| {
            switch (sym) {
                .variable_id => |id| std.debug.print(" ({d})", .{id}),
                .terminal_id => |id| std.debug.print(" {d}", .{id}),
            }
        }
        std.debug.print(" *", .{});
        for (self.production.rhs[self.cursor..]) |sym| {
            switch (sym) {
                .variable_id => |id| std.debug.print(" ({d})", .{id}),
                .terminal_id => |id| std.debug.print(" {d}", .{id}),
            }
        }
        std.debug.print("\n", .{});
    }
};

pub fn ParseTable(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const Self = @This();
        const GrammarType = slr_grammar.Grammar(Variable, Terminal);
        const Action = union(enum) {
            state: StateIdx,
            reduce: usize, // index of grammar.rules
            invalid,
            accept,
        };

        pub const StateIdx = usize;

        grammar: GrammarType,
        goto_table: utils.Slice2d([]Action), // TODO add const back to these
        action_table: utils.Slice2d([]Action),

        pub fn init(allocator: std.mem.Allocator, grammar: GrammarType) !Self {
            const action_table, const goto_table = try generateTables3(allocator, grammar);
            return Self{
                .grammar = grammar,
                .goto_table = goto_table,
                .action_table = action_table,
            };
        }

        // TODO: initComptime ?

        /// Note: Does NOT free the memory associated with the grammar
        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.goto_table.slice);
            allocator.free(self.action_table.slice);
        }

        pub fn getStartState(_: Self) StateIdx {
            return 0;
        }

        pub fn lookupSymbol(self: Self, state: StateIdx, symbol: slr_grammar.SymbolId) Action {
            return switch (symbol) {
                .terminal_id => |t_id| self.action_table.row(state)[t_id],
                .variable_id => |v_id| self.goto_table.row(state)[v_id],
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
            std.debug.print("\n{s: ^" ++ COL_SPACE ++ "} ||", .{""});
            for (self.grammar.terminals) |t| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{t.getString()});
            }
            std.debug.print("|", .{});
            for (self.grammar.variables) |v| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{v.getString()});
            }
            std.debug.print("|", .{});

            var goto_it = self.goto_table.iterRows();
            var action_it = self.action_table.iterRows();
            var s: usize = 0;
            while (goto_it.next()) |goto_row| : (s += 1) {
                const action_row = action_it.next().?;

                std.debug.print("\n{d: >" ++ COL_SPACE ++ "} ||", .{s});
                for (action_row) |entry| switch (entry) {
                    .state => |state_num| std.debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| std.debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                std.debug.print("|", .{});
                for (goto_row) |entry| switch (entry) {
                    .state => |state_num| std.debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| std.debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                std.debug.print("| {d: <" ++ COL_SPACE ++ "}", .{s});
            }
            std.debug.print("\n", .{});
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
                                for (0..grammar.ruleCount()) |rule_id| {
                                    const rule = grammar.getRule(rule_id);
                                    if (sym.eqlVariable(rule.lhs)) {
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

        // TODO: remove
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

        fn generateTables3(
            allocator: std.mem.Allocator,
            grammar: GrammarType,
        ) !struct { utils.Slice2d([]Action), utils.Slice2d([]Action) } {
            // Generate grammar variable to epsilon closure map
            var closures = try grammar.computeEpsilonClosures(allocator);
            defer closures.deinit(allocator);

            // Generate table data structures: Action table, Goto table, and
            // DFA state -> NFA state set map
            var action_table = std.ArrayList([]Action).empty;
            defer {
                for (action_table.items) |row| allocator.free(row);
                action_table.deinit(allocator);
            }
            var goto_table = std.ArrayList([]Action).empty;
            defer {
                for (goto_table.items) |row| allocator.free(row);
                goto_table.deinit(allocator);
            }
            // Only store kernels, not entire set
            // TODO: do i actually need to store values, or can i just use the
            // index of they keys?
            const ArrayHashMapType = std.array_hash_map.Custom(
                []GrammarType.NfaView.State,
                void,
                struct {
                    pub fn hash(_: @This(), key: []GrammarType.NfaView.State) u32 {
                        return @truncate(std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(key)));
                    }
                    pub fn eql(_: @This(), a: []GrammarType.NfaView.State, b: []GrammarType.NfaView.State, _: usize) bool {
                        return std.mem.eql(GrammarType.NfaView.State, a, b);
                    }
                },
                // TODO: better understand what this does
                false,
            );
            var table_state_sets = ArrayHashMapType.empty;
            defer {
                for (table_state_sets.entries.items(.key)) |set| {
                    allocator.free(set);
                }
                table_state_sets.deinit(allocator);
            }

            // First DFA state is the epsilon closure of the first e-NFA state
            try table_state_sets.put(
                allocator,
                try allocator.dupe(
                    GrammarType.NfaView.State,
                    &[_]GrammarType.NfaView.State{grammar.getStartSymbolId().variable_id},
                ),
                {},
            );

            // Now populate the table: add new rows until all state sets
            // accounted for
            var action_row_state_sets: []std.ArrayList(GrammarType.NfaView.State) = try allocator.alloc(
                std.ArrayList(GrammarType.NfaView.State),
                grammar.getTerminalCount(),
            );
            for (0..action_row_state_sets.len) |i| {
                action_row_state_sets[i] = .empty;
            }
            defer {
                for (action_row_state_sets) |*set| set.deinit(allocator);
                allocator.free(action_row_state_sets);
            }
            var goto_row_state_sets: []std.ArrayList(GrammarType.NfaView.State) = try allocator.alloc(
                std.ArrayList(GrammarType.NfaView.State),
                grammar.getVariableCount(),
            );
            for (0..goto_row_state_sets.len) |i| {
                goto_row_state_sets[i] = .empty;
            }
            defer {
                for (goto_row_state_sets) |*set| set.deinit(allocator);
                allocator.free(goto_row_state_sets);
            }
            const nfa = grammar.nfa();
            var state: StateIdx = 0;
            while (state < table_state_sets.count()) : (state += 1) {
                const nfa_kernels = table_state_sets.entries.get(state).key;

                for (action_row_state_sets) |*set| {
                    set.items.len = 0;
                }
                for (goto_row_state_sets) |*set| {
                    set.items.len = 0;
                }

                try action_table.ensureUnusedCapacity(allocator, 1);
                var action_row = try allocator.alloc(Action, grammar.getTerminalCount());
                // Append right away so memory deallocation will be handled by
                // table cleanup if we encounter an error.
                action_table.appendAssumeCapacity(action_row);
                @memset(action_row, .invalid);

                try goto_table.ensureUnusedCapacity(allocator, 1);
                var goto_row = try allocator.alloc(Action, grammar.getVariableCount());
                // Append right away, same as above.
                goto_table.appendAssumeCapacity(goto_row);
                @memset(goto_row, .invalid);

                // Populate NFA state sets in the row
                for (nfa_kernels) |kernel_nfa_state| {
                    // First deal with symbol being read in the kernel state
                    const kernel_symbol = nfa.symbolIdFromState(kernel_nfa_state) orelse continue;
                    const kernel_symbol_v_id = ret: switch (kernel_symbol) {
                        .terminal_id => |id| {
                            try action_row_state_sets[id].append(allocator, kernel_nfa_state + 1);
                            continue;
                        },
                        .variable_id => |id| {
                            try goto_row_state_sets[id].append(allocator, kernel_nfa_state + 1);
                            break :ret id;
                        },
                    };

                    // We only get here if kernel_symbol is a variable
                    const kernel_closure = closures.row(kernel_symbol_v_id);
                    for (kernel_closure) |nfa_state| {
                        const reading_symbol = nfa.symbolIdFromState(nfa_state).?;
                        switch (reading_symbol) {
                            .terminal_id => |id| {
                                const found =std.mem.findScalar(
                                    GrammarType.NfaView.State,
                                    action_row_state_sets[id].items,
                                    nfa_state + 1,
                                );
                                if (found == null) {
                                    try action_row_state_sets[id].append(allocator, nfa_state + 1);
                                }
                            },
                            .variable_id => |id| {
                                const found = std.mem.findScalar(
                                    GrammarType.NfaView.State,
                                    goto_row_state_sets[id].items,
                                    nfa_state + 1,
                                );
                                if (found == null) {
                                    try goto_row_state_sets[id].append(allocator, nfa_state + 1);
                                }
                            },
                        }
                    }
                }

                for (action_row_state_sets) |*set| {
                    std.mem.sortUnstable(
                        GrammarType.NfaView.State,
                        set.items,
                        {},
                        std.sort.asc(GrammarType.NfaView.State),
                    );
                }

                // Look at NFA state sets in the current row: skip existing
                // ones, and create new states (new rows in the parse table) for
                // new ones
                for (action_row_state_sets, 0..) |set, t_id| {
                    if (set.items.len == 0) {
                        continue;
                    }
                    std.debug.assert(action_row[t_id] == .invalid);
                    if (table_state_sets.getIndex(set.items)) |state_id| {
                        action_row[t_id] = Action{ .state = state_id };
                    } else {
                        const new_state_id = table_state_sets.count();
                        try table_state_sets.put(
                            allocator,
                            try allocator.dupe(GrammarType.NfaView.State,set.items),
                            {},
                        );
                        action_row[t_id] = Action{ .state = new_state_id };
                    }
                }

                for (goto_row_state_sets) |*set| {
                    std.mem.sortUnstable(
                        GrammarType.NfaView.State,
                        set.items,
                        {},
                        std.sort.asc(GrammarType.NfaView.State),
                    );
                }

                for (goto_row_state_sets, 0..) |set, v_id| {
                    if (set.items.len == 0) {
                        continue;
                    }
                    std.debug.assert(goto_row[v_id] == .invalid);
                    if (table_state_sets.getIndex(set.items)) |state_id| {
                        goto_row[v_id] = Action{ .state = state_id };
                    } else {
                        const new_state_id = table_state_sets.count();
                        try table_state_sets.put(
                            allocator,
                            try allocator.dupe(GrammarType.NfaView.State, set.items),
                            {},
                        );
                        goto_row[v_id] = Action{ .state = new_state_id };
                    }
                }
            }

            // Now that states are populated, we populate reductions
            // TODO: we already have closures, should probably be able to pass in
            const first_set = try grammar.getFirstSet(allocator);
            defer allocator.free(first_set);
            const follow_set = utils.Slice2d([]const bool).init(
                try grammar.getFollowSet(
                    allocator,
                    // TODO : I shouldnt have to do this here
                    utils.Slice2d([]const bool).init(first_set, grammar.getSymbolCount()),
                ),
                grammar.getTerminalCount(),
            );
            defer allocator.free(follow_set.slice);

            // TODO: this should probably move into the above loop so we don't
            // have to "look for" the states with end nfa states, we can just
            // populate reductions as we hit end states
            for (table_state_sets.entries.items(.key), 0..) |set, state_id| {
                for (set) |nfa_state| {
                    // Continue if this isn't the last state in a rule.
                    if (nfa.symbolIdFromState(nfa_state) != null) {
                        continue;
                    }

                    const rule_id = nfa.ruleIdFromState(nfa_state);
                    const rule = grammar.getRule(rule_id);
                    for (follow_set.row(rule.lhs), 0..) |is_in_follow_set, t_id| {
                        if (!is_in_follow_set) {
                            continue;
                        }

                        action_table.items[state_id][t_id] = try switch (action_table.items[state_id][t_id]) {
                            .invalid => Action{ .reduce = rule_id },
                            .state => TableGeneratorError.shiftReduceError,
                            .reduce => TableGeneratorError.shiftReduceError,
                            .accept => unreachable,
                        };
                    }
                }
            }

            var action_table_final = utils.Slice2d([]Action).init(
                try allocator.alloc(Action, action_table.items.len * grammar.getTerminalCount()),
                grammar.getTerminalCount(),
            );
            errdefer allocator.free(action_table_final.slice);
            for (action_table.items, 0..) |row, i| {
                @memcpy(action_table_final.row(i), row);
            }

            var goto_table_final = utils.Slice2d([]Action).init(
                try allocator.alloc(Action, goto_table.items.len * grammar.getVariableCount()),
                grammar.getVariableCount(),
            );
            errdefer allocator.free(goto_table_final.slice);
            for (goto_table.items, 0..) |row, i| {
                @memcpy(goto_table_final.row(i), row);
            }

            return .{ action_table_final, goto_table_final };
        }

        fn generateTables(
            allocator: std.mem.Allocator,
            grammar: GrammarType,
        ) !struct { utils.Slice2d([]Action), utils.Slice2d([]Action) } {
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
            primary_productions_table.items[0][0] = ProductionInstance.fromProduction(grammar.getRule(grammar.getStartRuleId()));

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

            const first_set = try grammar.getFirstSet(allocator);
            defer allocator.free(first_set);

            const follow_set = try grammar.getFollowSet(allocator, utils.Slice2d([]const bool).init(first_set, grammar.getSymbolCount()));
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
                        if (!follow_set[instance.production.lhs * grammar.getTerminalCount() + t_id]) continue;

                        action_table.items[state_num][t_id] = try switch (action_table.items[state_num][t_id]) {
                            .invalid => Action{ .reduce = rule_id },
                            .state => TableGeneratorError.shiftReduceError,
                            .reduce => TableGeneratorError.reduceReduceError,
                            .accept => TableGeneratorError.reduceAcceptError,
                        };
                    }

                    // TODO: hardcoded 0 kinda yucky
                    if (instance.production.lhs == grammar.getStartSymbolId().variable_id) {
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
            const goto_slice = try allocator.alloc(Action, goto_table.items.len * goto_table.items[0].len);
            const action_slice = try allocator.alloc(Action, action_table.items.len * action_table.items[0].len);

            var goto_view = utils.Slice2d([]Action).init(goto_slice, goto_table.items[0].len);
            var action_view = utils.Slice2d([]Action).init(action_slice, action_table.items[0].len);

            for (goto_table.items, 0..) |row, i| {
                @memcpy(goto_view.row(i), row);
            }
            for (action_table.items, 0..) |row, i| {
                @memcpy(action_view.row(i), row);
            }

            const goto_const_view = utils.Slice2d([]Action).init(goto_slice, goto_table.items[0].len);
            const action_const_view = utils.Slice2d([]Action).init(action_slice, action_table.items[0].len);

            for (0..goto_table.items.len) |i| {
                allocator.free(goto_table.items[i]);
            }
            for (0..action_table.items.len) |i| {
                allocator.free(action_table.items[i]);
            }

            return .{ action_const_view, goto_const_view };
        }
    };
}

test "ParseTable.expandProductions [grammar1.0]" {
    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

    const V = TestVariable.fromString;
    const G = slr_grammar.Grammar(TestVariable, TestTerminal);
    const grammar = comptime G.initFromTuples(.{
        .{ V("S"), .{V("wff")} },
        .{ V("wff"), .{TestTerminal.Proposition} },
        .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
    }, V("S"), TestTerminal.End);

    const P = ParseTable(TestVariable, TestTerminal);

    const expected_variable_branches = &[_][]const ProductionInstance{
        &[_]ProductionInstance{},
        &[_]ProductionInstance{.{ .production = grammar.getRule(0), .cursor = 1 }},
    };

    const expected_terminal_branches = &[_][]const ProductionInstance{
        &[_]ProductionInstance{.{ .production = grammar.getRule(1), .cursor = 1 }},
        &[_]ProductionInstance{.{ .production = grammar.getRule(2), .cursor = 1 }},
        &[_]ProductionInstance{
            .{ .production = grammar.getRule(6), .cursor = 1 },
            .{ .production = grammar.getRule(5), .cursor = 1 },
            .{ .production = grammar.getRule(4), .cursor = 1 },
            .{ .production = grammar.getRule(3), .cursor = 1 },
        },
        &[_]ProductionInstance{},
        &[_]ProductionInstance{},
        &[_]ProductionInstance{},
        &[_]ProductionInstance{},
        &[_]ProductionInstance{},
        &[_]ProductionInstance{},
    };

    const start_productions = [_]ProductionInstance{ProductionInstance.fromProduction(grammar.getRule(0))};
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

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

    const V = TestVariable.fromString;
    const G = slr_grammar.Grammar(TestVariable, TestTerminal);
    const grammar = comptime G.initFromTuples(.{
        .{ V("S"), .{V("wff")} },
        .{ V("wff"), .{TestTerminal.Proposition} },
        .{ V("wff"), .{ TestTerminal.Not, V("wff") } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.And, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Or, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Cond, V("wff"), TestTerminal.RParen } },
        .{ V("wff"), .{ TestTerminal.LParen, V("wff"), TestTerminal.Bicond, V("wff"), TestTerminal.RParen } },
    }, V("S"), TestTerminal.End);

    const P = ParseTable(TestVariable, TestTerminal);

    // const expected_table = P {
    //     .grammar = grammar,
    //     .goto_table = utils.Slice2d([]P.Action).init(
    //         &[_] P.Action {
    //             .{.invalid = {}}, .{.state = 1},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.state = 5},
    //             .{.invalid = {}}, .{.state = 6},

    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.state = 11},
    //             .{.invalid = {}}, .{.state = 12},
    //             .{.invalid = {}}, .{.state = 13},

    //             .{.invalid = {}}, .{.state = 14},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},

    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}},
    //         },
    //         grammar.getVariableCount(),
    //     ),
    //     .action_table = utils.Slice2d([]P.Action).init(
    //         &[_]P.Action {
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.accept = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1}, .{.reduce = 1},
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},

    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2}, .{.reduce = 2},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 7}, .{.invalid = {}}, .{.state = 8}, .{.state = 9}, .{.state = 10},  .{.invalid = {}},
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},

    //             .{.state = 2}, .{.state = 3}, .{.state = 4}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 15}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 16}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 17}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.state = 18}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}},

    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3}, .{.reduce = 3},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4}, .{.reduce = 4},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5}, .{.reduce = 5},
    //             .{.invalid = {}}, .{.invalid = {}}, .{.invalid = {}}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6}, .{.reduce = 6},
    //         },
    //         grammar.getTerminalCount(),
    //     )
    // };

    const table = try P.init(std.testing.allocator, grammar);
    defer table.deinit(std.testing.allocator);

    // const table_comptime = comptime P.initComptime(grammar);
    table.printDebugTable();

    // try std.testing.expectEqualDeep(expected_table.goto_table, table.goto_table);
    // try std.testing.expectEqualDeep(expected_table.action_table, table.action_table);

    // try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    // try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);

}

test "Create parse table [grammar2.0]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestWffTerminal;

    const V = TestVariable.fromString;
    const G = slr_grammar.Grammar(TestVariable, TestTerminal);
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

    const P = ParseTable(TestVariable, TestTerminal);

    const table = try P.init(std.testing.allocator, grammar);
    defer table.deinit(std.testing.allocator);

    // const table_comptime = comptime P.initComptime(grammar);

    table.printDebugTable();

    //     try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    //     try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);
}

test "Create parse table [test-grammar-1]" {
    @setEvalBranchQuota(10000);

    const TestVariable = test_common.TestVariable;
    const TestTerminal = test_common.TestTerminal;

    const V = TestVariable.fromString;
    const T = TestTerminal.fromString;
    const G = slr_grammar.Grammar(TestVariable, TestTerminal);
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

    const P = ParseTable(TestVariable, TestTerminal);

    const table = try P.init(std.testing.allocator, grammar);
    defer table.deinit(std.testing.allocator);

    // const table_comptime = comptime P.initComptime(grammar);

    table.printDebugTable();

    //     try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    //     try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);
}

// test "generateTables2" {
//     const TestVariable = test_common.TestVariable;
//     const TestTerminal = test_common.TestTerminal;

//     const V = TestVariable.fromString;
//     const T = TestTerminal.fromString;
//     const G = slr_grammar.Grammar(TestVariable, TestTerminal);
//     const grammar = comptime G.initFromTuples(
//         .{
//             .{ V("S"), .{ V("A") } },

//             .{ V("A"), .{ T("a"), V("B"), T("c") } },
//             .{ V("A"), .{ T("a"), V("B"), T("d"), T("e")} },
//             .{ V("A"), .{ T("a"), V("B"), T("d"), T("f")} },

//             .{ V("D"), .{ T("q") } },
//         },
//         V("S"),
//         T("$"),
//     );

//     const P = ParseTable(TestVariable, TestTerminal);

//     const action_table = try std.testing.allocator.alloc(P.Action, grammar.getTerminalCount() * 20);
//     const goto_table = try std.testing.allocator.alloc(P.Action, grammar.getVariableCount() * 20);
//     const state_count = try std.testing.allocator.alloc(usize, grammar.rules.len);
//     try P.generateTables3(
//         std.testing.allocator,
//         grammar,
//     );
// }
