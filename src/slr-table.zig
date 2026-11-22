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

pub fn ParseTable(comptime Variable: type, comptime Terminal: type) type {
    return struct {
        const Self = @This();
        const GrammarType = slr_grammar.Grammar(Variable, Terminal);
        const Action = union(enum) {
            state: RowInt,
            reduce: slr_grammar.RuleId,
            invalid,
            accept,
        };

        pub const RowInt = usize;

        grammar: GrammarType,
        table: utils.Slice2d([]Action), // TODO add const back

        pub fn init(allocator: std.mem.Allocator, grammar: GrammarType) !Self {
            return Self{
                .grammar = grammar,
                .table = try generateTable(allocator, grammar),
            };
        }

        // TODO: initComptime ?

        /// Note: Does NOT free the memory associated with the grammar
        pub fn deinit(self: Self, allocator: std.mem.Allocator) void {
            allocator.free(self.table.slice);
        }

        pub fn getStartState(_: Self) RowInt {
            return 0;
        }

        pub fn lookupSymbol(self: Self, state: RowInt, symbol: slr_grammar.Symbol) Action {
            return switch (symbol) {
                .terminal => |t_id| self.action_table.row(state)[t_id],
                .variable => |v_id| self.goto_table.row(state)[v_id],
            };
        }

        pub fn lookupVariable(self: Self, state: RowInt, variable: Variable) ?Action {
            const symbol = self.grammar.getSymbolIdFromVariable(variable) orelse return null;
            return self.lookupSymbol(state, symbol);
        }

        pub fn lookupTerminal(self: Self, state: RowInt, terminal: Terminal) ?Action {
            const symbol = self.grammar.getSymbolIdFromTerminal(terminal) orelse return null;
            return self.lookupSymbol(state, symbol);
        }

        fn printDebugTable(self: Self) void {
            const COL_SPACE = "4";
            std.debug.print("\n{s: ^" ++ COL_SPACE ++ "} ||", .{""});
            for (self.grammar.variables) |t| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{t.getString()});
            }
            std.debug.print("|", .{});
            for (self.grammar.terminals) |v| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{v.getString()});
            }
            std.debug.print("|", .{});

            var it = self.table.iterRows();
            var s: usize = 0;
            while (it.next()) |row| : (s += 1) {
                std.debug.print("\n{d: >" ++ COL_SPACE ++ "} ||", .{s});
                for (row[0..self.grammar.getVariableCount()]) |entry| switch (entry) {
                    .state => |state_num| std.debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| std.debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                std.debug.print("|", .{});
                for (row[self.grammar.getVariableCount()..self.grammar.getSymbolCount()]) |entry| switch (entry) {
                    .state => |state_num| std.debug.print(" {d: ^" ++ COL_SPACE ++ "} |", .{state_num}),
                    .reduce => |rule_num| std.debug.print("R{d: ^" ++ COL_SPACE ++ "} |", .{rule_num}),
                    .accept => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{"ACC"}),
                    .invalid => std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{""}),
                };
                std.debug.print("| {d: <" ++ COL_SPACE ++ "}", .{s});
            }
            std.debug.print("\n", .{});
        }

        fn generateTable(
            allocator: std.mem.Allocator,
            grammar: GrammarType,
        ) !utils.Slice2d([]Action) {
            var closures = try grammar.computeEpsilonClosures(allocator);
            defer closures.deinit(allocator);

            var parse_table = std.ArrayList([]Action).empty;
            defer {
                for (parse_table.items) |row| allocator.free(row);
                parse_table.deinit(allocator);
            }

            // Only store kernels, not entire set
            const ArrayHashMapType = std.array_hash_map.Custom(
                []GrammarType.NfaView.StateId,
                void,
                struct {
                    pub fn hash(_: @This(), key: []GrammarType.NfaView.StateId) u32 {
                        return @truncate(std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(key)));
                    }
                    pub fn eql(_: @This(), a: []GrammarType.NfaView.StateId, b: []GrammarType.NfaView.StateId, _: usize) bool {
                        return std.mem.eql(GrammarType.NfaView.StateId, a, b);
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
                    GrammarType.NfaView.StateId,
                    &[_]GrammarType.NfaView.StateId{@enumFromInt(0)},
                ),
                {},
            );

            // Now populate the table: add new rows until all state sets
            // accounted for
            var row_state_sets: []std.ArrayList(GrammarType.NfaView.StateId) = try allocator.alloc(
                std.ArrayList(GrammarType.NfaView.StateId),
                grammar.getSymbolCount(),
            );
            for (row_state_sets) |*set| {
                set.* = .empty;
            }
            defer {
                for (row_state_sets) |*set| set.deinit(allocator);
                allocator.free(row_state_sets);
            }

            const nfa = grammar.nfa();
            var state: RowInt = 0;
            while (state < table_state_sets.count()) : (state += 1) {
                const nfa_kernels = table_state_sets.entries.get(state).key;

                for (row_state_sets) |*set| {
                    set.items.len = 0;
                }

                try parse_table.ensureUnusedCapacity(allocator, 1);
                var table_row = try allocator.alloc(Action, grammar.getSymbolCount());
                // Append right away so memory deallocation will be handled by
                // table cleanup if we encounter an error.
                parse_table.appendAssumeCapacity(table_row);
                @memset(table_row, .invalid);

                // Populate NFA state sets in the row
                for (nfa_kernels) |kernel_nfa_state| {
                    // First deal with symbol being read in the kernel state
                    const kernel_symbol_id = nfa.symbolIdFromState(kernel_nfa_state) orelse continue;
                    try row_state_sets[@intFromEnum(kernel_symbol_id)].append(allocator, @enumFromInt(@intFromEnum(kernel_nfa_state) + 1));
                    switch (grammar.getSymbolType(kernel_symbol_id)) {
                        .terminal => continue,
                        .variable => {},
                    }

                    // We only get here if kernel_symbol_id is for a variable
                    const kernel_closure = closures.row(@intFromEnum(kernel_symbol_id));
                    for (kernel_closure) |nfa_state| {
                        const reading_symbol_id = nfa.symbolIdFromState(nfa_state).?;
                        const next_state_id: GrammarType.NfaView.StateId = @enumFromInt(@intFromEnum(nfa_state) + 1);

                        const found = std.mem.findScalar(
                            GrammarType.NfaView.StateId,
                            row_state_sets[@intFromEnum(reading_symbol_id)].items,
                            next_state_id,
                        );
                        if (found == null) {
                            try row_state_sets[@intFromEnum(reading_symbol_id)].append(allocator, next_state_id);
                        }
                    }
                }

                for (row_state_sets) |*set| {
                    std.mem.sortUnstable(
                        GrammarType.NfaView.StateId,
                        set.items,
                        {},
                        struct {
                            pub fn asc(_: void, a: GrammarType.NfaView.StateId, b: GrammarType.NfaView.StateId) bool {
                                return @intFromEnum(a) < @intFromEnum(b);
                            }
                        }.asc,
                    );
                }

                // Look at NFA state sets in the current row: skip existing
                // ones, and create new states (new rows in the parse table) for
                // new ones
                for (row_state_sets, 0..) |set, symbol_id| {
                    if (set.items.len == 0) {
                        continue;
                    }
                    std.debug.assert(table_row[symbol_id] == .invalid);
                    if (table_state_sets.getIndex(set.items)) |state_id| {
                        table_row[symbol_id] = Action{ .state = state_id };
                    } else {
                        const new_state_id = table_state_sets.count();
                        try table_state_sets.put(
                            allocator,
                            try allocator.dupe(GrammarType.NfaView.StateId, set.items),
                            {},
                        );
                        table_row[symbol_id] = Action{ .state = new_state_id };
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

                    const rule_id = nfa.ruleIdFromStateId(nfa_state);
                    const rule = grammar.getRule(rule_id);
                    for (follow_set.row(@intFromEnum(rule.lhs)), 0..) |is_in_follow_set, t_idx| {
                        if (!is_in_follow_set) {
                            continue;
                        }

                        const symbol_idx = @intFromEnum(grammar.terminalIdToSymbolId(@enumFromInt(t_idx)));
                        parse_table.items[state_id][symbol_idx] = try switch (parse_table.items[state_id][symbol_idx]) {
                            .invalid => Action{ .reduce = rule_id },
                            .state => TableGeneratorError.shiftReduceError,
                            .reduce => TableGeneratorError.shiftReduceError,
                            .accept => unreachable,
                        };
                    }
                }
            }

            var parse_table_final = utils.Slice2d([]Action).init(
                try allocator.alloc(Action, parse_table.items.len * grammar.getSymbolCount()),
                grammar.getSymbolCount(),
            );
            errdefer allocator.free(parse_table_final.slice);
            for (parse_table.items, 0..) |row, i| {
                @memcpy(parse_table_final.row(i), row);
            }

            return parse_table_final;
        }
    };
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
            .{ V("S"), .{ V("wff1"), } },

            .{ V("wff1"), .{ V("wff2"), } },
            .{ V("wff1"), .{ V("wff1"), TestTerminal.Bicond, V("wff2") } },

            .{ V("wff2"), .{ V("wff3"), } },
            .{ V("wff2"), .{ V("wff2"), TestTerminal.Cond, V("wff3") } },

            .{ V("wff3"), .{ V("wff4"), } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.Or, V("wff4") } },
            .{ V("wff3"), .{ V("wff3"), TestTerminal.And, V("wff4") } },

            .{ V("wff4"), .{ V("prop"), } },
            .{ V("wff4"), .{ TestTerminal.Not, V("wff4") } },

            .{ V("prop"), .{ TestTerminal.LParen, V("wff1"), TestTerminal.RParen } },
            .{ V("prop"), .{ TestTerminal.Proposition}, },
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
