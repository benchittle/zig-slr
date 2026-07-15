const std = @import("std");

const slr_grammar = @import("slr-grammar.zig");
const test_common = @import("test-common.zig");

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

        pub fn lookupSymbol(self: Self, state: StateIdx, symbol: slr_grammar.SymbolId) Action {
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
            std.debug.print("\n{s: ^" ++ COL_SPACE ++ "} ||", .{""});
            for (self.grammar.terminals) |t| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{t.getString()});
            }
            std.debug.print("|", .{});
            for (self.grammar.variables) |v| {
                std.debug.print(" {s: ^" ++ COL_SPACE ++ "} |", .{v.getString()});
            }
            std.debug.print("|", .{});

            for (self.action_table, self.goto_table, 0..) |action_row, goto_row, s| {
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
    defer table.deinit();

    const table_comptime = comptime P.initComptime(grammar);
    defer table_comptime.deinit();

    // table.printDebugTable();

    try std.testing.expectEqualDeep(table.action_table, table_comptime.action_table);
    try std.testing.expectEqualDeep(table.goto_table, table_comptime.goto_table);
}
