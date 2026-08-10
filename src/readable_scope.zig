const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");

pub const Scope = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    reachable_blocks: []bool,
    reachable_instructions: []bool,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !Scope {
        const reachable_blocks = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(reachable_blocks);
        @memset(reachable_blocks, true);
        const reachable_instructions = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(reachable_instructions);
        @memset(reachable_instructions, true);

        for (program.functions) |function| {
            cfg.markReachable(allocator, program, function, reachable_blocks) catch |err| switch (err) {
                error.InvalidCfg => continue,
                error.OutOfMemory => return error.OutOfMemory,
            };
            for (function.blocks) |block_id| {
                if (block_id.index() >= program.blocks.len) continue;
                const block_reachable = reachable_blocks[block_id.index()];
                reachable_blocks[block_id.index()] = block_reachable;
                for (program.blocks[block_id.index()].instructions) |instruction_id| {
                    if (instruction_id.index() < reachable_instructions.len) {
                        reachable_instructions[instruction_id.index()] = block_reachable;
                    }
                }
            }
        }
        return .{
            .allocator = allocator,
            .program = program,
            .reachable_blocks = reachable_blocks,
            .reachable_instructions = reachable_instructions,
        };
    }

    pub fn deinit(self: *Scope) void {
        self.allocator.free(self.reachable_blocks);
        self.allocator.free(self.reachable_instructions);
        self.* = undefined;
    }

    pub fn block(self: *const Scope, block_id: ir.BlockId) bool {
        if (block_id.index() >= self.reachable_blocks.len) return true;
        return self.reachable_blocks[block_id.index()];
    }

    pub fn instruction(self: *const Scope, instruction_id: ir.InstructionId) bool {
        if (instruction_id.index() >= self.reachable_instructions.len) return true;
        return self.reachable_instructions[instruction_id.index()];
    }

    pub fn valuePack(self: *const Scope, pack_id: ir.ValuePackId) bool {
        if (pack_id.index() >= self.program.value_packs.len) return true;
        return switch (self.program.value_packs[pack_id.index()].origin) {
            .varargs => true,
            .instruction_result => |instruction_id| self.instruction(instruction_id),
        };
    }

    pub fn entity(self: *const Scope, subject: ir.EntityRef) bool {
        return switch (subject) {
            .program, .function, .place, .capture, .external_binding => true,
            .block => |block_id| self.block(block_id),
            .instruction => |instruction_id| self.instruction(instruction_id),
            .value => |value_id| self.value(value_id),
            .value_pack => |pack_id| self.valuePack(pack_id),
        };
    }

    pub fn obligationSubject(self: *const Scope, subject: ir.ObligationSubject) bool {
        return switch (subject) {
            .program, .function, .place, .capture, .external_binding => true,
            .block => |block_id| self.block(block_id),
            .instruction => |instruction_id| self.instruction(instruction_id),
            .value => |value_id| self.value(value_id),
            .value_pack => |pack_id| self.valuePack(pack_id),
            .control_branch => |control| self.block(control.block),
        };
    }

    pub fn value(self: *const Scope, value_id: ir.ValueId) bool {
        if (value_id.index() >= self.program.values.len) return true;
        return switch (self.program.values[value_id.index()].origin) {
            .instruction_result => |origin| self.instruction(origin.instruction),
            .block_parameter => |origin| self.block(origin.block),
            .parameter, .capture => true,
        };
    }
};

test "readable scope reachability matches full CFG analysis" {
    const fixtures = @import("fixtures.zig");
    const program = &fixtures.arithmetic_module.program;
    var scope = try Scope.init(std.testing.allocator, program);
    defer scope.deinit();

    for (program.functions) |function| {
        var analysis = try cfg.Analysis.init(std.testing.allocator, program, function);
        defer analysis.deinit();
        for (function.blocks) |block_id| {
            try std.testing.expectEqual(analysis.isReachable(block_id), scope.block(block_id));
            for (program.blocks[block_id.index()].instructions) |instruction_id| {
                try std.testing.expectEqual(analysis.isReachable(block_id), scope.instruction(instruction_id));
            }
        }
    }
}
