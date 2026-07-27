const std = @import("std");
const cfg = @import("cfg.zig");
const ir = @import("ir.zig");

/// Nearest explicit writes that can reach one place read through the admitted
/// intraprocedural CFG. `reaches_entry` preserves the path where the place's
/// incoming or initial value reaches the read without an explicit write.
pub const DirectReachingWrites = struct {
    allocator: std.mem.Allocator,
    place: ir.PlaceId,
    reaches_entry: bool,
    writes: []ir.InstructionId,

    pub fn deinit(self: *DirectReachingWrites) void {
        self.allocator.free(self.writes);
        self.* = undefined;
    }
};

pub fn analyzeDirectReachingWrites(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    read_id: ir.InstructionId,
) cfg.AnalysisError!?DirectReachingWrites {
    if (!validId(read_id, program.instructions.len)) return null;
    const read = program.instructions[read_id.index()];
    const place_id = switch (read.operation) {
        .place_read => |place| place,
        else => return null,
    };
    if (!validId(place_id, program.places.len) or !validId(read.block, program.blocks.len)) return null;

    const read_block = program.blocks[read.block.index()];
    if (!validId(read_block.function, program.functions.len) or
        program.places[place_id.index()].function != read_block.function) return null;
    const function = program.functions[read_block.function.index()];

    var read_position: ?usize = null;
    for (read_block.instructions, 0..) |instruction_id, position| {
        if (instruction_id == read_id) {
            read_position = position;
            break;
        }
    }
    const position = read_position orelse return null;

    var analysis = try cfg.Analysis.init(allocator, program, function);
    defer analysis.deinit();
    if (!analysis.isReachable(read.block)) return null;

    const candidate_writes = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(candidate_writes);
    @memset(candidate_writes, false);

    const visited_full_blocks = try allocator.alloc(bool, function.blocks.len);
    defer allocator.free(visited_full_blocks);
    @memset(visited_full_blocks, false);

    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    var reaches_entry = false;

    if (lastWriteBefore(program, read_block, position, place_id)) |write_id| {
        candidate_writes[write_id.index()] = true;
    } else {
        if (read.block == function.entry_block) reaches_entry = true;
        try appendPredecessors(&analysis, read.block, visited_full_blocks, &pending);
    }

    while (pending.pop()) |block_id| {
        const block = program.blocks[block_id.index()];
        if (lastWriteBefore(program, block, block.instructions.len, place_id)) |write_id| {
            candidate_writes[write_id.index()] = true;
            continue;
        }
        if (block_id == function.entry_block) reaches_entry = true;
        try appendPredecessors(&analysis, block_id, visited_full_blocks, &pending);
    }

    var write_count: usize = 0;
    for (candidate_writes) |candidate| if (candidate) {
        write_count += 1;
    };
    const writes = try allocator.alloc(ir.InstructionId, write_count);
    errdefer allocator.free(writes);
    var write_index: usize = 0;
    for (candidate_writes, 0..) |candidate, instruction_index| {
        if (!candidate) continue;
        writes[write_index] = ir.InstructionId.fromIndex(instruction_index);
        write_index += 1;
    }

    return .{
        .allocator = allocator,
        .place = place_id,
        .reaches_entry = reaches_entry,
        .writes = writes,
    };
}

fn appendPredecessors(
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
    visited_full_blocks: []bool,
    pending: *std.ArrayList(ir.BlockId),
) std.mem.Allocator.Error!void {
    for (0..analysis.predecessorCount(block_id)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(block_id, predecessor_index) orelse continue;
        const local_index = analysis.blockIndex(predecessor) orelse continue;
        if (visited_full_blocks[local_index]) continue;
        visited_full_blocks[local_index] = true;
        try pending.append(analysis.allocator, predecessor);
    }
}

fn lastWriteBefore(
    program: *const ir.Program,
    block: ir.Block,
    end: usize,
    place_id: ir.PlaceId,
) ?ir.InstructionId {
    var position = @min(end, block.instructions.len);
    while (position != 0) {
        position -= 1;
        const instruction_id = block.instructions[position];
        if (!validId(instruction_id, program.instructions.len)) continue;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.block != block.id) continue;
        const write = switch (instruction.operation) {
            .place_write => |value| value,
            else => continue,
        };
        if (write.place == place_id) return instruction_id;
    }
    return null;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

test "direct reaching writes keep only the latest straight-line write" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const first_write = ir.InstructionId.fromIndex(0);
    const second_write = ir.InstructionId.fromIndex(1);
    const read_id = ir.InstructionId.fromIndex(2);
    const place_id = ir.PlaceId.fromIndex(0);
    const first = ir.ValueId.fromIndex(0);
    const second = ir.ValueId.fromIndex(1);
    const snapshot = ir.ValueId.fromIndex(2);
    const instructions = [_]ir.Instruction{
        .{ .id = first_write, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = first } }, .results = &.{}, .effects = .place_write },
        .{ .id = second_write, .block = block_id, .operation = .{ .place_write = .{ .place = place_id, .value = second } }, .results = &.{}, .effects = .place_write },
        .{ .id = read_id, .block = block_id, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read },
    };
    const blocks = [_]ir.Block{.{ .id = block_id, .function = function_id, .instructions = &.{ first_write, second_write, read_id }, .terminator = .{ .return_values = &.{snapshot} } }};
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{ first, second }, .local_places = &.{place_id}, .blocks = &.{block_id}, .entry_block = block_id }};
    const values = [_]ir.Value{
        .{ .id = first, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = second, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = snapshot, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .origin = .{ .local = 0 } }};
    const program: ir.Program = .{ .program_id = "direct-place-flow", .entry_function = function_id, .functions = &functions, .blocks = &blocks, .instructions = &instructions, .values = &values, .places = &places };

    var result = (try analyzeDirectReachingWrites(std.testing.allocator, &program, read_id)).?;
    defer result.deinit();
    try std.testing.expect(!result.reaches_entry);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{second_write}, result.writes);
}

test "direct reaching writes merge explicit predecessor generations" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const join = ir.BlockId.fromIndex(3);
    const seed_write = ir.InstructionId.fromIndex(0);
    const branch_write = ir.InstructionId.fromIndex(1);
    const read_id = ir.InstructionId.fromIndex(2);
    const place_id = ir.PlaceId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(0);
    const branch = ir.ValueId.fromIndex(1);
    const condition = ir.ValueId.fromIndex(2);
    const snapshot = ir.ValueId.fromIndex(3);
    const instructions = [_]ir.Instruction{
        .{ .id = seed_write, .block = entry, .operation = .{ .place_write = .{ .place = place_id, .value = seed } }, .results = &.{}, .effects = .place_write },
        .{ .id = branch_write, .block = then_block, .operation = .{ .place_write = .{ .place = place_id, .value = branch } }, .results = &.{}, .effects = .place_write },
        .{ .id = read_id, .block = join, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{seed_write}, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = then_block }, .else_edge = .{ .target = else_block } } } },
        .{ .id = then_block, .function = function_id, .instructions = &.{branch_write}, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = else_block, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = join, .function = function_id, .instructions = &.{read_id}, .terminator = .{ .return_values = &.{snapshot} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{ seed, branch, condition }, .local_places = &.{place_id}, .blocks = &.{ entry, then_block, else_block, join }, .entry_block = entry }};
    const values = [_]ir.Value{
        .{ .id = seed, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = branch, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = snapshot, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .origin = .{ .local = 0 } }};
    const program: ir.Program = .{ .program_id = "diamond-place-flow", .entry_function = function_id, .functions = &functions, .blocks = &blocks, .instructions = &instructions, .values = &values, .places = &places };

    var result = (try analyzeDirectReachingWrites(std.testing.allocator, &program, read_id)).?;
    defer result.deinit();
    try std.testing.expect(!result.reaches_entry);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{ seed_write, branch_write }, result.writes);
}

test "direct reaching writes preserve entry and loop-carried paths" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const exit_block = ir.BlockId.fromIndex(2);
    const read_id = ir.InstructionId.fromIndex(0);
    const loop_write = ir.InstructionId.fromIndex(1);
    const place_id = ir.PlaceId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(0);
    const replacement = ir.ValueId.fromIndex(1);
    const snapshot = ir.ValueId.fromIndex(2);
    const instructions = [_]ir.Instruction{
        .{ .id = read_id, .block = header, .operation = .{ .place_read = place_id }, .results = &.{snapshot}, .effects = .place_read },
        .{ .id = loop_write, .block = body, .operation = .{ .place_write = .{ .place = place_id, .value = replacement } }, .results = &.{}, .effects = .place_write },
    };
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .instructions = &.{read_id}, .terminator = .{ .branch = .{ .condition = condition, .then_edge = .{ .target = body }, .else_edge = .{ .target = exit_block } } } },
        .{ .id = body, .function = function_id, .instructions = &.{loop_write}, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{snapshot} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .parameters = &.{ condition, replacement }, .local_places = &.{place_id}, .blocks = &.{ header, body, exit_block }, .entry_block = header }};
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = replacement, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = snapshot, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } } },
    };
    const places = [_]ir.Place{.{ .id = place_id, .function = function_id, .origin = .{ .local = 0 } }};
    const program: ir.Program = .{ .program_id = "loop-place-flow", .entry_function = function_id, .functions = &functions, .blocks = &blocks, .instructions = &instructions, .values = &values, .places = &places };

    var result = (try analyzeDirectReachingWrites(std.testing.allocator, &program, read_id)).?;
    defer result.deinit();
    try std.testing.expect(result.reaches_entry);
    try std.testing.expectEqualSlices(ir.InstructionId, &.{loop_write}, result.writes);
}
