--!strict

-- The per-function scope of the structure-feedback decline on a
-- published IR. It reads an author-written fixture, its resolve-ir output and the resolve-ir output of the control
-- fixture (luau/fixtures/feedback_decline_worker_ok.lifter-ir.json: function 0 plans, function 1 is the same worker),
-- prints one line and fails unless
--   (a) function 0 of the resolved IR keeps the block list of function 0 of the fixture (a declined function is
--       published with its feedback-start blocks),
--   (b) no edge rewrite of the resolved IR has its source block in function 0, and
--   (c) function 1 of the resolved IR has the block list of function 1 of the control, and the edge rewrites of the
--       resolved IR equal those of the control in order (rule, source, kind, from, to, node split group): the worker
--       beside a declined function is published as it is beside a function that plans.
-- Usage: lune run luau/feedback_decline_audit.luau <fixture-name> <fixture.json> <resolved.json> <control-resolved.json>
local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local USAGE =
	"usage: lune run luau/feedback_decline_audit.luau <fixture-name> <fixture.json> <resolved.json> <control-resolved.json>"

local fixtureName = assert(process.args[1], USAGE)
local fixture: any = serde.decode("json", fs.readFile(assert(process.args[2], USAGE)))
local resolved: any = serde.decode("json", fs.readFile(assert(process.args[3], USAGE)))
local control: any = serde.decode("json", fs.readFile(assert(process.args[4], USAGE)))

local function listText(list: any): string
	local parts = {}
	for _, value in list do
		table.insert(parts, tostring(value))
	end
	return table.concat(parts, ",")
end

local function edgeText(edge: any): string
	return `b{edge.target}({listText(edge.arguments)})`
end

local function rewritesText(program: any): string
	local parts = {}
	for _, rewrite in program.edge_rewrites do
		table.insert(
			parts,
			`{rewrite.rule} src=b{rewrite.source}.{rewrite.kind} from={edgeText(rewrite.from)} to={edgeText(rewrite.to)} group={tostring(rewrite.node_split_group)}`
		)
	end
	return table.concat(parts, "; ")
end

local functionZeroBlocks = resolved.functions[1].blocks
local sourcedInFunctionZero = 0
for _, rewrite in resolved.edge_rewrites do
	if table.find(functionZeroBlocks, rewrite.source) ~= nil then
		sourcedInFunctionZero += 1
	end
end

print(
	`semantic-lifter-feedback-decline fixture={fixtureName} function0_blocks={#functionZeroBlocks} rewrites={#resolved.edge_rewrites} worker_blocks={#resolved.functions[2].blocks}`
)
assert(
	listText(functionZeroBlocks) == listText(fixture.functions[1].blocks),
	`{fixtureName}: function 0 does not keep the block list of the fixture`
)
assert(sourcedInFunctionZero == 0, `{fixtureName}: an edge rewrite has its source in function 0`)
assert(
	listText(resolved.functions[2].blocks) == listText(control.functions[2].blocks),
	`{fixtureName}: the worker block list differs from the control`
)
assert(
	rewritesText(resolved) == rewritesText(control),
	`{fixtureName}: the edge rewrites differ from the control: {rewritesText(resolved)} against {rewritesText(control)}`
)
