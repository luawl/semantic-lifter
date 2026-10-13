--!strict

-- Re-resolution fixed-point audit for `resolve-ir`, run on the recorded nested graph.
--
-- Usage: lune run luau/irreducible_nested_reresolve_audit.luau <resolved> <reresolved> <third> <renormalized>
--
-- The build wires four `semantic-lifter` runs on luau/fixtures/nested_inner_cycle_w1.lifter-ir.json:
--   resolve-ir   <input>       -> <resolved>
--   resolve-ir   <resolved>    -> <reresolved>
--   resolve-ir   <reresolved>  -> <third>
--   normalize-ir <resolved>    -> <renormalized>
-- Then this audit asserts, in order:
--   (a) <resolved> and <reresolved> are byte-identical     (re-resolution is byte-idempotent);
--   (b) <reresolved> and <third> are byte-identical        (the fixed point does not oscillate);
--   (c) <renormalized> has the same block count and the    (the resolver's output is already a
--       same edge_rewrites count as <resolved>              normalizer fixed point).
-- It compares bytes, not a canonical form: resolve-ir is deterministic across builds and modes, and
-- the differences between passes are additions, not renumberings, so a canonical form would hide them
-- (the comparison below is therefore byte for byte).

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local USAGE =
	"usage: lune run luau/irreducible_nested_reresolve_audit.luau <resolved> <reresolved> <third> <renormalized>"

local resolvedPath = assert(process.args[1], USAGE)
local reresolvedPath = assert(process.args[2], USAGE)
local thirdPath = assert(process.args[3], USAGE)
local renormalizedPath = assert(process.args[4], USAGE)

local resolved = fs.readFile(resolvedPath)
local reresolved = fs.readFile(reresolvedPath)
local third = fs.readFile(thirdPath)

-- (a) byte-idempotent re-resolution.
assert(resolved == reresolved, "re-resolution is not byte-idempotent")
-- (b) the fixed point does not oscillate under a further re-resolution.
assert(reresolved == third, "re-resolution oscillates past its fixed point")

-- (c) the resolver's output is already a normalizer fixed point.
local resolvedProgram: any = serde.decode("json", resolved)
local renormalizedProgram: any = serde.decode("json", fs.readFile(renormalizedPath))
assert(
	#renormalizedProgram.blocks == #resolvedProgram.blocks,
	"re-normalizing the resolved IR changed the block count"
)
assert(
	#renormalizedProgram.edge_rewrites == #resolvedProgram.edge_rewrites,
	"re-normalizing the resolved IR changed the edge-rewrite count"
)

print(
	`irreducible_nested_reresolve_audit: ok (re-resolution byte-idempotent; `
		.. `{#resolvedProgram.blocks} blocks, {#resolvedProgram.edge_rewrites} edge rewrites; normalizer fixed point)`
)
