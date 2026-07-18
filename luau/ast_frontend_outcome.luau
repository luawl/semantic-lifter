--!strict

-- Shared expression-lowering control contract. Payloads stay frontend-local;
-- only admitted semantic operations and terminators cross into lifter IR.

local AstFrontendOutcome = {}

export type Value = {
	kind: "value",
	value: any,
}

export type OpenPack = {
	kind: "open_pack",
	pack: number,
	exact_types: { any }?,
}

export type Effect = {
	kind: "effect",
}

export type Terminated = {
	kind: "terminated",
}

export type Outcome = Value | OpenPack | Effect | Terminated

local effectOutcome: Effect = table.freeze({ kind = "effect" :: "effect" })
local terminatedOutcome: Terminated = table.freeze({ kind = "terminated" :: "terminated" })

function AstFrontendOutcome.value(value: any): Value
	return { kind = "value", value = value }
end

function AstFrontendOutcome.openPack(pack: number, exactTypes: { any }?): OpenPack
	return { kind = "open_pack", pack = pack, exact_types = exactTypes }
end

function AstFrontendOutcome.effect(): Effect
	return effectOutcome
end

function AstFrontendOutcome.terminated(): Terminated
	return terminatedOutcome
end

return table.freeze(AstFrontendOutcome)
