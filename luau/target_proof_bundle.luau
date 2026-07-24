--!strict

-- Owns frontend-private proof framing and detached bundle admission. Signature
-- verification is injected so the reusable Luau boundary does not own a
-- native cryptographic implementation.

local TargetProofBundle = {}

TargetProofBundle.maxAccessPathKeys = 64
TargetProofBundle.maxResultOrdinal = 64
TargetProofBundle.maxProofContentBytes = 65536
TargetProofBundle.maxBundleBytes = 1024 * 1024
TargetProofBundle.maxBundleContentBytes = 512 * 1024
TargetProofBundle.maxBundleEntries = 256
TargetProofBundle.maxEntryBindings = 256
TargetProofBundle.maxBundleBindings = 4096

type Record = { [string]: any }

export type Evidence = {
	kind: string,
	locator: string,
	digest: string?,
}

export type Input = {
	bytes: string,
	decode: (bytes: string) -> any,
	trusted_public_key: string,
	verify_signature: (message: string, signature: string, trustedPublicKey: string) -> boolean,
}

export type Entry = {
	id: string,
	content: string,
	binding_digests: { [string]: boolean },
}

export type Bundle = {
	evidence: Evidence,
	by_id: { [string]: Entry },
	used_ids: { [string]: boolean },
	used_binding_digests: { [string]: boolean },
	resolve: (self: Bundle, id: string, bindingDigest: string, label: string) -> Entry,
	assertFullyUsed: (self: Bundle, label: string) -> (),
}

local wordModulus = 4294967296
local roundConstants: { number } = {
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
	0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
	0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
	0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
	0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
	0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
	0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
	0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}

local function add2(left: number, right: number): number
	return (left + right) % wordModulus
end

local function add4(a: number, b: number, c: number, d: number): number
	return (a + b + c + d) % wordModulus
end

local function add5(a: number, b: number, c: number, d: number, e: number): number
	return (a + b + c + d + e) % wordModulus
end

function TargetProofBundle.sha256(input: string): string
	local byteLength = #input
	local paddedLength = byteLength + 1 + 8
	local remainder = paddedLength % 64
	if remainder ~= 0 then
		paddedLength += 64 - remainder
	end
	local bytes: { number } = table.create(paddedLength, 0)
	for index = 1, byteLength do
		local value = string.byte(input, index)
		assert(value ~= nil)
		bytes[index] = value
	end
	bytes[byteLength + 1] = 0x80
	local bitLength = byteLength * 8
	local high = math.floor(bitLength / wordModulus)
	local low = bitLength % wordModulus
	for offset = 0, 3 do
		bytes[paddedLength - 7 + offset] = bit32.band(bit32.rshift(high, 24 - offset * 8), 0xff)
		bytes[paddedLength - 3 + offset] = bit32.band(bit32.rshift(low, 24 - offset * 8), 0xff)
	end

	local hashes: { number } = {
		0x6a09e667,
		0xbb67ae85,
		0x3c6ef372,
		0xa54ff53a,
		0x510e527f,
		0x9b05688c,
		0x1f83d9ab,
		0x5be0cd19,
	}
	local schedule: { number } = table.create(64, 0)
	for blockStart = 1, paddedLength, 64 do
		for index = 1, 16 do
			local start = blockStart + (index - 1) * 4
			schedule[index] = bit32.bor(
				bit32.lshift(bytes[start], 24),
				bit32.lshift(bytes[start + 1], 16),
				bit32.lshift(bytes[start + 2], 8),
				bytes[start + 3]
			)
		end
		for index = 17, 64 do
			local prior15 = schedule[index - 15]
			local prior2 = schedule[index - 2]
			local sigma0 = bit32.bxor(bit32.rrotate(prior15, 7), bit32.rrotate(prior15, 18), bit32.rshift(prior15, 3))
			local sigma1 = bit32.bxor(bit32.rrotate(prior2, 17), bit32.rrotate(prior2, 19), bit32.rshift(prior2, 10))
			schedule[index] = add4(schedule[index - 16], sigma0, schedule[index - 7], sigma1)
		end

		local a, b, c, d = hashes[1], hashes[2], hashes[3], hashes[4]
		local e, f, g, h = hashes[5], hashes[6], hashes[7], hashes[8]
		for index = 1, 64 do
			local upperSigma1 = bit32.bxor(bit32.rrotate(e, 6), bit32.rrotate(e, 11), bit32.rrotate(e, 25))
			local choose = bit32.bxor(bit32.band(e, f), bit32.band(bit32.bnot(e), g))
			local temporary1 = add5(h, upperSigma1, choose, roundConstants[index], schedule[index])
			local upperSigma0 = bit32.bxor(bit32.rrotate(a, 2), bit32.rrotate(a, 13), bit32.rrotate(a, 22))
			local majority = bit32.bxor(bit32.band(a, b), bit32.band(a, c), bit32.band(b, c))
			local temporary2 = add2(upperSigma0, majority)
			h = g
			g = f
			f = e
			e = add2(d, temporary1)
			d = c
			c = b
			b = a
			a = add2(temporary1, temporary2)
		end
		hashes[1] = add2(hashes[1], a)
		hashes[2] = add2(hashes[2], b)
		hashes[3] = add2(hashes[3], c)
		hashes[4] = add2(hashes[4], d)
		hashes[5] = add2(hashes[5], e)
		hashes[6] = add2(hashes[6], f)
		hashes[7] = add2(hashes[7], g)
		hashes[8] = add2(hashes[8], h)
	end

	local encoded = table.create(8)
	for index, value in hashes do
		encoded[index] = string.format("%08x", value)
	end
	return table.concat(encoded)
end

local function proofComponent(value: string): string
	return tostring(#value) .. ":" .. value
end

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an object`)
	return value :: Record
end

local function expectString(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must be a non-empty string`)
	return value
end

local function rejectUnknownKeys(value: Record, allowed: { [string]: boolean }, label: string)
	for key in value do
		assert(allowed[key] == true, `{label}.{key} is not supported`)
	end
end

local function expectExactFields(value: any, allowed: { [string]: boolean }, count: number, label: string): Record
	local record = expectRecord(value, label)
	rejectUnknownKeys(record, allowed, label)
	local actualCount = 0
	for _ in record do
		actualCount += 1
	end
	assert(actualCount == count, `{label} must contain exactly {count} fields`)
	return record
end

local function expectVariant(value: any, allowed: { [string]: boolean }, label: string): (Record, string)
	local record = expectRecord(value, label)
	local selected: string? = nil
	for key in record do
		assert(allowed[key] == true, `{label}.{key} is not supported`)
		assert(selected == nil, `{label} must contain exactly one semantic variant`)
		selected = key
	end
	assert(selected ~= nil, `{label} must contain exactly one semantic variant`)
	return record, selected :: string
end

local function expectDenseArray(value: any, minimum: number, maximum: number, label: string): { any }
	assert(type(value) == "table", `{label} must be an array`)
	local array = value :: { any }
	local length = #array
	assert(length >= minimum and length <= maximum, `{label} count is invalid`)
	local count = 0
	for index in array do
		assert(type(index) == "number" and index % 1 == 0 and index >= 1 and index <= length, `{label} must be a dense array`)
		count += 1
	end
	assert(count == length, `{label} must be a dense array`)
	return array
end

local valueOriginFields = { local_value = true, local_place = true, environment = true }
local accessKeyFields = { literal = true, local_value = true, local_place = true, environment = true }
local tableKeyFields = { source_expression = true, literal = true, local_value = true, local_place = true, environment = true }
local receiverOriginFields = { access_path = true, local_value = true, local_place = true, environment = true }
local targetOriginFields = {
	intrinsic = true,
	local_value = true,
	local_place = true,
	environment = true,
	table_get = true,
	access_path = true,
	namecall = true,
	closure_value = true,
}

local function canonicalValueOrigin(origin: any): string
	local record, kind = expectVariant(origin, valueOriginFields, "target proof value origin")
	return kind .. proofComponent(expectString(record[kind], `target proof value origin.{kind}`))
end

local function canonicalAccessKey(key: any): string
	if type(key) == "string" then
		return "string" .. proofComponent(key)
	end
	local record, kind = expectVariant(key, accessKeyFields, "target proof access key")
	if kind == "literal" then
		local literal, literalKind = expectVariant(record.literal, { boolean = true, number = true }, "target proof literal key")
		if literalKind == "boolean" then
			assert(type(literal.boolean) == "boolean", "target proof literal key.boolean must be a Boolean")
			return if literal.boolean then "boolean1" else "boolean0"
		end
		local numberValue = literal.number
		assert(
			type(numberValue) == "number"
				and numberValue == numberValue
				and numberValue ~= math.huge
				and numberValue ~= -math.huge,
			"target proof numeric key must be finite"
		)
		local encoded = if numberValue == 0 then "0" else string.format("%.17g", numberValue)
		return "number" .. proofComponent(encoded)
	end
	return canonicalValueOrigin(record)
end

local function canonicalTableKey(key: any): string
	if type(key) ~= "table" or key.source_expression == nil then
		return canonicalAccessKey(key)
	end
	local record, kind = expectVariant(key, tableKeyFields, "target proof table key")
	assert(kind == "source_expression")
	return "source_expression" .. proofComponent(expectString(record.source_expression, "target proof table key.source_expression"))
end

local function canonicalAccessPath(path: any): string
	local record = expectExactFields(path, { root = true, keys = true }, 2, "target proof access path")
	local keys = expectDenseArray(record.keys, 1, TargetProofBundle.maxAccessPathKeys, "target proof access path.keys")
	local parts = { "access_path", proofComponent(canonicalValueOrigin(record.root)), proofComponent(tostring(#keys)) }
	for index = 1, #keys do
		table.insert(parts, proofComponent(canonicalAccessKey(keys[index])))
	end
	return table.concat(parts)
end

local function canonicalReceiverOrigin(origin: any): string
	local record, kind = expectVariant(origin, receiverOriginFields, "target proof receiver origin")
	if kind == "access_path" then
		return canonicalAccessPath(record.access_path)
	end
	return canonicalValueOrigin(record)
end

local function canonicalTargetOrigin(origin: any): string
	local record, kind = expectVariant(origin, targetOriginFields, "target proof origin")
	if kind == "intrinsic" then
		return "intrinsic" .. proofComponent(expectString(record.intrinsic, "target proof origin.intrinsic"))
	elseif kind == "closure_value" then
		return "closure_value" .. proofComponent(expectString(record.closure_value, "target proof origin.closure_value"))
	elseif kind == "table_get" then
		local access = expectExactFields(record.table_get, { table = true, key = true }, 2, "target proof table origin")
		return "table_get"
			.. proofComponent(canonicalValueOrigin(access.table))
			.. proofComponent(canonicalTableKey(access.key))
	elseif kind == "access_path" then
		return canonicalAccessPath(record.access_path)
	elseif kind == "namecall" then
		local namecall = expectExactFields(record.namecall, { receiver = true, method = true }, 2, "target proof namecall origin")
		return "namecall"
			.. proofComponent(canonicalReceiverOrigin(namecall.receiver))
			.. proofComponent(expectString(namecall.method, "target proof namecall origin.method"))
	end
	return canonicalValueOrigin(record)
end

function TargetProofBundle.targetOriginKey(origin: any): string
	return canonicalTargetOrigin(origin)
end

function TargetProofBundle.targetProofDigest(
	sourceSha256: string,
	callLocation: string,
	origin: any,
	content: string
): string
	local normalizedSource = string.lower(sourceSha256)
	assert(
		#normalizedSource == 64 and string.match(normalizedSource, "^[0-9a-f]+$") ~= nil,
		"target proof source digest must be SHA-256"
	)
	assert(callLocation ~= "", "target proof call location must not be empty")
	assert(content ~= "" and #content <= TargetProofBundle.maxProofContentBytes, "target proof content size is invalid")
	return TargetProofBundle.sha256(
		"lifter-target-recovery-proof-v1"
			.. proofComponent(normalizedSource)
			.. proofComponent(callLocation)
			.. proofComponent(canonicalTargetOrigin(origin))
			.. proofComponent(content)
	)
end

function TargetProofBundle.resultContractProofDigest(
	sourceSha256: string,
	producerCallLocation: string,
	resultOrdinal: number,
	origin: any,
	content: string
): string
	local normalizedSource = string.lower(sourceSha256)
	assert(
		#normalizedSource == 64 and string.match(normalizedSource, "^[0-9a-f]+$") ~= nil,
		"target result proof source digest must be SHA-256"
	)
	assert(producerCallLocation ~= "", "target result proof producer location must not be empty")
	assert(
		resultOrdinal >= 1
			and resultOrdinal <= TargetProofBundle.maxResultOrdinal
			and resultOrdinal % 1 == 0,
		"target result proof ordinal is invalid"
	)
	assert(content ~= "" and #content <= TargetProofBundle.maxProofContentBytes, "target result proof content size is invalid")
	return TargetProofBundle.sha256(
		"lifter-target-result-proof-v1"
			.. proofComponent(normalizedSource)
			.. proofComponent(producerCallLocation)
			.. proofComponent(tostring(resultOrdinal))
			.. proofComponent(canonicalTargetOrigin(origin))
			.. proofComponent(content)
	)
end

local BundleMethods = {}
BundleMethods.__index = BundleMethods

function BundleMethods:resolve(id: string, bindingDigest: string, label: string): Entry
	local bundle = self :: any
	local entry = bundle.by_id[id]
	assert(entry ~= nil, `{label} does not identify an entry in the detached proof bundle`)
	local normalizedBinding = string.lower(bindingDigest)
	assert(entry.binding_digests[normalizedBinding] == true, `{label} is not authorized by the detached proof bundle`)
	bundle.used_ids[id] = true
	bundle.used_binding_digests[normalizedBinding] = true
	return entry
end

function BundleMethods:assertFullyUsed(label: string)
	local bundle = self :: any
	for id in bundle.by_id do
		assert(bundle.used_ids[id] == true, `{label} contains unused proof entry {id}`)
	end
	for digest in bundle.binding_owners do
		assert(bundle.used_binding_digests[digest] == true, `{label} contains unused proof binding {digest}`)
	end
end

function TargetProofBundle.open(input: Input, signature: string, evidence: Evidence, label: string): Bundle
	assert(input.bytes ~= "" and #input.bytes <= TargetProofBundle.maxBundleBytes, `{label} byte size is invalid`)
	local normalizedSignature = string.lower(signature)
	local normalizedPublicKey = string.lower(input.trusted_public_key)
	assert(#normalizedSignature == 128 and string.match(normalizedSignature, "^[0-9a-f]+$") ~= nil, `{label}.signature must be an Ed25519 signature`)
	assert(#normalizedPublicKey == 64 and string.match(normalizedPublicKey, "^[0-9a-f]+$") ~= nil, `{label} trusted key must be an Ed25519 public key`)
	assert(evidence.kind == "frontend_proof", `{label}.evidence.kind must be frontend_proof`)
	assert(evidence.locator ~= "", `{label}.evidence.locator must not be empty`)
	local bundleDigest = TargetProofBundle.sha256(input.bytes)
	assert(
		type(evidence.digest) == "string" and string.lower(evidence.digest) == bundleDigest,
		`{label}.evidence must authenticate the exact detached bundle bytes`
	)
	assert(input.verify_signature(input.bytes, normalizedSignature, normalizedPublicKey) == true, `{label} signature is not trusted`)

	local decoded = expectRecord(input.decode(input.bytes), label)
	rejectUnknownKeys(decoded, { schema_version = true, entries = true }, label)
	assert(decoded.schema_version == "lifter_target_proof_bundle_v1", `{label}.schema_version is not supported`)
	local entries = expectDenseArray(decoded.entries, 1, TargetProofBundle.maxBundleEntries, label .. ".entries")

	local byId: { [string]: Entry } = {}
	local bindingOwners: { [string]: string } = {}
	local totalContentBytes = 0
	local totalBindingCount = 0
	for index = 1, #entries do
		local item = entries[index]
		local entryLabel = `{label}.entries[{index}]`
		local entry = expectRecord(item, entryLabel)
		rejectUnknownKeys(entry, { id = true, content = true, bindings = true }, entryLabel)
		local id = string.lower(expectString(entry.id, entryLabel .. ".id"))
		local content = expectString(entry.content, entryLabel .. ".content")
		assert(#content <= TargetProofBundle.maxProofContentBytes, `{entryLabel}.content exceeds the proof-content limit`)
		local existing = byId[id]
		if existing ~= nil then
			assert(existing.content == content, `{entryLabel}.id collides with different proof content`)
			error(`{entryLabel} duplicates proof content already stored in the bundle`, 0)
		end
		local expectedId = "sha256:" .. TargetProofBundle.sha256(content)
		assert(id == expectedId, `{entryLabel}.id does not content-address its proof bytes`)
		local bindings = expectDenseArray(entry.bindings, 1, TargetProofBundle.maxEntryBindings, entryLabel .. ".bindings")
		local bindingDigests: { [string]: boolean } = {}
		for bindingIndex = 1, #bindings do
			local rawDigest = bindings[bindingIndex]
			local bindingLabel = `{entryLabel}.bindings[{bindingIndex}]`
			local bindingDigest = string.lower(expectString(rawDigest, bindingLabel))
			assert(
				#bindingDigest == 64 and string.match(bindingDigest, "^[0-9a-f]+$") ~= nil,
				`{bindingLabel} must be SHA-256`
			)
			assert(bindingDigests[bindingDigest] ~= true, `{bindingLabel} duplicates a proof binding in its entry`)
			assert(bindingOwners[bindingDigest] == nil, `{bindingLabel} collides with a proof binding in another entry`)
			bindingDigests[bindingDigest] = true
			bindingOwners[bindingDigest] = id
			totalBindingCount += 1
			assert(totalBindingCount <= TargetProofBundle.maxBundleBindings, `{label} exceeds the proof-binding budget`)
		end
		totalContentBytes += #content
		assert(totalContentBytes <= TargetProofBundle.maxBundleContentBytes, `{label} exceeds the proof-content budget`)
		byId[id] = { id = id, content = content, binding_digests = bindingDigests }
	end

	return setmetatable({
		evidence = evidence,
		by_id = byId,
		used_ids = {},
		binding_owners = bindingOwners,
		used_binding_digests = {},
	}, BundleMethods) :: any
end

return table.freeze(TargetProofBundle)
