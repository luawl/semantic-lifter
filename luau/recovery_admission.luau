--!strict

local RecoveryAdmission = {}

RecoveryAdmission.maxManifestBytes = 1024 * 1024
RecoveryAdmission.maxCollectionItems = 4096
RecoveryAdmission.maxIntrinsicBindings = 64

function RecoveryAdmission.expectManifestBytes(value: any, label: string): string
	assert(type(value) == "string", `{label} must be a byte string`)
	assert(#value <= RecoveryAdmission.maxManifestBytes, `{label} exceeds the manifest byte limit`)
	return value
end

function RecoveryAdmission.expectDenseArray(value: any, label: string, limit: number): { any }
	assert(type(value) == "table", `{label} must be an array`)
	assert(limit >= 0 and limit % 1 == 0, "recovery admission array limit must be a non-negative integer")
	local array = value :: { any }
	local length = #array
	assert(length <= limit, `{label} exceeds the admission item limit of {limit}`)
	local count = 0
	for index in array do
		count += 1
		assert(count <= limit, `{label} exceeds the admission item limit of {limit}`)
		assert(type(index) == "number" and index % 1 == 0 and index >= 1 and index <= length, `{label} must be a dense array`)
	end
	assert(count == length, `{label} must be a dense array`)
	return array
end

return table.freeze(RecoveryAdmission)
