-- The returned function stores numbers of magnitude 2^53 and more in record fields (2^53, 2^53 + 2, 2^63, 2^64, 1e20
-- and -2^64), passes three of them to sink, collects three in a list and returns seven of them with the record and
-- the list. Each is an integer that a double holds exactly, written with its exact digits, except 2^63 written as
-- 9.223372036854775808e18 in record.half64 and the seventh return value; record.half64expr computes 0.5 * 2 ^ 64.
return function(sink)
	local record = {}
	record.p53 = 9007199254740992
	record.p53plus2 = 9007199254740994
	record.p63 = 9223372036854775808
	record.p64 = 18446744073709551616
	record.e20 = 100000000000000000000
	record.neg64 = -18446744073709551616
	record.half64 = 9.223372036854775808e18
	record.half64expr = 0.5 * 2 ^ 64
	sink(9223372036854775808, 18446744073709551616, -18446744073709551616)
	local list = { 9007199254740994, 18446744073709551616, 100000000000000000000 }
	return 9007199254740992, 9007199254740994, 9223372036854775808, 18446744073709551616, 100000000000000000000, -18446744073709551616, 9.223372036854775808e18, record, list
end
