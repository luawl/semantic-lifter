-- The returned function returns a list of ten number literals: 2^1023 and 2^1022 in decimal notation, 0.000001, 1e-9,
-- 1e-12, 1.602176634e-19, the largest finite double, 0.1, the subnormal 1e-320 and 1e23.
return function()
	return {
		8.98846567431158e307,
		4.4942328371557898e307,
		0.000001,
		1e-9,
		1e-12,
		1.602176634e-19,
		1.7976931348623157e308,
		0.1,
		1e-320,
		1e23,
	}
end
