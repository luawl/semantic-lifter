local function worker(items, ...)
	local x = 0
	local q = items[1]
	local function get() return x end
	for a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9 in items do
		for a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9 in items do
			for a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9 in items do
				for a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8, a4_9 in items do
					for a5_1, a5_2, a5_3, a5_4, a5_5, a5_6, a5_7, a5_8, a5_9 in items do
						for a6_1, a6_2, a6_3, a6_4, a6_5, a6_6, a6_7, a6_8, a6_9 in items do
							for a7_1, a7_2, a7_3, a7_4, a7_5, a7_6, a7_7, a7_8, a7_9 in items do
								for a8_1, a8_2, a8_3, a8_4, a8_5, a8_6, a8_7, a8_8, a8_9 in items do
									for a9_1, a9_2, a9_3, a9_4, a9_5, a9_6, a9_7, a9_8, a9_9 in items do
										for a10_1, a10_2, a10_3, a10_4, a10_5, a10_6, a10_7, a10_8, a10_9 in items do
											for a11_1, a11_2, a11_3, a11_4, a11_5, a11_6, a11_7, a11_8, a11_9 in items do
												for a12_1, a12_2, a12_3, a12_4, a12_5, a12_6, a12_7, a12_8, a12_9 in items do
													for a13_1, a13_2, a13_3, a13_4, a13_5, a13_6, a13_7, a13_8, a13_9 in items do
														for a14_1, a14_2, a14_3, a14_4, a14_5, a14_6, a14_7, a14_8, a14_9 in items do
															for a15_1, a15_2, a15_3, a15_4, a15_5, a15_6, a15_7, a15_8, a15_9 in items do
																for a16_1, a16_2, a16_3, a16_4, a16_5, a16_6, a16_7, a16_8, a16_9 in items do
																	for a17_1, a17_2, a17_3, a17_4, a17_5, a17_6, a17_7, a17_8, a17_9 in items do
																		for a18_1, a18_2, a18_3, a18_4, a18_5, a18_6, a18_7, a18_8, a18_9 in items do
																			for a19_1, a19_2, a19_3, a19_4, a19_5, a19_6, a19_7, a19_8, a19_9 in items do
																				for a20_1, a20_2, a20_3, a20_4, a20_5, a20_6, a20_7, a20_8, a20_9 in items do
																					for a21_1, a21_2, a21_3, a21_4, a21_5, a21_6, a21_7 in items do
																						if a21_1 then
																						if a21_2 then
																						x = a21_3
																						continue
																						end
																						end
																						if a21_3 then x = a21_1 end
																						if a21_1 then x = a21_2 end
																						if a21_2 then x = a21_3 end
																						if a21_3 then x = a21_2 end
																						if a21_1 then x = a21_3 end
																						if a21_4 then
																						if a21_5 then
																						x = a21_1
																						continue
																						end
																						end
																						x = a21_1
																					end
																				end
																			end
																		end
																	end
																end
															end
														end
													end
												end
											end
										end
									end
								end
							end
						end
					end
				end
			end
		end
	end
	return get, q
end
return worker
