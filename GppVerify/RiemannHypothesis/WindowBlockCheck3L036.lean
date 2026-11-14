import GppVerify.RiemannHypothesis.WindowBlockCheck2L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 3 of 8

Rows 12–15 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_12 : muRowOK 12 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_12 : wRowOK 12 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_12 : resRowOK 12 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_13 : muRowOK 13 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_13 : wRowOK 13 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_13 : resRowOK 13 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_14 : muRowOK 14 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_14 : wRowOK 14 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_14 : resRowOK 14 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_15 : muRowOK 15 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_15 : wRowOK 15 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_15 : resRowOK 15 = true := by decide +kernel

end GppWindowBlockDataL036
