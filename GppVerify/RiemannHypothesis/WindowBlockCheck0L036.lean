import GppVerify.RiemannHypothesis.WindowBlockDataL036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 0 of 8

Rows 0–3 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
Also the factorial table and the sign of the diagonal factor.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_0 : muRowOK 0 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_0 : wRowOK 0 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_0 : resRowOK 0 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_1 : muRowOK 1 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_1 : wRowOK 1 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_1 : resRowOK 1 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_2 : muRowOK 2 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_2 : wRowOK 2 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_2 : resRowOK 2 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_3 : muRowOK 3 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_3 : wRowOK 3 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_3 : resRowOK 3 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem invFactOK_eq : invFactOK = true := by decide +kernel
theorem DOK_eq : DOK = true := by decide +kernel

end GppWindowBlockDataL036
