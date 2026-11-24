import GppVerify.RiemannHypothesis.WindowBlockCheck0L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 1 of 8

Rows 4–7 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_4 : muRowOK 4 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_4 : wRowOK 4 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_4 : resRowOK 4 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_5 : muRowOK 5 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_5 : wRowOK 5 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_5 : resRowOK 5 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_6 : muRowOK 6 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_6 : wRowOK 6 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_6 : resRowOK 6 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_7 : muRowOK 7 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_7 : wRowOK 7 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_7 : resRowOK 7 = true := by decide +kernel

end GppWindowBlockDataL036
