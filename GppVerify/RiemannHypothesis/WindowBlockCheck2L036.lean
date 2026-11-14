import GppVerify.RiemannHypothesis.WindowBlockCheck1L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 2 of 8

Rows 8–11 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_8 : muRowOK 8 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_8 : wRowOK 8 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_8 : resRowOK 8 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_9 : muRowOK 9 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_9 : wRowOK 9 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_9 : resRowOK 9 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_10 : muRowOK 10 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_10 : wRowOK 10 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_10 : resRowOK 10 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_11 : muRowOK 11 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_11 : wRowOK 11 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_11 : resRowOK 11 = true := by decide +kernel

end GppWindowBlockDataL036
