import GppVerify.RiemannHypothesis.WindowBlockCheck4L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 5 of 8

Rows 20–23 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_20 : muRowOK 20 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_20 : wRowOK 20 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_20 : resRowOK 20 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_21 : muRowOK 21 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_21 : wRowOK 21 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_21 : resRowOK 21 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_22 : muRowOK 22 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_22 : wRowOK 22 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_22 : resRowOK 22 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_23 : muRowOK 23 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_23 : wRowOK 23 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_23 : resRowOK 23 = true := by decide +kernel

end GppWindowBlockDataL036
