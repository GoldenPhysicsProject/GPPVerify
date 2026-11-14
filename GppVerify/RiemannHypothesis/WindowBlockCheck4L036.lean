import GppVerify.RiemannHypothesis.WindowBlockCheck3L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 4 of 8

Rows 16–19 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_16 : muRowOK 16 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_16 : wRowOK 16 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_16 : resRowOK 16 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_17 : muRowOK 17 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_17 : wRowOK 17 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_17 : resRowOK 17 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_18 : muRowOK 18 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_18 : wRowOK 18 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_18 : resRowOK 18 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_19 : muRowOK 19 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_19 : wRowOK 19 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_19 : resRowOK 19 = true := by decide +kernel

end GppWindowBlockDataL036
