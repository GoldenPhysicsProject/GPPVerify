import GppVerify.RiemannHypothesis.WindowBlockCheck6L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 7 of 8

Rows 28–31 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_28 : muRowOK 28 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_28 : wRowOK 28 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_28 : resRowOK 28 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_29 : muRowOK 29 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_29 : wRowOK 29 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_29 : resRowOK 29 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_30 : muRowOK 30 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_30 : wRowOK 30 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_30 : resRowOK 30 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_31 : muRowOK 31 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_31 : wRowOK 31 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_31 : resRowOK 31 = true := by decide +kernel

end GppWindowBlockDataL036
