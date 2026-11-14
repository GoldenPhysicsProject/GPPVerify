import GppVerify.RiemannHypothesis.WindowBlockCheck5L036

/-!
# Kernel checks for the `ℓ = 9/25` finite block, part 6 of 8

Rows 24–27 of the `μ` and `w` tables and of the `L D Lᵀ` residual, each checked by
`decide +kernel` in its own declaration (see `WindowBlockDataL036`). The eight parts import each other
in sequence so that the build runs them one at a time: each holds a few GB of kernel intermediates.
-/

namespace GppWindowBlockDataL036

set_option maxRecDepth 400000 in
theorem muRowOK_24 : muRowOK 24 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_24 : wRowOK 24 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_24 : resRowOK 24 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_25 : muRowOK 25 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_25 : wRowOK 25 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_25 : resRowOK 25 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_26 : muRowOK 26 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_26 : wRowOK 26 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_26 : resRowOK 26 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem muRowOK_27 : muRowOK 27 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem wRowOK_27 : wRowOK 27 = true := by decide +kernel
set_option maxRecDepth 400000 in
theorem resRowOK_27 : resRowOK 27 = true := by decide +kernel

end GppWindowBlockDataL036
