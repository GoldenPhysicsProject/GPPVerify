import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The intermediate-value step of the source-site spectral flow

Source: Codex/Discovery2, GPP-bridge PR #11 comment 6390537686 ("source-site spectral flow: the
intermediate value theorem gives `θ* ∈ (0, 1/4)` with `det Q(θ*) = 0`"). Daniel Toupin / Golden
Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

For a family `Q : ℝ → Matrix (Fin n) (Fin n) ℝ` whose entries are continuous on `[a, b]`:

* `det_zero_of_sign_change`: if `det Q(a)` and `det Q(b)` have opposite strict signs, there is
  `θ ∈ (a, b)` with `det Q(θ) = 0`.
* `exists_det_zero_Ioo_quarter`: the special case `[0, 1/4]`, with the endpoint signs stated as
  hypotheses (`det Q(0) < 0 < det Q(1/4)` or the reverse).

**Scope.** Only this intermediate-value step. The certified endpoint signs themselves (Codex's Arb
computation of `det Q` at `θ = 0` and `θ = 1/4`), the definition of the source-site matrix `Q(θ)`,
the continuity of its entries, and the uniqueness of the zero are NOT formalized; they enter as
hypotheses. No claim about RH.
-/

set_option autoImplicit false

open Set

namespace GppSpectralFlowIVT

/-- If the determinant changes sign across `[a, b]`, it vanishes somewhere in `(a, b)`. -/
theorem det_zero_of_sign_change {n : ℕ} {a b : ℝ} (hab : a < b)
    (Q : ℝ → Matrix (Fin n) (Fin n) ℝ) (hQ : ContinuousOn Q (Icc a b))
    (hs : (Q a).det < 0 ∧ 0 < (Q b).det ∨ 0 < (Q a).det ∧ (Q b).det < 0) :
    ∃ θ ∈ Ioo a b, (Q θ).det = 0 := by
  have hd : ContinuousOn (fun θ => (Q θ).det) (Icc a b) :=
    (continuous_id.matrix_det).comp_continuousOn hQ
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact intermediate_value_Ioo hab.le hd ⟨h1, h2⟩
  · exact intermediate_value_Ioo' hab.le hd ⟨h2, h1⟩

/-- The `[0, 1/4]` instance used for the source-site spectral flow. -/
theorem exists_det_zero_Ioo_quarter {n : ℕ} (Q : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ContinuousOn Q (Icc 0 (1 / 4)))
    (hs : (Q 0).det < 0 ∧ 0 < (Q (1 / 4)).det ∨ 0 < (Q 0).det ∧ (Q (1 / 4)).det < 0) :
    ∃ θ ∈ Ioo (0 : ℝ) (1 / 4), (Q θ).det = 0 :=
  det_zero_of_sign_change (by norm_num) Q hQ hs

end GppSpectralFlowIVT
