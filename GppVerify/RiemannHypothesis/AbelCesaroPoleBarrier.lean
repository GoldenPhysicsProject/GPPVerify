import GppVerify.RiemannHypothesis.YakaboyluMatrixElement
import GppVerify.RiemannHypothesis.YakaboyluPositivityKernel
import Mathlib.Tactic

/-!
# Abel--Cesàro pole barrier

The regularized Yakaboylu/Abel matrix element has two logically distinct statements:

1. an **integral identity** valid only in the convergence strip
   `1 - ε < σ < 1 + ε`;
2. a **rational-function limit** `ε²/(ε²-(σ-1)²) -> 0` as `ε -> 0`
   whenever `σ != 1`.

For an off-self-dual exponent `σ != 1`, these statements cannot be joined by taking the
positive integral to `ε = 0`: the convergence strip itself stays a positive distance away
from zero.  This file formalizes that domain barrier.  It does not assert RH and does not
use any zeta-zero data.

This is the precise elementary gap in the old Abel--Cesàro positivity passage: positivity
of the genuine integral cannot be transported through the pole by the separate
meromorphic/rational continuation theorem.
-/

namespace GppAbelCesaroPoleBarrier

open Filter

/-- The Yakaboylu convergence strip is exactly the inequality `|σ - 1| < ε`. -/
theorem convergence_strip_iff_abs_lt {σ ε : ℝ} :
    (1 - ε < σ ∧ σ < 1 + ε) ↔ |σ - 1| < ε := by
  constructor
  · intro h
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  · intro h
    rw [abs_lt] at h
    constructor <;> linarith [h.1, h.2]

/-- Off the self-dual point `σ = 1`, there is a whole punctured interval next to
`ε = 0` containing no regulator for which the Abel/Yakaboylu integral converges. -/
theorem off_self_dual_has_regulator_gap {σ : ℝ} (hσ : σ ≠ 1) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ε : ℝ, 0 < ε → ε < η → ¬ (1 - ε < σ ∧ σ < 1 + ε) := by
  have hgap : 0 < |σ - 1| := abs_pos.mpr (sub_ne_zero.mpr hσ)
  refine ⟨|σ - 1|, hgap, ?_⟩
  intro ε hε hsmall hstrip
  have habs : |σ - 1| < ε := convergence_strip_iff_abs_lt.mp hstrip
  linarith

/-- Specialization to a reflection pair centered at the critical half-density.  The
self-pairing real exponent is `σ = 1 + 2δ`, so any nonzero displacement `δ` produces a
strict regulator gap before `ε = 0`. -/
theorem offcenter_reflection_pair_has_regulator_gap {δ : ℝ} (hδ : δ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ε : ℝ, 0 < ε → ε < η →
        ¬ (1 - ε < 1 + 2 * δ ∧ 1 + 2 * δ < 1 + ε) := by
  have hσ : (1 + 2 * δ : ℝ) ≠ 1 := by
    intro h
    have : δ = 0 := by linarith
    exact hδ this
  exact off_self_dual_has_regulator_gap hσ

/-- The algebraic/meromorphic matrix-element formula nevertheless tends to zero at the
origin for every nonzero displacement.  Together with
`offcenter_reflection_pair_has_regulator_gap`, this records formally that the zero limit
is **not** a limit taken through the positive integral's convergence domain. -/
theorem offcenter_meromorphic_formula_tends_zero {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto
      (fun ε : ℝ => ε ^ 2 / (ε ^ 2 - (2 * δ) ^ 2))
      (nhds 0) (nhds 0) := by
  have hσ : (1 + 2 * δ : ℝ) ≠ 1 := by
    intro h
    have : δ = 0 := by linarith
    exact hδ this
  have h := GppYakaboylu.tendsto_matrix_element_zero (σ := 1 + 2 * δ) hσ
  simpa [show (1 + 2 * δ - 1 : ℝ) = 2 * δ by ring] using h

/-- Compact package: off-center, the genuine positive integral domain is separated from
`ε = 0`, even though the rational continuation has a zero limit there. -/
theorem offcenter_pole_barrier_package {δ : ℝ} (hδ : δ ≠ 0) :
    (∃ η : ℝ, 0 < η ∧
      ∀ ε : ℝ, 0 < ε → ε < η →
        ¬ (1 - ε < 1 + 2 * δ ∧ 1 + 2 * δ < 1 + ε)) ∧
    Tendsto
      (fun ε : ℝ => ε ^ 2 / (ε ^ 2 - (2 * δ) ^ 2))
      (nhds 0) (nhds 0) := by
  exact ⟨offcenter_reflection_pair_has_regulator_gap hδ,
    offcenter_meromorphic_formula_tends_zero hδ⟩

end GppAbelCesaroPoleBarrier

#check @GppAbelCesaroPoleBarrier.convergence_strip_iff_abs_lt
#check @GppAbelCesaroPoleBarrier.off_self_dual_has_regulator_gap
#check @GppAbelCesaroPoleBarrier.offcenter_reflection_pair_has_regulator_gap
#check @GppAbelCesaroPoleBarrier.offcenter_meromorphic_formula_tends_zero
#check @GppAbelCesaroPoleBarrier.offcenter_pole_barrier_package
