import GppVerify.RiemannHypothesis.ZetaGibbsFisher
import Mathlib.Tactic

/-!
# Information geometry of the zeta Gibbs family

The analytic identification of the zeta Gibbs family supplies the potential
`A(β)=log ζ(β)` and mean energy `U(β)=-A'(β)`. This file records the exact
Bregman/Jeffreys algebra independently of any continuation away from `β>1`.
-/

namespace GppZetaGibbsInformationGeometry

/-- Bregman-form relative entropy associated to a potential `A` and response `U`. -/
def bregmanKL (A U : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  A γ - A β + (γ - β) * U β

/-- Symmetrized Bregman divergence. -/
def jeffreys (A U : ℝ → ℝ) (β γ : ℝ) : ℝ :=
  bregmanKL A U β γ + bregmanKL A U γ β

/-- Exact cancellation of the potential terms in the Jeffreys divergence. -/
theorem jeffreys_eq_parameter_gap_mul_response_gap
    (A U : ℝ → ℝ) (β γ : ℝ) :
    jeffreys A U β γ = (γ - β) * (U β - U γ) := by
  unfold jeffreys bregmanKL
  ring

/-- Symmetry of the Jeffreys divergence. -/
theorem jeffreys_comm (A U : ℝ → ℝ) (β γ : ℝ) :
    jeffreys A U β γ = jeffreys A U γ β := by
  unfold jeffreys
  ring

/-- If the response decreases between two ordered parameters, the Jeffreys
quantity is nonnegative. This is the order-theoretic form used by the Gibbs
family because `U'=-g≤0` on the honest thermodynamic domain. -/
theorem jeffreys_nonneg_of_le_of_antitone_pair
    (A U : ℝ → ℝ) {β γ : ℝ} (hβγ : β ≤ γ) (hU : U γ ≤ U β) :
    0 ≤ jeffreys A U β γ := by
  rw [jeffreys_eq_parameter_gap_mul_response_gap]
  exact mul_nonneg (sub_nonneg.mpr hβγ) (sub_nonneg.mpr hU)

end GppZetaGibbsInformationGeometry

#print axioms GppZetaGibbsInformationGeometry.jeffreys_eq_parameter_gap_mul_response_gap
#print axioms GppZetaGibbsInformationGeometry.jeffreys_comm
#print axioms GppZetaGibbsInformationGeometry.jeffreys_nonneg_of_le_of_antitone_pair
