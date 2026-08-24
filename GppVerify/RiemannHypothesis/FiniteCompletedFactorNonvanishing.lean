import GppVerify.RiemannHypothesis.ArchimedeanEulerNonvanishing
import Mathlib.Tactic

/-!
# Nonvanishing of every finite completed local zeta product

`ArchimedeanEulerNonvanishing.lean` proves nonvanishing for the Euler holonomies
`1-p^{-s}`.  The actual local Euler zeta factors are their inverses.  This file states the
corresponding theorem in the zeta-factor normalization:

  Z_{S,∞}(s) = π^{-s/2} Γ(s/2) ∏_{p∈S} (1-p^{-s})^{-1}.

For every finite set of bases `p>1` and every `Re s>0`, this finite completed local product
is nonzero. Therefore no nontrivial zeta zero can be a zero of any finite Euler × Gamma
truncation. The zero mechanism necessarily belongs to the global infinite/analytically
continued object.

No RH claim is made here.
-/

namespace GppFiniteCompletedFactor

open Complex
open scoped BigOperators

/-- Finite product of genuine local Euler zeta factors. -/
noncomputable def finiteEulerZetaProduct {ι : Type} [Fintype ι]
    (p : ι → ℝ) (s : ℂ) : ℂ :=
  ∏ i, GppCutkoskyWeil.zetaP (p i) s

/-- Finite completed local zeta product, including the real-place Gamma factor. -/
noncomputable def finiteCompletedZetaProduct {ι : Type} [Fintype ι]
    (p : ι → ℝ) (s : ℂ) : ℂ :=
  GppArchEuler.archFactor s * finiteEulerZetaProduct p s

/-- Each genuine local Euler factor is nonzero in `Re s>0` for `p>1`. -/
theorem zetaP_ne_zero_of_re_pos {p : ℝ} (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    GppCutkoskyWeil.zetaP p s ≠ 0 := by
  rw [GppPrimeFermion.zetaP_eq_eulerHolonomy_inv]
  exact inv_ne_zero (GppArchEuler.eulerHolonomy_ne_zero_of_re_pos hp hs)

/-- A finite Euler product of genuine local zeta factors is nonzero in `Re s>0`. -/
theorem finiteEulerZetaProduct_ne_zero_of_re_pos {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) {s : ℂ} (hs : 0 < s.re) :
    finiteEulerZetaProduct p s ≠ 0 := by
  unfold finiteEulerZetaProduct
  exact Finset.prod_ne_zero_iff.mpr fun i hi => zetaP_ne_zero_of_re_pos (hp i) hs

/-- **Finite completed-zeta obstruction.** No finite Euler × Archimedean truncation has a
zero anywhere in the open right half-plane. -/
theorem finiteCompletedZetaProduct_ne_zero_of_re_pos {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) {s : ℂ} (hs : 0 < s.re) :
    finiteCompletedZetaProduct p s ≠ 0 := by
  unfold finiteCompletedZetaProduct
  exact mul_ne_zero (GppArchEuler.archFactor_ne_zero_of_re_pos hs)
    (finiteEulerZetaProduct_ne_zero_of_re_pos p hp hs)

/-- In particular, the obstruction applies on every critical-line point `1/2+it`. -/
theorem finiteCompletedZetaProduct_critical_ne_zero {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (t : ℝ) :
    finiteCompletedZetaProduct p (1 / 2 + t * Complex.I) ≠ 0 := by
  apply finiteCompletedZetaProduct_ne_zero_of_re_pos p hp
  norm_num

end GppFiniteCompletedFactor

#print axioms GppFiniteCompletedFactor.zetaP_ne_zero_of_re_pos
#print axioms GppFiniteCompletedFactor.finiteEulerZetaProduct_ne_zero_of_re_pos
#print axioms GppFiniteCompletedFactor.finiteCompletedZetaProduct_ne_zero_of_re_pos
#print axioms GppFiniteCompletedFactor.finiteCompletedZetaProduct_critical_ne_zero
