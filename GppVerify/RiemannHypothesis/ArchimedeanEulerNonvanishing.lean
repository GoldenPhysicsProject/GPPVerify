import GppVerify.RiemannHypothesis.FinitePrimeDiracCompletion
import GppVerify.RiemannHypothesis.ArchimedeanZetaIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Finite Euler × Archimedean nonvanishing in the right half-plane

The completed zeta factorization is multiplicative at the local-factor level.  This file
formalizes a basic but important obstruction: in the half-plane `Re s > 0`, every finite
Euler holonomy `1 - p^{-s}` with `p>1` is nonzero, and the Archimedean Gamma factor
`π^{-s/2} Γ(s/2)` is also nonzero. Therefore multiplying finitely many local Euler
holonomies by the Archimedean factor cannot create a zero.

Any zero mechanism for the completed zeta function must therefore use genuinely global
information: the infinite Euler product / analytic continuation / renormalized global
operator, not a finite local product and not an independent positive Archimedean channel.

No RH claim is made here.
-/

namespace GppArchEuler

open Complex
open scoped BigOperators

/-- Complex Archimedean factor in exponential form, avoiding branch-notation ambiguity:
`π^{-s/2} Γ(s/2) = exp(-(s/2) log π) Γ(s/2)` for the positive real base `π`. -/
noncomputable def archFactor (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) * Complex.Gamma (s / 2)

/-- The Gamma part of the Archimedean factor is nonzero throughout `Re s > 0`. -/
theorem gamma_half_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma (s / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  simp
  linarith

/-- The entire Archimedean local factor is nonzero throughout `Re s > 0`. -/
theorem archFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : archFactor s ≠ 0 := by
  unfold archFactor
  exact mul_ne_zero (Complex.exp_ne_zero _) (gamma_half_ne_zero_of_re_pos hs)

/-- A local Euler holonomy cannot vanish in `Re s > 0` for `p>1`.
The proof is the same strict-norm argument as on the critical line: `|p^{-s}|=p^{-Re s}<1`. -/
theorem eulerHolonomy_ne_zero_of_re_pos {p : ℝ} (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    GppPrimeFermion.eulerHolonomy p s ≠ 0 := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hlogpC : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp0.le).symm
  intro hzero
  have hexp : Complex.exp (-s * Complex.log p) = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  have hnorm : ‖Complex.exp (-s * Complex.log p)‖ = 1 := by
    rw [hexp]
    norm_num
  rw [Complex.norm_exp] at hnorm
  have hre : (-s * Complex.log p).re = -s.re * Real.log p := by
    rw [hlogpC]
    simp [Complex.mul_re]
  rw [hre] at hnorm
  have hneg : -s.re * Real.log p < 0 := by
    have hlog : 0 < Real.log p := Real.log_pos hp
    nlinarith
  have hlt : Real.exp (-s.re * Real.log p) < 1 := Real.exp_lt_one_iff.mpr hneg
  linarith

/-- Every finite product of Euler holonomies is nonzero in `Re s > 0` when all bases exceed 1. -/
theorem finiteEulerProduct_ne_zero_of_re_pos {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) {s : ℂ} (hs : 0 < s.re) :
    (∏ i, GppPrimeFermion.eulerHolonomy (p i) s) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i hi => eulerHolonomy_ne_zero_of_re_pos (hp i) hs

/-- **Finite local completion obstruction.** The Archimedean factor times any finite Euler
holonomy product is nonzero throughout `Re s > 0`. In particular, finite local completion
cannot generate a critical-strip zero. -/
theorem finiteCompletedLocalProduct_ne_zero {ι : Type} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) {s : ℂ} (hs : 0 < s.re) :
    archFactor s * (∏ i, GppPrimeFermion.eulerHolonomy (p i) s) ≠ 0 := by
  exact mul_ne_zero (archFactor_ne_zero_of_re_pos hs)
    (finiteEulerProduct_ne_zero_of_re_pos p hp hs)

end GppArchEuler

#print axioms GppArchEuler.gamma_half_ne_zero_of_re_pos
#print axioms GppArchEuler.archFactor_ne_zero_of_re_pos
#print axioms GppArchEuler.eulerHolonomy_ne_zero_of_re_pos
#print axioms GppArchEuler.finiteEulerProduct_ne_zero_of_re_pos
#print axioms GppArchEuler.finiteCompletedLocalProduct_ne_zero
