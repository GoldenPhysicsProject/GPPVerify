import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerFubini
import GppVerify.RiemannHypothesis.PoissonGeometricFiber
import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import Mathlib.Tactic

/-!
# Prime-power modes as radial Poisson modes

This file closes the termwise algebra between the canonical von-Mangoldt
prime-power coordinates and the one-sided Poisson geometric fiber, and then
combines that local identity with the already-proved absolute-convergence
Fubini theorem to obtain the full prime-Poisson response on `a>1`.
-/

namespace GppVonMangoldtPrimePowerPoissonFiber

open Real
open GppVonMangoldtPrimePowerReindex
open GppVonMangoldtPrimePowerFubini
open GppPoissonGeometricFiber
open GppPrimePoissonRadial

/-- The exponential damping on the `m`th prime-power mode is exactly the
`m`th ordinary power of the radial coordinate `p^{-a}`. -/
theorem exp_primePower_damping_eq_rpow_nat
    (p : Nat.Primes) (a : ℝ) (m : ℕ) :
    Real.exp (-(m : ℝ) * Real.log (p : ℕ) * a) =
      ((((p : ℕ) : ℝ) ^ (-a)) : ℝ) ^ m := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.prop.pos
  rw [rpow_neg_eq_exp hp0]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A single canonical prime-power von-Mangoldt cosine summand is exactly the
corresponding radial Poisson Fourier mode. -/
theorem cosineSummand_primePower_eq_radial_mode
    (p : Nat.Primes) (k : ℕ) (a t : ℝ) :
    cosineSummand a t ((p : ℕ) ^ (k + 1)) =
      Real.log (p : ℕ) *
        ((((p : ℕ) : ℝ) ^ (-a)) : ℝ) ^ (k + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * (t * Real.log (p : ℕ))) := by
  rw [cosineSummand_primePower p k a t]
  rw [exp_primePower_damping_eq_rpow_nat p a (k + 1)]
  congr 2
  congr 1
  push_cast
  ring

/-- One complete prime-power tower is exactly the local vacuum-subtracted
Poisson response. -/
theorem two_mul_primePower_inner_tsum_eq_WpA
    (p : Nat.Primes) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    2 * (∑' k : ℕ, cosineSummand a t ((p : ℕ) ^ (k + 1))) =
      WpA ((p : ℕ) : ℝ) a t := by
  let r : ℝ := (((p : ℕ) : ℝ) ^ (-a))
  let θ : ℝ := t * Real.log (p : ℕ)
  have hp1 : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.prop.one_lt
  have hp0 : (0 : ℝ) < (p : ℕ) := lt_trans zero_lt_one hp1
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg hp0.le _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr ha)
  have hrewrite :
      (∑' k : ℕ, cosineSummand a t ((p : ℕ) ^ (k + 1))) =
        Real.log (p : ℕ) *
          ∑' k : ℕ, r ^ (k + 1) *
            Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simpa [r, θ] using
      cosineSummand_primePower_eq_radial_mode p k a t
  rw [hrewrite]
  calc
    2 * (Real.log (p : ℕ) *
        ∑' k : ℕ, r ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
        Real.log (p : ℕ) *
          (2 * ∑' k : ℕ, r ^ (k + 1) *
            Real.cos (((k + 1 : ℕ) : ℝ) * θ)) := by ring
    _ = Real.log (p : ℕ) * (GppCutkoskyWeil.KrClosed r θ - 1) := by
      rw [two_mul_tsum_rpow_cos_eq_KrClosed_sub_one hr0 hr1 θ]
    _ = WpA ((p : ℕ) : ℝ) a t := by
      simp [WpA, r, θ]

/-- Absolute convergence of the outer prime-Poisson response on `a>1`. -/
theorem summable_WpA {a : ℝ} (ha : 1 < a) (t : ℝ) :
    Summable (fun p : Nat.Primes => WpA ((p : ℕ) : ℝ) a t) := by
  have houter : Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, cosineSummand a t ((p : ℕ) ^ (k + 1))) :=
    (summable_primePower_pair ha t).prod
  have hscaled : Summable (fun p : Nat.Primes =>
      2 * (∑' k : ℕ, cosineSummand a t ((p : ℕ) ^ (k + 1)))) :=
    houter.mul_left 2
  exact hscaled.congr (fun p =>
    two_mul_primePower_inner_tsum_eq_WpA p (lt_trans zero_lt_one ha) t)

/-- **Global prime-Poisson closure on the honest convergence half-plane.**
The real logarithmic derivative is exactly the countable sum of local radial
Poisson responses. No analytic continuation into the critical strip is used. -/
theorem two_mul_neg_zeta_logDeriv_re_eq_tsum_WpA
    {a t : ℝ} (ha : 1 < a) :
    2 * (-(Complex.deriv Complex.riemannZeta
      ((a : ℂ) + (t : ℂ) * Complex.I) /
      Complex.riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re =
      ∑' p : Nat.Primes, WpA ((p : ℕ) : ℝ) a t := by
  rw [neg_zeta_logDeriv_re_eq_iterated_primePower_tsum ha]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  exact two_mul_primePower_inner_tsum_eq_WpA p (lt_trans zero_lt_one ha) t

end GppVonMangoldtPrimePowerPoissonFiber

#print axioms GppVonMangoldtPrimePowerPoissonFiber.exp_primePower_damping_eq_rpow_nat
#print axioms GppVonMangoldtPrimePowerPoissonFiber.cosineSummand_primePower_eq_radial_mode
#print axioms GppVonMangoldtPrimePowerPoissonFiber.two_mul_primePower_inner_tsum_eq_WpA
#print axioms GppVonMangoldtPrimePowerPoissonFiber.summable_WpA
#print axioms GppVonMangoldtPrimePowerPoissonFiber.two_mul_neg_zeta_logDeriv_re_eq_tsum_WpA
