import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# One-sided geometric fibers of the Poisson kernel

For a complex `z` with `‖z‖<1`, the shifted geometric series has sum `z/(1-z)`.
Taking real parts and specializing to `z = r exp(iθ)` identifies the positive-frequency
fiber with one half of the vacuum-subtracted Poisson kernel.
-/

namespace GppPoissonGeometricFiber

open Complex Real
open GppCutkoskyWeil

/-- Shifted geometric series. -/
theorem tsum_pow_succ {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' k : ℕ, z ^ (k + 1)) = z / (1 - z) := by
  have hs : Summable (fun k : ℕ => z ^ k) :=
    (hasSum_geometric_of_norm_lt_one hz).summable
  calc
    (∑' k : ℕ, z ^ (k + 1)) = ∑' k : ℕ, z * z ^ k := by
      apply tsum_congr
      intro k
      rw [pow_succ']
    _ = z * ∑' k : ℕ, z ^ k := hs.tsum_mul_left z
    _ = z * (1 - z)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hz]
    _ = z / (1 - z) := by rw [div_eq_mul_inv]

/-- Real parts of the shifted geometric series sum to the real part of `z/(1-z)`. -/
theorem tsum_re_pow_succ {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' k : ℕ, (z ^ (k + 1)).re) = (z / (1 - z)).re := by
  have hs0 : Summable (fun k : ℕ => z ^ k) :=
    (hasSum_geometric_of_norm_lt_one hz).summable
  have hs : Summable (fun k : ℕ => z ^ (k + 1)) := by
    have hmul : Summable (fun k : ℕ => z * z ^ k) := hs0.mul_left z
    apply hmul.congr
    intro k
    rw [pow_succ']
  calc
    (∑' k : ℕ, (z ^ (k + 1)).re) = ((∑' k : ℕ, z ^ (k + 1)) : ℂ).re := by
      symm
      simpa using Complex.reCLM.map_tsum hs
    _ = (z / (1 - z)).re := by rw [tsum_pow_succ hz]

/-- De Moivre form of the real part of a radial phase power. -/
theorem re_radial_phase_pow (r θ : ℝ) (m : ℕ) :
    (((r : ℂ) * Complex.exp (θ * Complex.I)) ^ m).re =
      r ^ m * Real.cos ((m : ℝ) * θ) := by
  rw [mul_pow]
  rw [← Complex.exp_nat_mul]
  have harg : (m : ℂ) * (θ * Complex.I) = (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  rw [Complex.mul_re, Complex.exp_re]
  simp

/-- Complex-power form of the positive-frequency Poisson fiber. -/
theorem two_mul_tsum_re_pow_succ_eq_KrClosed_sub_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    2 * (∑' k : ℕ,
      (((r : ℂ) * Complex.exp (θ * Complex.I)) ^ (k + 1)).re) =
      KrClosed r θ - 1 := by
  let z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I)
  have hz : ‖z‖ < 1 := by
    simp [z, abs_of_nonneg hr0, hr1]
  rw [tsum_re_pow_succ hz]
  exact (KrClosed_sub_one_eq_two_mul_re hr0 hr1 θ).symm

/-- Readable real cosine form of the one-sided Poisson fiber. -/
theorem two_mul_tsum_rpow_cos_eq_KrClosed_sub_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    2 * (∑' k : ℕ,
      r ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
      KrClosed r θ - 1 := by
  rw [← two_mul_tsum_re_pow_succ_eq_KrClosed_sub_one hr0 hr1 θ]
  congr 1
  apply tsum_congr
  intro k
  exact (re_radial_phase_pow r θ (k + 1)).symm

end GppPoissonGeometricFiber

#print axioms GppPoissonGeometricFiber.tsum_pow_succ
#print axioms GppPoissonGeometricFiber.re_radial_phase_pow
#print axioms GppPoissonGeometricFiber.two_mul_tsum_rpow_cos_eq_KrClosed_sub_one
