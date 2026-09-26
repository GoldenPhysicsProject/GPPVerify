import GppVerify.RiemannHypothesis.ScaleShadowHalfDensity
import Mathlib.Tactic

/-!
# Arithmetic split coordinates about the half-density center

Write

  sigma(s) = Re(s) - 1/2,
  tau(s)   = Im(s),

and introduce the real light-cone combinations

  xi_+(s) = sigma(s) + tau(s),
  xi_-(s) = sigma(s) - tau(s).

These coordinates give an exact split quadratic identity

  xi_+(s) xi_-(s) = sigma(s)^2 - tau(s)^2.

The arithmetic involutions act particularly simply:

* Riemann shadow `s -> 1-s` negates both `xi_+` and `xi_-`;
* complex conjugation swaps `xi_+` and `xi_-`.

The critical line is not the null cone of this split form. It is exactly the
anti-diagonal `xi_+ = -xi_-`. On that anti-diagonal, swapping the coordinates is
the same operation as negating both, which is the real-coordinate content of the
already-proved identity `conj s = 1-s` on `Re s = 1/2`.

The sum `xi_+ + xi_-` is twice the nonunitary displacement `sigma`, while their
difference is twice the spectral coordinate `tau`. Therefore the modulus of the
half-density character depends only on the symmetric split combination, and the
critical line is exactly where that combination vanishes.

Under the project dictionary `Delta = 2s`, the corresponding celestial centered
coordinates scale by exactly two.
-/

namespace GppArithmeticSplitCoordinates

open Complex
open GppScaleShadow
open GppScaleMass

/-- Real displacement from the half-density center `Re s = 1/2`. -/
noncomputable def sigma (s : ℂ) : ℝ := s.re - 1 / 2

/-- Spectral coordinate along the critical line. -/
noncomputable def tau (s : ℂ) : ℝ := s.im

/-- First real light-cone coordinate about the arithmetic center. -/
noncomputable def xiPlus (s : ℂ) : ℝ := sigma s + tau s

/-- Second real light-cone coordinate about the arithmetic center. -/
noncomputable def xiMinus (s : ℂ) : ℝ := sigma s - tau s

/-- Split quadratic factorization in arithmetic centered coordinates. -/
theorem xiPlus_mul_xiMinus (s : ℂ) :
    xiPlus s * xiMinus s = sigma s ^ 2 - tau s ^ 2 := by
  unfold xiPlus xiMinus
  ring

/-- The symmetric split combination reconstructs the off-critical displacement. -/
theorem sigma_eq_half_split_sum (s : ℂ) :
    sigma s = (xiPlus s + xiMinus s) / 2 := by
  unfold xiPlus xiMinus
  ring

/-- The antisymmetric split combination reconstructs the spectral coordinate. -/
theorem tau_eq_half_split_difference (s : ℂ) :
    tau s = (xiPlus s - xiMinus s) / 2 := by
  unfold xiPlus xiMinus
  ring

/-- Riemann shadow negates the centered real displacement. -/
theorem sigma_shadow (s : ℂ) : sigma (1 - s) = -sigma s := by
  unfold sigma
  simp
  ring

/-- Riemann shadow reverses the spectral coordinate. -/
theorem tau_shadow (s : ℂ) : tau (1 - s) = -tau s := by
  simp [tau]

/-- Riemann shadow negates the first split coordinate. -/
theorem xiPlus_shadow (s : ℂ) : xiPlus (1 - s) = -xiPlus s := by
  unfold xiPlus
  rw [sigma_shadow, tau_shadow]
  ring

/-- Riemann shadow negates the second split coordinate. -/
theorem xiMinus_shadow (s : ℂ) : xiMinus (1 - s) = -xiMinus s := by
  unfold xiMinus
  rw [sigma_shadow, tau_shadow]
  ring

/-- Complex conjugation swaps the first split coordinate with the second. -/
theorem xiPlus_conj (s : ℂ) :
    xiPlus ((starRingEnd ℂ) s) = xiMinus s := by
  unfold xiPlus xiMinus sigma tau
  simp
  ring

/-- Complex conjugation swaps the second split coordinate with the first. -/
theorem xiMinus_conj (s : ℂ) :
    xiMinus ((starRingEnd ℂ) s) = xiPlus s := by
  unfold xiPlus xiMinus sigma tau
  simp

/-- The Riemann critical line is exactly the anti-diagonal in split coordinates. -/
theorem critical_line_iff_antidiagonal (s : ℂ) :
    s.re = 1 / 2 ↔ xiPlus s = -xiMinus s := by
  unfold xiPlus xiMinus sigma tau
  constructor <;> intro h
  · rw [h]
    ring
  · linarith

/-- Equivalent symmetric form: criticality means the split-coordinate sum vanishes. -/
theorem critical_line_iff_split_sum_zero (s : ℂ) :
    s.re = 1 / 2 ↔ xiPlus s + xiMinus s = 0 := by
  rw [critical_line_iff_antidiagonal]
  constructor <;> intro h <;> linarith

/-- On the critical line, coordinate swap equals simultaneous sign reversal. -/
theorem conj_split_eq_shadow_split {s : ℂ} (hs : s.re = 1 / 2) :
    xiPlus ((starRingEnd ℂ) s) = xiPlus (1 - s) ∧
      xiMinus ((starRingEnd ℂ) s) = xiMinus (1 - s) := by
  have hadiag : xiPlus s = -xiMinus s :=
    (critical_line_iff_antidiagonal s).1 hs
  constructor
  · rw [xiPlus_conj, xiPlus_shadow]
    linarith
  · rw [xiMinus_conj, xiMinus_shadow]
    linarith

/-- Exact half-density modulus written in split coordinates. The symmetric split
combination controls growth/decay under positive-real dilation. -/
theorem norm_dilationCharacter_split (s : ℂ) (a : ℝ) :
    ‖dilationCharacter s a‖ =
      Real.exp (Real.log a * ((xiPlus s + xiMinus s) / 2)) := by
  rw [norm_dilationCharacter]
  rw [← sigma_eq_half_split_sum]
  rfl

/-- At any fixed nontrivial positive scale, unit modulus is equivalent to the
anti-diagonal split condition. -/
theorem split_antidiagonal_iff_dilation_unitary
    {s : ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    xiPlus s = -xiMinus s ↔ ‖dilationCharacter s a‖ = 1 := by
  rw [← critical_line_iff_antidiagonal]
  exact critical_line_iff_dilation_unitary ha ha1

/-- Celestial centered real displacement for `Delta = 2s`. -/
noncomputable def deltaSigma (s : ℂ) : ℝ := (celestialDelta s).re - 1

/-- Celestial spectral coordinate for `Delta = 2s`. -/
noncomputable def deltaTau (s : ℂ) : ℝ := (celestialDelta s).im

/-- `Delta = 2s` doubles the centered real arithmetic coordinate. -/
theorem deltaSigma_eq_two_mul_sigma (s : ℂ) :
    deltaSigma s = 2 * sigma s := by
  simp [deltaSigma, sigma, celestialDelta]
  ring

/-- `Delta = 2s` doubles the arithmetic spectral coordinate. -/
theorem deltaTau_eq_two_mul_tau (s : ℂ) :
    deltaTau s = 2 * tau s := by
  simp [deltaTau, tau, celestialDelta]

/-- Celestial first split coordinate, centered at `Re Delta = 1`. -/
noncomputable def deltaXiPlus (s : ℂ) : ℝ := deltaSigma s + deltaTau s

/-- Celestial second split coordinate, centered at `Re Delta = 1`. -/
noncomputable def deltaXiMinus (s : ℂ) : ℝ := deltaSigma s - deltaTau s

/-- The project dictionary doubles the first split coordinate exactly. -/
theorem deltaXiPlus_eq_two_mul_xiPlus (s : ℂ) :
    deltaXiPlus s = 2 * xiPlus s := by
  rw [deltaXiPlus, deltaSigma_eq_two_mul_sigma, deltaTau_eq_two_mul_tau]
  simp [xiPlus]
  ring

/-- The project dictionary doubles the second split coordinate exactly. -/
theorem deltaXiMinus_eq_two_mul_xiMinus (s : ℂ) :
    deltaXiMinus s = 2 * xiMinus s := by
  rw [deltaXiMinus, deltaSigma_eq_two_mul_sigma, deltaTau_eq_two_mul_tau]
  simp [xiMinus]
  ring

end GppArithmeticSplitCoordinates

#print axioms GppArithmeticSplitCoordinates.xiPlus_mul_xiMinus
#print axioms GppArithmeticSplitCoordinates.sigma_eq_half_split_sum
#print axioms GppArithmeticSplitCoordinates.tau_eq_half_split_difference
#print axioms GppArithmeticSplitCoordinates.xiPlus_shadow
#print axioms GppArithmeticSplitCoordinates.xiMinus_shadow
#print axioms GppArithmeticSplitCoordinates.xiPlus_conj
#print axioms GppArithmeticSplitCoordinates.xiMinus_conj
#print axioms GppArithmeticSplitCoordinates.critical_line_iff_antidiagonal
#print axioms GppArithmeticSplitCoordinates.critical_line_iff_split_sum_zero
#print axioms GppArithmeticSplitCoordinates.conj_split_eq_shadow_split
#print axioms GppArithmeticSplitCoordinates.norm_dilationCharacter_split
#print axioms GppArithmeticSplitCoordinates.split_antidiagonal_iff_dilation_unitary
#print axioms GppArithmeticSplitCoordinates.deltaXiPlus_eq_two_mul_xiPlus
#print axioms GppArithmeticSplitCoordinates.deltaXiMinus_eq_two_mul_xiMinus
