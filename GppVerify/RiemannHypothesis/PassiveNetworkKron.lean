import GppVerify.RiemannHypothesis.PrimeEdgeDtn
import GppVerify.RiemannHypothesis.SchurGapTransfer
import Mathlib.Tactic

/-!
# Passive-network lemmas for the semilocal Weil/Kron route

Finite algebra only.  These lemmas isolate the two facts needed before any
arithmetic identification is attempted:

1. a positive parent block with positive-definite interior has positive
   Kron/Schur reduction;
2. the massive interval DtN block used for prime edges has positive even and
   odd channel energies, with determinant one.

No Weil-form identification and no RH claim is made here.
-/

open Matrix

namespace GppPassiveNetwork

open GppPrimeEdgeDtn
open GppSchurGapTransfer

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A positive finite parent network has positive Kron reduction whenever the
    eliminated interior block is positive definite. -/
theorem kron_reduction_posSemidef
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : A.PosDef) [Invertible A]
    (hH : (fromBlocks A B Bᴴ C).PosSemidef) :
    (C - Bᴴ * A⁻¹ * B).PosSemidef := by
  have h :=
    (schur_gap_iff A B C 0 hA).mp
      (by simpa using hH)
  simpa using h

/-- The even DtN channel eigenvalue is strictly positive for positive edge length. -/
theorem dtn_even_channel_pos (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < coth ℓ - csch ℓ := by
  rw [dtn_eigen_tanh ℓ hℓ, Real.tanh_eq_sinh_div_cosh]
  exact div_pos
    (Real.sinh_pos_iff.mpr (by linarith))
    (Real.cosh_pos _)

/-- The odd DtN channel eigenvalue is strictly positive for positive edge length. -/
theorem dtn_odd_channel_pos (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < coth ℓ + csch ℓ := by
  have hs : 0 < Real.sinh ℓ := Real.sinh_pos_iff.mpr hℓ
  have hc : 0 < Real.cosh ℓ := Real.cosh_pos _
  have hn : 0 < Real.cosh ℓ + 1 := by linarith
  rw [show coth ℓ + csch ℓ = (Real.cosh ℓ + 1) / Real.sinh ℓ by
    unfold coth csch
    ring]
  exact div_pos hn hs

/-- Diagonalization of the scalar DtN energy into even and odd boundary channels. -/
theorem dtn_energy_decomposition (ℓ x y : ℝ) :
    coth ℓ * (x ^ 2 + y ^ 2) - 2 * csch ℓ * x * y =
      (1 / 2 : ℝ) * (coth ℓ - csch ℓ) * (x + y) ^ 2 +
      (1 / 2 : ℝ) * (coth ℓ + csch ℓ) * (x - y) ^ 2 := by
  ring

/-- The interval DtN energy is nonnegative for every pair of boundary values. -/
theorem dtn_energy_nonneg (ℓ x y : ℝ) (hℓ : 0 < ℓ) :
    0 ≤ coth ℓ * (x ^ 2 + y ^ 2) - 2 * csch ℓ * x * y := by
  rw [dtn_energy_decomposition]
  have he : 0 ≤ coth ℓ - csch ℓ := (dtn_even_channel_pos ℓ hℓ).le
  have ho : 0 ≤ coth ℓ + csch ℓ := (dtn_odd_channel_pos ℓ hℓ).le
  have hx : 0 ≤ (x + y) ^ 2 := sq_nonneg _
  have hy : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  positivity

/-- The massive DtN block has determinant one. -/
theorem dtn_det_one (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (dtn ℓ).det = 1 := by
  rw [dtn, Matrix.det_fin_two_of]
  simpa [pow_two] using coth_sq_sub_csch_sq ℓ hℓ

end GppPassiveNetwork
