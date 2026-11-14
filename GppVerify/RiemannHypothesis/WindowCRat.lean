import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Complex rationals for kernel checks

A minimal computable model of `ℚ + ℚ i` (pairs of rationals) with multiplication, inverse and
powers, and the cast lemmas into `ℂ`, so that quantities like `Re((-i/2)^n / s₀^{n+1})` with
`s₀ = a + i c/2` (`a, c ∈ ℚ`) can be computed by `decide` and identified with the real numbers they
stand for (`toC_mul`, `toC_inv`, `toC_pow`).

Unconditional; no `sorry`, no axioms.
-/

namespace GppWindowCRat

/-- A complex rational `x + y i`. -/
abbrev CQ := ℚ × ℚ

def mulQ (z w : CQ) : CQ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def invQ (z : CQ) : CQ := (z.1 / (z.1 ^ 2 + z.2 ^ 2), -z.2 / (z.1 ^ 2 + z.2 ^ 2))

def powQ (z : CQ) : ℕ → CQ
  | 0 => (1, 0)
  | n + 1 => mulQ (powQ z n) z

/-- The complex number a complex rational stands for. -/
noncomputable def toC (z : CQ) : ℂ := ((z.1 : ℝ) : ℂ) + ((z.2 : ℝ) : ℂ) * Complex.I

theorem toC_re (z : CQ) : (toC z).re = (z.1 : ℝ) := by simp [toC]

theorem toC_mul (z w : CQ) : toC (mulQ z w) = toC z * toC w := by
  apply Complex.ext <;> simp [toC, mulQ]

theorem toC_pow (z : CQ) (n : ℕ) : toC (powQ z n) = toC z ^ n := by
  induction n with
  | zero => simp [powQ, toC]
  | succ n ih => rw [powQ, toC_mul, ih, pow_succ]

theorem toC_inv (z : CQ) : toC (invQ z) = (toC z)⁻¹ := by
  have hx : ((z.1 / (z.1 ^ 2 + z.2 ^ 2) : ℚ) : ℝ) =
      (z.1 : ℝ) / ((z.1 : ℝ) * (z.1 : ℝ) + (z.2 : ℝ) * (z.2 : ℝ)) := by push_cast; ring_nf
  have hy : ((-z.2 / (z.1 ^ 2 + z.2 ^ 2) : ℚ) : ℝ) =
      -(z.2 : ℝ) / ((z.1 : ℝ) * (z.1 : ℝ) + (z.2 : ℝ) * (z.2 : ℝ)) := by push_cast; ring_nf
  unfold toC invQ
  rw [hx, hy]
  apply Complex.ext
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring

end GppWindowCRat

#print axioms GppWindowCRat.toC_inv
