import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Positive finite Fredholm determinants vanish only on the imaginary axis

Source: Codex, GPPDiscovery2 branch `codex/discovery-workbench`, Lean sandbox
`DiscoveryLean/PositiveFredholmFactor.lean` (2026-09-27, commit `c333773`), which proves the
scalar statement `1 + a z² = 0, a > 0 ⟹ Re z = 0, a·(Im z)² = 1`. Ported and upgraded here
2026-09-27.

The sandbox's scalar lemma is the one-mode case of the actual finite model behind the note
"Recast RH exactly as a positive density-matrix Fredholm problem" (workbench commit `c30455e`):
for a positive semidefinite Hermitian matrix `A`,

  det(I + z² A) = ∏ᵢ (1 + z² λᵢ),     λᵢ ≥ 0,

so the determinant vanishes only on the imaginary axis, exactly at `z = ±i/√λᵢ` for the positive
eigenvalues. With `z = s - 1/2` this is the finite Hilbert–Pólya shape: zeros on `Re s = 1/2`.

## Proved here

* `positive_factor_zero` (sandbox lemma, restated over ℂ): `1 + a z² = 0` with `a > 0` forces
  `Re z = 0` and `a (Im z)² = 1`;
* `det_one_add_smul_eq_prod`: `det(I + c A) = ∏ᵢ (1 + c λᵢ)` for Hermitian `A` (spectral theorem);
* `fredholm_zero_on_imaginary_axis`: for `A` positive semidefinite, `det(I + z² A) = 0` implies
  `Re z = 0` and `λᵢ (Im z)² = 1` for some eigenvalue `λᵢ > 0`;
* `fredholm_ne_zero_off_axis`: `Re z ≠ 0 → det(I + z² A) ≠ 0`;
* `negative_factor_real_zero`: without positivity the conclusion fails (a negative eigenvalue
  `λ` gives the real zero `z = 1/√(-λ)`).

## What this does and does not say

Positivity is exactly what confines the zeros: for a Hermitian `A` with a negative eigenvalue
`λ < 0`, `1 + z² λ` vanishes at the real points `z = ±1/√(-λ)`, off the imaginary axis. The
RH-strength content of the note is the existence of a positive trace-class `A` whose regularized
determinant is the completed zeta function; that is not constructed here, and nothing in this
file is a step that proves RH.
-/

open Matrix Complex
open scoped ComplexOrder

namespace GppPositiveFredholmFactor

/-- **Sandbox lemma, over ℂ.** If `a > 0` and `1 + a z² = 0`, then `Re z = 0` and
`a (Im z)² = 1`. -/
theorem positive_factor_zero (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 1 + (a : ℂ) * z ^ 2 = 0) :
    z.re = 0 ∧ a * z.im ^ 2 = 1 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sq, Complex.zero_re, Complex.add_im,
    Complex.one_im, Complex.mul_im, zero_add, Complex.zero_im] at hre him
  have hxy : z.re * z.im = 0 := by
    have : a * (z.re * z.im + z.im * z.re) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha.ne'
    · linarith
  have hx : z.re = 0 := by
    rcases mul_eq_zero.mp hxy with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re, mul_pos ha ha]
  refine ⟨hx, ?_⟩
  rw [hx] at hre
  nlinarith

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det(I + c A) = ∏ᵢ (1 + c λᵢ)` for a Hermitian matrix `A`. -/
theorem det_one_add_smul_eq_prod (A : Matrix n n ℂ) (hA : A.IsHermitian) (c : ℂ) :
    (1 + c • A).det = ∏ i, (1 + c * (hA.eigenvalues i : ℂ)) := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ)
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hAeq : A = U * D * star U := by
    have := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hconj : 1 + c • A = U * (1 + c • D) * star U := by
    rw [hAeq, mul_add, add_mul, mul_one, hUU, mul_smul_comm, smul_mul_assoc]
  have hdet : (U * (1 + c • D) * star U).det = (1 + c • D).det := by
    rw [det_mul, det_mul]
    calc U.det * (1 + c • D).det * (star U).det
        = (1 + c • D).det * (U.det * (star U).det) := by ring
      _ = (1 + c • D).det := by rw [← det_mul, hUU, det_one, mul_one]
  rw [hconj, hdet]
  have : (1 : Matrix n n ℂ) + c • D = diagonal (fun i => 1 + c * (hA.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [D]
    · simp [D, h]
  rw [this, det_diagonal]

/-- **Zeros only on the imaginary axis.** For positive semidefinite `A`, `det(I + z² A) = 0`
forces `Re z = 0`, with `λᵢ (Im z)² = 1` for some positive eigenvalue `λᵢ`. -/
theorem fredholm_zero_on_imaginary_axis (A : Matrix n n ℂ) (hA : A.PosSemidef) (z : ℂ)
    (hz : (1 + z ^ 2 • A).det = 0) :
    z.re = 0 ∧ ∃ i, 0 < hA.1.eigenvalues i ∧ hA.1.eigenvalues i * z.im ^ 2 = 1 := by
  rw [det_one_add_smul_eq_prod A hA.1, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  have hnn := hA.eigenvalues_nonneg i
  have hpos : 0 < hA.1.eigenvalues i := by
    rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h] at hi; simp at hi
  have hi' : 1 + ((hA.1.eigenvalues i : ℝ) : ℂ) * z ^ 2 = 0 := by
    rw [mul_comm]; exact hi
  obtain ⟨hx, hy⟩ := positive_factor_zero _ hpos z hi'
  exact ⟨hx, i, hpos, hy⟩

/-- `Re z ≠ 0 → det(I + z² A) ≠ 0` for positive semidefinite `A`. -/
theorem fredholm_ne_zero_off_axis (A : Matrix n n ℂ) (hA : A.PosSemidef) (z : ℂ)
    (hz : z.re ≠ 0) : (1 + z ^ 2 • A).det ≠ 0 :=
  fun h => hz (fredholm_zero_on_imaginary_axis A hA z h).1

/-- Positivity is necessary: a negative eigenvalue gives a real zero of `1 + z² λ`. -/
theorem negative_factor_real_zero (l : ℝ) (hl : l < 0) :
    1 + ((Real.sqrt (-l))⁻¹ : ℝ) ^ 2 * l = 0 := by
  have h : 0 < -l := by linarith
  rw [inv_pow, Real.sq_sqrt h.le, inv_mul_eq_div, div_neg, div_self hl.ne]
  ring

end GppPositiveFredholmFactor
