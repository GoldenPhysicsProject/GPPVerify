import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import GppVerify.RiemannHypothesis.FourComponentRigidity

/-!
# The conformal Casimir `s(1−s)` and the critical line

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-28_rh_selfadjoint_conformal_casimir.md` (commit `1c74389`) and its checker
`DiscoveryLean/CasimirCriticalLine.lean` (`d2c09af`).

The note recasts RH in the `PSL(2,ℝ)` Casimir variable `c = s(1−s) = ¼ − z²`, `s = ½ + z`. It makes
four exact claims, all proved here.

* **§1. `ξ` is a function of the Casimir.** `xi_factors_through_casimir`: there is a function
  `X` with `ξ(s) = X(s(1−s))` for every `s`. The proof is that `s(1−s) = t(1−t)` forces
  `t = s` or `t = 1−s` (`casimir_eq_iff`), and `ξ(1−s) = ξ(s)`.
* **§2. The principal series is the Casimir threshold.** `casimir_half_add`:
  `(½ + iλ)(½ − iλ) = ¼ + λ²`.
* **§3. A real Casimir forces the line.** `casimir_im`: `Im ρ(1−ρ) = γ(1 − 2β)`.
  `casimir_real_iff`: `ρ(1−ρ) ∈ ℝ ↔ Re ρ = ½ ∨ Im ρ = 0`. Codex's checker proved only the
  forward direction for `γ ≠ 0`.
* **§4. The threshold form, as an equivalence.** `casimir_ge_quarter_iff`:
  `ρ(1−ρ)` is real and `≥ ¼` **iff** `Re ρ = ½`. This holds with no side condition; the note
  states only the forward direction.
* **§5. Positive-Fredholm ↔ Casimir dictionary.** `fredholm_casimir_matrix`: for invertible `A`
  and `C = ¼ I + A⁻¹`, `(C − c I) A = I + (¼ − c) A`. So
  `det(I + z²A) = det(C − cI) · det A` with `c = ¼ − z²`. This is the note's
  `Ξ(z) = det[(C − c)(C − ¼)⁻¹]`, in finite dimensions.

## Scope

`X` is constructed as a function. That it is entire (via the even Taylor series) is not
formalized. §3–§4 are statements about complex numbers. RH would follow from them only after
constructing, without zero data, a self-adjoint `C_phys ≥ ¼` whose spectral determinant is `ξ`.
That construction is exactly the open problem, as the note says. The finite-dimensional §5
identity does not supply it. This file makes no RH claim, and neither does the note.
-/

open Complex

namespace GppCasimirCriticalLine

open GppFourComponentRigidity

/-- The conformal Casimir `c(s) = s(1−s)`. -/
def casimir (s : ℂ) : ℂ := s * (1 - s)

/-- `Im ρ(1−ρ) = γ(1 − 2β)` for `ρ = β + iγ`. -/
theorem casimir_im (ρ : ℂ) : (casimir ρ).im = ρ.im * (1 - 2 * ρ.re) := by
  simp [casimir, mul_im, sub_im, sub_re]; ring

/-- `Re ρ(1−ρ) = β(1−β) + γ²`. -/
theorem casimir_re (ρ : ℂ) : (casimir ρ).re = ρ.re * (1 - ρ.re) + ρ.im ^ 2 := by
  simp [casimir, mul_re, sub_im, sub_re]; ring

/-- **A real Casimir forces the critical line or the real axis.** -/
theorem casimir_real_iff (ρ : ℂ) : (casimir ρ).im = 0 ↔ ρ.re = 1 / 2 ∨ ρ.im = 0 := by
  rw [casimir_im, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl h

/-- Codex's checker: for a nonreal `ρ`, a real Casimir forces `Re ρ = ½`. -/
theorem real_casimir_forces_half (ρ : ℂ) (hγ : ρ.im ≠ 0) (h : (casimir ρ).im = 0) :
    ρ.re = 1 / 2 :=
  ((casimir_real_iff ρ).mp h).resolve_right hγ

/-- **The principal series.** `c(½ + iλ) = ¼ + λ²`. -/
theorem casimir_half_add (lam : ℝ) : casimir (1 / 2 + lam * I) = 1 / 4 + (lam : ℂ) ^ 2 := by
  simp only [casimir]
  linear_combination (-(lam : ℂ) ^ 2) * I_sq

/-- **The threshold, as an equivalence.** `ρ(1−ρ)` is real and at least `¼` iff `Re ρ = ½`. -/
theorem casimir_ge_quarter_iff (ρ : ℂ) :
    ((casimir ρ).im = 0 ∧ 1 / 4 ≤ (casimir ρ).re) ↔ ρ.re = 1 / 2 := by
  rw [casimir_im, casimir_re]
  constructor
  · rintro ⟨him, hre⟩
    rcases mul_eq_zero.mp him with h | h
    · rw [h] at hre
      nlinarith [sq_nonneg (ρ.re - 1 / 2)]
    · linarith
  · intro h
    rw [h]
    exact ⟨by ring, by nlinarith [sq_nonneg ρ.im]⟩

/-- `s(1−s) = t(1−t)` iff `t = s` or `t = 1 − s`. -/
theorem casimir_eq_iff (s t : ℂ) : casimir s = casimir t ↔ t = s ∨ t = 1 - s := by
  have key : casimir s - casimir t = (t - s) * (t - (1 - s)) := by
    simp only [casimir]; ring
  rw [← sub_eq_zero, key, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- `ξ(1 − s) = ξ(s)`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  rw [xi, xi, completedRiemannZeta_one_sub]; ring

/-- A point with prescribed Casimir: `c(½ + √(¼ − c)) = c`. -/
theorem casimir_root (c : ℂ) :
    casimir (1 / 2 + (1 / 4 - c) ^ ((2 : ℕ)⁻¹ : ℂ)) = c := by
  have h := cpow_nat_inv_pow (1 / 4 - c) (n := 2) two_ne_zero
  simp only [casimir]
  linear_combination -h

/-- **§1: `ξ` factors through the Casimir.** There is a function `X` with `ξ(s) = X(s(1−s))`.
(That `X` is entire is not formalized here.) -/
theorem xi_factors_through_casimir :
    ∃ X : ℂ → ℂ, ∀ s, xi s = X (casimir s) := by
  refine ⟨fun c => xi (1 / 2 + (1 / 4 - c) ^ ((2 : ℕ)⁻¹ : ℂ)), fun s => ?_⟩
  have h := casimir_root (casimir s)
  rcases (casimir_eq_iff s _).mp h.symm with h1 | h1
  · simp only; rw [h1]
  · simp only; rw [h1, xi_one_sub]

/-- **§5: the positive-Fredholm ↔ Casimir dictionary.** For invertible `A` and `C = ¼ I + A⁻¹`,
`(C − c I) A = I + (¼ − c) A`. -/
theorem fredholm_casimir_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) [Invertible A] (c : ℂ) :
    ((1 / 4 : ℂ) • (1 : Matrix n n ℂ) + A⁻¹ - c • 1) * A = 1 + (1 / 4 - c) • A := by
  rw [sub_mul, add_mul, Matrix.inv_mul_of_invertible, smul_mul_assoc, one_mul,
    smul_mul_assoc, one_mul, sub_smul]
  abel

/-- The determinant form: `det(I + (¼ − c) A) = det(C − cI) · det A`. With `c = ¼ − z²` this is
`det(I + z² A) = det(C − cI) · det A`. -/
theorem fredholm_casimir_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) [Invertible A] (c : ℂ) :
    (1 + (1 / 4 - c) • A).det = ((1 / 4 : ℂ) • (1 : Matrix n n ℂ) + A⁻¹ - c • 1).det * A.det := by
  rw [← Matrix.det_mul, fredholm_casimir_matrix]

end GppCasimirCriticalLine
