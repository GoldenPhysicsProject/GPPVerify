import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# A scalar Schur criterion at the form level, and a bounded example where truncations mislead

Source: Astra, `work/2026-10-22_astra_wave231_assembly_audit.md` (GPP-bridge), sections "A
constructive form-domain route for the scalar Schur step" and "Why one scalar still needs a global
estimate", written while auditing Turbo's 2026-10-22 RH assembly note. Daniel Toupin / Golden
Physics Project, with AI assistance from Astra (statements) and Claude Code (formalization).

* `nonneg_iff`: for a positive semidefinite bilinear form `a`, a linear functional `ℓ` and a
  real `c`, `a(u,u) + 2tℓ(u) + ct² ≥ 0` for all `(u, t)` iff `0 ≤ c` and `ℓ(u)² ≤ c·a(u,u)` for all
  `u`. This is Astra's "`P ≤ c`", with the price `P = ∞` when `ℓ` is nonzero on the null space of
  `a`. No inverse of `a`, no completion, and no Riesz representative are needed.
* Astra's example: `a_K(u) = ∑_{n≤K} u_n²/n²`, `ℓ_K(u) = ∑_{n≤K} u_n/n`, `c = 6`.
  `price_le` (Cauchy–Schwarz) and `price_attained` (`u_n = n`) show the finite price is exactly
  `K`; `truncation_nonneg_iff` shows the truncated form is nonnegative iff `K ≤ 6`, and
  `seven_witness` gives the value `−1` at `K = 7`. Both `a` and `ℓ` are bounded on `ℓ²`, so bounded
  operator realisation does not give positivity, and positive finite margins `6 − K` do not certify
  a limit.

**Scope.** These are general facts about quadratic forms. They do not prove Turbo's (SEP), any
operator realisation, OS reflection positivity, or anything about the zeros of `ζ`. Astra's audit
findings about the assembly note itself (conventions, labels) are not formalized here. No RH
content.
-/

open Finset

namespace GppScalarSchurForm

/-- **Astra's scalar Schur criterion (form level).** Let `a` be a positive semidefinite bilinear
form on a real vector space `V`, `ℓ` a linear functional and `c` real. Then
`Q(u, t) = a(u, u) + 2 t ℓ(u) + c t²` is nonnegative on `V × ℝ` iff `0 ≤ c` and
`ℓ(u)² ≤ c · a(u, u)` for every `u`. That is Astra's `P ≤ c`, with `P = ∞` when `ℓ` is nonzero on
the null space of `a`. No inverse of `a` and no completion are used. -/
theorem nonneg_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (a : LinearMap.BilinForm ℝ V)
    (ha : ∀ u, 0 ≤ a u u) (ℓ : V →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ u : V, ∀ t : ℝ, 0 ≤ a u u + 2 * t * ℓ u + c * t ^ 2) ↔
      (0 ≤ c ∧ ∀ u, ℓ u ^ 2 ≤ c * a u u) := by
  constructor
  · intro h
    refine ⟨?_, fun u => ?_⟩
    · have := h 0 1
      simpa using this
    · have hq : ∀ t : ℝ, 0 ≤ c * (t * t) + (2 * ℓ u) * t + a u u := fun t => by
        have := h u t; nlinarith
      have hd := discrim_le_zero hq
      unfold discrim at hd
      nlinarith
  · rintro ⟨hc, hL⟩ u t
    rcases hc.lt_or_eq with hc | hc
    · have h1 : 0 ≤ c * (a u u + 2 * t * ℓ u + c * t ^ 2) := by
        nlinarith [sq_nonneg (c * t + ℓ u), hL u]
      exact (mul_nonneg_iff_of_pos_left hc).mp h1
    · subst hc
      have : ℓ u = 0 := by nlinarith [hL u, sq_nonneg (ℓ u)]
      rw [this]; nlinarith [ha u]

/-- The truncated diagonal form `a_K(u) = ∑_{n=1}^K u_n²/n²`. -/
noncomputable def aK (K : ℕ) (u : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 K, u n ^ 2 / (n : ℝ) ^ 2

/-- The truncated functional `ℓ_K(u) = ∑_{n=1}^K u_n/n`. -/
noncomputable def lK (K : ℕ) (u : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 K, u n / n

/-- **The finite price is `K`.** `ℓ_K(u)² ≤ K a_K(u)` (Cauchy–Schwarz). -/
theorem price_le (K : ℕ) (u : ℕ → ℝ) : lK K u ^ 2 ≤ K * aK K u := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 K) (fun n => u n / n) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
    div_pow] at h
  rw [lK, aK]
  linarith [h]

/-- The price `K` is attained at `u_n = n`. -/
theorem price_attained (K : ℕ) : lK K (fun n => n) = K ∧ aK K (fun n => n) = K := by
  have h : ∀ n ∈ Icc 1 K, ((n : ℝ) / n = 1) ∧ ((n : ℝ) ^ 2 / (n : ℝ) ^ 2 = 1) := by
    intro n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
    exact ⟨div_self this, div_self (pow_ne_zero 2 this)⟩
  refine ⟨?_, ?_⟩
  · rw [lK, sum_congr rfl fun n hn => (h n hn).1]; simp
  · rw [aK, sum_congr rfl fun n hn => (h n hn).2]; simp

lemma neg_witness (K : ℕ) :
    lK K (fun n => -(n : ℝ)) = -K ∧ aK K (fun n => -(n : ℝ)) = K := by
  constructor
  · rw [lK]
    simp_rw [neg_div, sum_neg_distrib]
    rw [← lK, (price_attained K).1]
  · rw [aK]; simp_rw [neg_sq]; rw [← aK, (price_attained K).2]

/-- **Astra's separation example.** With `c = 6`, the truncated sewing form
`a_K(u) + 2 t ℓ_K(u) + 6 t²` is nonnegative iff `K ≤ 6`, although `a` and `ℓ` are bounded on
`ℓ²` (`∑ 1/n² < ∞`). Finite positive Schur margins `6 − K` do not certify the limit. -/
theorem truncation_nonneg_iff (K : ℕ) :
    (∀ (u : ℕ → ℝ) (t : ℝ), 0 ≤ aK K u + 2 * t * lK K u + 6 * t ^ 2) ↔ K ≤ 6 := by
  constructor
  · intro h
    by_contra hK
    have := h (fun n => -(n : ℝ)) 1
    rw [(neg_witness K).1, (neg_witness K).2] at this
    have : (7 : ℝ) ≤ K := by exact_mod_cast (by omega : 7 ≤ K)
    linarith
  · intro hK u t
    have hp := price_le K u
    have ha : 0 ≤ aK K u := sum_nonneg fun n _ => by positivity
    have hK' : (K : ℝ) ≤ 6 := by exact_mod_cast hK
    have h6 : lK K u ^ 2 ≤ 6 * aK K u := hp.trans (mul_le_mul_of_nonneg_right hK' ha)
    nlinarith [sq_nonneg (6 * t + lK K u)]

/-- At `K = 7` the explicit witness `u_n = −n`, `t = 1` gives the value `−1`. -/
theorem seven_witness : aK 7 (fun n => -(n : ℝ)) + 2 * 1 * lK 7 (fun n => -(n : ℝ)) + 6 * 1 ^ 2
    = -1 := by
  rw [(neg_witness 7).1, (neg_witness 7).2]
  norm_num

end GppScalarSchurForm
