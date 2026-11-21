/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import GppVerify.RiemannHypothesis.UndampingTransfer
import GppVerify.RiemannHypothesis.UndampingGreenForm
import GppVerify.RiemannHypothesis.UndampingScalars

/-!
# Undamping package, items (b)/(c): form-level assembly and signed tail

**A transfer and tail statement, not a positivity proof for `Q₀`; nothing here proves RH.**
Assembles `UndampingTransfer` (item (a), merged #655), `UndampingGreenForm` (spectral Green form and
tail) and the pointwise kernel split `kernel_split` (`UndampingKernel`).

* (b) `Kform_split`: for bounded measurable `f` supported in `[0,L]`,
  `K_b(f,f) = 2b·G_D(f,f) + H_b(f,f)`, with all three as `ℝ²`-integral quadratic forms
  (`Kform`, `Gform`, `Hform`); `Gform_eq` identifies `G_D(f,f)` with `∫₀ᴸ f·(G_D f)`.
* (c) `undamping_signed_tail`: with `R_M := P − Σ_b (H_b + 2b·Σ_{n≤M} modeₙ) − primes` (`Rform`;
  `Q₂`, `P`, `H_b` and all prime shifts kept in full) and the omitted positive tails
  `tail_b = 2b·Σ_{n>M} modeₙ`:
  `Q₀ − Q₂ = R_M − Σ_b tail_b` exactly, `0 ≤ Σ_b tail_b ≤ ε_M·‖f‖²` with `ε_M` the scalar
  `epsTail` of `UndampingScalars`, hence `R_M − ε_M‖f‖² ≤ Q₀ − Q₂ ≤ R_M`.

Scope: statements about quadratic forms tested against bounded measurable `f` (the operator
inequality `R_M − ε_M I ≤ Q₀ ≤ R_M` is the statement "for every `f`"), not an operator object on
`L²(0,L)`. `Q₀`, `Q₂` individually are not defined (see `UndampingTransfer`: the theorem concerns
`Q₀ − Q₂`). This bounds the undamping resolvent remainder only; it does not bound the full retained
form or `Q₂` (D2's open items). No `sorry`, no `axiom`.
-/


open MeasureTheory Set GppUndampingTransfer GppUndampingKernel GppSineBasis GppGreenForm

namespace GppUndampingForms

/-- Quadratic form of the Dirichlet Green kernel on `ℝ²` (for `f` supported in `[0,L]`). -/
noncomputable def Gform (b L : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, f p.1 * f p.2 * greenD b L p.1 p.2

/-- Quadratic form of the explicit boundary kernel `H_b` (rank ≤ 2). -/
noncomputable def Hform (b L : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, f p.1 * f p.2 * Hb b L p.1 p.2

section Basic

variable {f : ℝ → ℝ} {L B : ℝ}

theorem integrable_kernel (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) {K : ℝ × ℝ → ℝ} (hK : Continuous K) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * K p) := by
  have hBB : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).prod (isCompact_Icc (a := (0 : ℝ)) (b := L))
    |>.exists_bound_of_continuousOn hK.continuousOn
  refine integrable_of_bound (S := Icc 0 L ×ˢ Icc 0 L) (C := B * B * M) ?_ ?_ (vol_box _ _ _ _) ?_ ?_
  · have := hK.measurable
    fun_prop
  · exact measurableSet_Icc.prod measurableSet_Icc
  · rintro ⟨x, y⟩ hp
    have h1 := hM _ hp
    rw [Real.norm_eq_abs] at h1
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h1
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hB x) (hB y) (abs_nonneg _) hBB) h1 (abs_nonneg _) (by positivity)
  · rintro ⟨x, y⟩ hp
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with h | h
    · simp [hs x h]
    · simp [hs y h]

theorem continuous_greenD2 (b L : ℝ) : Continuous (fun p : ℝ × ℝ => greenD b L p.1 p.2) := by
  unfold greenD; fun_prop

theorem continuous_Hb2 (b L : ℝ) : Continuous (fun p : ℝ × ℝ => Hb b L p.1 p.2) := by
  unfold Hb; fun_prop

/-- **(b) at form level.** `K_b(f,f) = 2b·G_D(f,f) + H_b(f,f)` for `f` supported in `[0,L]`. -/
theorem Kform_split {b L : ℝ} (hb : 0 < b) (hL : 0 < L) (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (hs : ∀ x, x ∉ Icc 0 L → f x = 0) :
    Kform b f = 2 * b * Gform b L f + Hform b L f := by
  have iG := integrable_kernel hf hB hs (continuous_greenD2 b L)
  have iH := integrable_kernel hf hB hs (continuous_Hb2 b L)
  unfold Kform Gform Hform
  rw [← integral_const_mul, ← integral_add (iG.const_mul (2 * b)) iH]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [show Real.exp (-b * |p.1 - p.2|) = 2 * b * greenD b L p.1 p.2 + Hb b L p.1 p.2 from
    kernel_split hb hL p.1 p.2]
  ring

theorem integral_eq_interval {F : ℝ → ℝ} (hF : ∀ y, y ∉ Icc 0 L → F y = 0) (hL : 0 ≤ L) :
    ∫ y, F y = ∫ y in (0 : ℝ)..L, F y := by
  rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hF y hy)).symm

/-- `G_D(f,f) = ∫₀ᴸ f · (G_D f)`: the double-integral form equals the iterated form of
`UndampingGreenForm`. -/
theorem Gform_eq {b L : ℝ} (hL : 0 < L) (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (hs : ∀ x, x ∉ Icc 0 L → f x = 0) :
    Gform b L f = ∫ x in (0 : ℝ)..L, f x * Gf b L f x := by
  have iG := integrable_kernel hf hB hs (continuous_greenD2 b L)
  unfold Gform
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact iG)]
  have hin : ∀ x : ℝ, ∫ y, f x * f y * greenD b L x y = f x * Gf b L f x := by
    intro x
    by_cases hx : x ∈ Icc 0 L
    · have : ∫ y, f x * f y * greenD b L x y = f x * ∫ y, f y * greenD b L x y := by
        rw [← integral_const_mul]; refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only; ring
      rw [this, integral_eq_interval (F := fun y => f y * greenD b L x y)
        (fun y hy => by simp [hs y hy]) hL.le]
      unfold Gf
      congr 1
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      rw [Set.uIcc_of_le hL.le] at hy
      simp only [gD, clamp_of_mem hx, clamp_of_mem hy]
      ring
    · simp [hs x hx]
  simp_rw [hin]
  exact integral_eq_interval (F := fun x => f x * Gf b L f x) (fun x hx => by simp [hs x hx]) hL.le

end Basic

section Assembly

variable {f : ℝ → ℝ} {L B : ℝ}
open ArithmeticFunction in
/-- The prime-shift part of `Q₀ − Q₂`, truncated at `n ≤ N`. -/
noncomputable def primeTerm (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (1 - ((n : ℝ) ^ 2)⁻¹) * (vonMangoldt n / Real.sqrt n) *
    shiftForm f (Real.log n)

/-- The retained part for rate `b` after `M + 1` Dirichlet modes: boundary form plus the first
`M + 1` modes of `2b·G_D`. -/
noncomputable def partB (b L : ℝ) (f : ℝ → ℝ) (M : ℕ) : ℝ :=
  Hform b L f + 2 * b * ∑ n ∈ Finset.range (M + 1), mode b L f n

/-- The omitted positive tail for rate `b`. -/
noncomputable def tailB (b L : ℝ) (f : ℝ → ℝ) (M : ℕ) : ℝ :=
  2 * b * ∑' i : ℕ, mode b L f (i + (M + 1))

/-- `R_M`: the reconstructed undamped difference form with the negative resolvent tail omitted;
`Q₂`, `P`, `H_b` and all prime shifts kept in full. -/
noncomputable def Rform (L : ℝ) (f : ℝ → ℝ) (M N : ℕ) : ℝ :=
  Pform f - partB (1 / 2) L f M - partB (3 / 2) L f M - partB (5 / 2) L f M - primeTerm f N

open ArithmeticFunction in
/-- **(c) at form level, with the exact decomposition.**  For bounded measurable `f` supported in
`[0,L]`: `Q₀ − Q₂ = R_M − Σ_b tail_b` (exact), `0 ≤ Σ_b tail_b ≤ ε_M ‖f‖²`, hence
`R_M − ε_M ‖f‖² ≤ Q₀ − Q₂ ≤ R_M`.  A transfer/tail statement, not a positivity proof. -/
theorem undamping_signed_tail (hL : 0 < L) (hf : Measurable f) (hB : ∀ x, |f x| ≤ B)
    (hs : ∀ x, x ∉ Icc 0 L → f x = 0) (M N : ℕ) :
    diffForm f N = Rform L f M N - (tailB (1 / 2) L f M + tailB (3 / 2) L f M + tailB (5 / 2) L f M) ∧
    0 ≤ tailB (1 / 2) L f M + tailB (3 / 2) L f M + tailB (5 / 2) L f M ∧
    tailB (1 / 2) L f M + tailB (3 / 2) L f M + tailB (5 / 2) L f M
      ≤ GppUndampingScalars.epsTail L M * ∫ x in (0 : ℝ)..L, (f x) ^ 2 := by
  have hT := undamping_transfer hf hB hs N
  have hGT : ∀ b : ℝ, 0 < b →
      Kform b f = 2 * b * (∑ n ∈ Finset.range (M + 1), mode b L f n + ∑' i : ℕ, mode b L f (i + (M + 1)))
        + Hform b L f ∧
      0 ≤ ∑' i : ℕ, mode b L f (i + (M + 1)) ∧
      ∑' i : ℕ, mode b L f (i + (M + 1))
        ≤ (∫ x in (0 : ℝ)..L, (f x) ^ 2) / (b ^ 2 + (((M : ℝ) + 1) * Real.pi / L) ^ 2) := by
    intro b hb
    obtain ⟨h1, h2, h3⟩ := green_tail hb hL hf hB M
    refine ⟨?_, h2, ?_⟩
    · rw [Kform_split hb hL hf hB hs, Gform_eq hL hf hB hs, ← h1]
    · simpa [Nat.cast_add, Nat.cast_one] using h3
  obtain ⟨k1, t1, u1⟩ := hGT (1 / 2) (by norm_num)
  obtain ⟨k3, t3, u3⟩ := hGT (3 / 2) (by norm_num)
  obtain ⟨k5, t5, u5⟩ := hGT (5 / 2) (by norm_num)
  have hnorm : 0 ≤ ∫ x in (0 : ℝ)..L, (f x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hT, k1, k3, k5]
    unfold Rform partB tailB primeTerm
    ring
  · unfold tailB; positivity
  · unfold tailB GppUndampingScalars.epsTail
    rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_singleton]
    have e1 : 2 * (1 / 2 : ℝ) * ∑' i : ℕ, mode (1 / 2) L f (i + (M + 1))
        ≤ 2 * (1 / 2) * ((∫ x in (0 : ℝ)..L, (f x) ^ 2) / ((1 / 2) ^ 2 + (((M : ℝ) + 1) * Real.pi / L) ^ 2)) :=
      mul_le_mul_of_nonneg_left u1 (by norm_num)
    have e3 : 2 * (3 / 2 : ℝ) * ∑' i : ℕ, mode (3 / 2) L f (i + (M + 1))
        ≤ 2 * (3 / 2) * ((∫ x in (0 : ℝ)..L, (f x) ^ 2) / ((3 / 2) ^ 2 + (((M : ℝ) + 1) * Real.pi / L) ^ 2)) :=
      mul_le_mul_of_nonneg_left u3 (by norm_num)
    have e5 : 2 * (5 / 2 : ℝ) * ∑' i : ℕ, mode (5 / 2) L f (i + (M + 1))
        ≤ 2 * (5 / 2) * ((∫ x in (0 : ℝ)..L, (f x) ^ 2) / ((5 / 2) ^ 2 + (((M : ℝ) + 1) * Real.pi / L) ^ 2)) :=
      mul_le_mul_of_nonneg_left u5 (by norm_num)
    calc _ ≤ _ := add_le_add (add_le_add e1 e3) e5
      _ = _ := by ring

end Assembly

end GppUndampingForms

#print axioms GppUndampingForms.Kform_split
#print axioms GppUndampingForms.Gform_eq
#print axioms GppUndampingForms.undamping_signed_tail
