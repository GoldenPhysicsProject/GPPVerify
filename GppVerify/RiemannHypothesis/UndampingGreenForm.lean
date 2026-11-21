/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import GppVerify.RiemannHypothesis.DirichletSineParseval
import GppVerify.RiemannHypothesis.UndampingKernel
import GppVerify.RiemannHypothesis.UndampingSine

/-!
# Undamping package, items (b)/(c): spectral representation of the Dirichlet Green form

Built on `DirichletSineParseval` (sine Parseval) and the pointwise `greenD_sine` eigenvalue relation
(`UndampingSine`). For a bounded measurable real `f` on `[0, L]` and `b, L > 0`, with
`(G_D f)(x) = ∫₀ᴸ G_D(x,y) f(y) dy` (`Gf`; the kernel is clamped to `[0,L]` (`gD`) so it is globally
bounded and symmetric):

* `rc_Gf`: the sine coefficients transform diagonally, `cₙ(G_D f) = cₙ(f)/(b² + (nπ/L)²)`.
* `green_form`: `∫₀ᴸ f · G_D f = (2/L) Σₙ cₙ(f)² / (b² + (nπ/L)²)` (as a `HasSum`).
* `green_tail`: splitting after the modes `0 … M`, the remaining sum is nonnegative and at most
  `‖f‖²/(b² + ((M+1)π/L)²)` (`‖f‖² = ∫₀ᴸ f²`); this is the **form-level** version of the signed tail
  constant (`2b ×` it is `≤ 2b/(b²+((M+1)π/L)²) · ‖f‖²`, the summand of `epsTail` in
  `UndampingScalars`).

Scope: these are statements about the quadratic form of the Green operator on bounded measurable
`f`, i.e. the operator statement `2b(−∂²+b²)_D⁻¹ = Σ 2b/(b²+ωₙ²) |sinₙ⟩⟨sinₙ|` tested against `f`; no
operator object on `L²(0,L)` is constructed. The assembly with the kernel split `K_b = 2b G_D + H_b`
and the transfer identity is a separate step. No `sorry`, no `axiom`; no positivity claim for `Q₀`.
-/


open MeasureTheory Set GppSineBasis GppUndampingKernel

namespace GppGreenForm

/-- Clamp to `[0, L]`. -/
noncomputable def clamp (L x : ℝ) : ℝ := max 0 (min x L)

theorem clamp_mem {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : clamp L x ∈ Icc 0 L :=
  ⟨le_max_left _ _, max_le hL (min_le_right _ _)⟩

theorem clamp_of_mem {L x : ℝ} (hx : x ∈ Icc 0 L) : clamp L x = x := by
  unfold clamp; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem continuous_clamp (L : ℝ) : Continuous (clamp L) := by unfold clamp; fun_prop

/-- Globally bounded, symmetric extension of the Dirichlet Green kernel. -/
noncomputable def gD (b L x y : ℝ) : ℝ := greenD b L (clamp L x) (clamp L y)

theorem gD_symm (b L x y : ℝ) : gD b L x y = gD b L y x := by
  unfold gD greenD; rw [min_comm, max_comm]

theorem continuous_gD (b L : ℝ) : Continuous (fun p : ℝ × ℝ => gD b L p.1 p.2) := by
  have hc := continuous_clamp L
  unfold gD greenD
  fun_prop

theorem gD_bound (b L : ℝ) (hL : 0 ≤ L) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, |gD b L x y| ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L) := isCompact_Icc.prod isCompact_Icc
  have hc : Continuous (fun p : ℝ × ℝ => greenD b L p.1 p.2) := by unfold greenD; fun_prop
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := hM (clamp L x, clamp L y) ⟨clamp_mem hL x, clamp_mem hL y⟩
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)

theorem gD_sine {b L x : ℝ} (hb : 0 < b) (hL : 0 < L) (hx : x ∈ Icc 0 L) (n : ℕ) :
    ∫ y in (0 : ℝ)..L, gD b L x y * Real.sin (n * Real.pi * y / L)
      = Real.sin (n * Real.pi * x / L) / (b ^ 2 + (n * Real.pi / L) ^ 2) := by
  have h := greenD_sine hb hL hx.1 hx.2 n
  have e1 : ∫ y in (0 : ℝ)..L, gD b L x y * Real.sin (n * Real.pi * y / L)
      = ∫ y in (0 : ℝ)..L, greenD b L x y * Real.sin ((n * Real.pi / L) * y) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hL.le] at hy
    simp only [gD, clamp_of_mem hx, clamp_of_mem hy]
    congr 2; ring
  rw [e1, h]
  congr 2; ring

theorem swap_int {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hC : ∀ x y, |F x y| ≤ C) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (0 : ℝ)..L, ∫ y in (0 : ℝ)..L, F x y
      = ∫ y in (0 : ℝ)..L, ∫ x in (0 : ℝ)..L, F x y := by
  simp_rw [intervalIntegral.integral_of_le hL]
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) := ⟨by simp⟩
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) L)).prod (volume.restrict (Ioc (0 : ℝ) L))) :=
    (integrable_const C).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact hC p.1 p.2)
  exact integral_integral_swap hint

/-- `(G_D f)(x) = ∫₀ᴸ G_D(x,y) f(y) dy` with the clamped kernel. -/
noncomputable def Gf (b L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..L, gD b L x y * f y

theorem Gf_measurable {b L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (Gf b L f) := by
  unfold Gf
  simp_rw [intervalIntegral.integral_of_le hL]
  have : StronglyMeasurable (Function.uncurry fun x y : ℝ => gD b L x y * f y) :=
    ((continuous_gD b L).measurable.mul (hf.comp measurable_snd)).stronglyMeasurable
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) L)) this).measurable

theorem Gf_bound {b L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ∃ C : ℝ, ∀ x, |Gf b L f x| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := gD_bound b L hL
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine ⟨M * B * L, fun x => ?_⟩
  unfold Gf
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
    (f := fun y => gD b L x y * f y) (C := M * B) (fun y _ => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hM x y) (hB y) (abs_nonneg _) hM0)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hL] at this
  exact this

/-- **Eigen-expansion of the Green transform on sine coefficients.** -/
theorem rc_Gf {b L : ℝ} (hb : 0 < b) (hL : 0 < L) {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (n : ℕ) :
    rc L (Gf b L f) n = rc L f n / (b ^ 2 + (n * Real.pi / L) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := gD_bound b L hL.le
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set θ : ℝ → ℝ := fun x => Real.sin (n * Real.pi * x / L) with hθ
  have hθm : Measurable θ := by simp only [hθ]; fun_prop
  have hθb : ∀ x, |θ x| ≤ 1 := fun x => Real.abs_sin_le_one _
  unfold rc
  have h1 : ∫ x in (0 : ℝ)..L, Real.sin (n * Real.pi * x / L) * Gf b L f x
      = ∫ x in (0 : ℝ)..L, ∫ y in (0 : ℝ)..L, θ x * (gD b L x y * f y) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [Gf, hθ]
    rw [intervalIntegral.integral_const_mul]
  rw [h1]
  have hFm : Measurable (Function.uncurry fun x y : ℝ => θ x * (gD b L x y * f y)) :=
    (hθm.comp measurable_fst).mul (((continuous_gD b L).measurable).mul (hf.comp measurable_snd))
  rw [swap_int hFm (C := M * B) (fun x y => by
      rw [abs_mul, abs_mul]
      calc |θ x| * (|gD b L x y| * |f y|) ≤ 1 * (M * B) :=
            mul_le_mul (hθb x) (mul_le_mul (hM x y) (hB y) (abs_nonneg _) hM0) (by positivity) zero_le_one
        _ = M * B := one_mul _) hL.le]
  have h2 : ∀ y ∈ Set.uIcc (0 : ℝ) L, ∫ x in (0 : ℝ)..L, θ x * (gD b L x y * f y)
      = f y * Real.sin (n * Real.pi * y / L) / (b ^ 2 + (n * Real.pi / L) ^ 2) := by
    intro y hy
    rw [Set.uIcc_of_le hL.le] at hy
    have : ∫ x in (0 : ℝ)..L, θ x * (gD b L x y * f y)
        = f y * ∫ x in (0 : ℝ)..L, gD b L y x * Real.sin (n * Real.pi * x / L) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [hθ, gD_symm b L y x]
      ring
    rw [this, gD_sine hb hL hy n]; ring
  rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_div]
  have e : (∫ y in (0 : ℝ)..L, f y * Real.sin (n * Real.pi * y / L))
      = ∫ y in (0 : ℝ)..L, Real.sin (n * Real.pi * y / L) * f y :=
    intervalIntegral.integral_congr (fun y _ => by ring)
  rw [e]

/-- **Spectral representation of the Green form.**
`∫₀ᴸ f · (G_D f) = (2/L) Σₙ cₙ(f)² / (b² + (nπ/L)²)`. -/
theorem green_form {b L : ℝ} (hb : 0 < b) (hL : 0 < L) {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    HasSum (fun n : ℕ => (2 / L) * ((rc L f n) ^ 2 / (b ^ 2 + (n * Real.pi / L) ^ 2)))
      (∫ x in (0 : ℝ)..L, f x * Gf b L f x) := by
  obtain ⟨C, hC⟩ := Gf_bound (b := b) hL.le hB
  have h := sine_parseval_pol hL hf (Gf_measurable hL.le hf) (B := max B C)
    (fun x => le_trans (hB x) (le_max_left _ _)) (fun x => le_trans (hC x) (le_max_right _ _))
  have hfun : (fun n : ℕ => (2 / L) * ((rc L f n) ^ 2 / (b ^ 2 + (n * Real.pi / L) ^ 2)))
      = fun n : ℕ => (2 / L) * (rc L f n * rc L (Gf b L f) n) := by
    funext n; rw [rc_Gf hb hL hf hB n]; ring
  rw [hfun]; exact h

/-- The `n`-th mode of the Green form. -/
noncomputable def mode (b L : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (2 / L) * ((rc L f n) ^ 2 / (b ^ 2 + (n * Real.pi / L) ^ 2))

/-- **Signed tail.** Splitting the Green form after the modes `0 … M`:
`∫ f·G_D f = Σ_{n ≤ M} modeₙ + tail_M`, with `0 ≤ tail_M ≤ ‖f‖²/(b² + ((M+1)π/L)²)`. -/
theorem green_tail {b L : ℝ} (hb : 0 < b) (hL : 0 < L) {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), mode b L f n) + ∑' i : ℕ, mode b L f (i + (M + 1))
        = ∫ x in (0 : ℝ)..L, f x * Gf b L f x ∧
      0 ≤ ∑' i : ℕ, mode b L f (i + (M + 1)) ∧
      ∑' i : ℕ, mode b L f (i + (M + 1))
        ≤ (∫ x in (0 : ℝ)..L, (f x) ^ 2) / (b ^ 2 + ((M + 1 : ℕ) * Real.pi / L) ^ 2) := by
  have hG := green_form hb hL hf hB
  have hP := sine_parseval_real hL hf hB
  have hGs : HasSum (mode b L f) (∫ x in (0 : ℝ)..L, f x * Gf b L f x) := hG
  set D : ℝ := b ^ 2 + ((M + 1 : ℕ) * Real.pi / L) ^ 2 with hD
  have hDpos : 0 < D := by positivity
  have hmode_nonneg : ∀ n, 0 ≤ mode b L f n := fun n => by unfold mode; positivity
  have hPn : ∀ n : ℕ, 0 ≤ (2 / L) * (rc L f n) ^ 2 := fun n => by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := hGs.summable.sum_add_tsum_nat_add (M + 1)
    rw [this]; exact hGs.tsum_eq
  · exact tsum_nonneg fun i => hmode_nonneg _
  · -- compare termwise with the Parseval tail
    have hPs := hP.summable
    have hle : ∀ i : ℕ, mode b L f (i + (M + 1)) ≤ ((2 / L) * (rc L f (i + (M + 1))) ^ 2) / D := by
      intro i
      unfold mode
      have hω : ((M + 1 : ℕ) : ℝ) ≤ ((i + (M + 1) : ℕ) : ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      have hD' : D ≤ b ^ 2 + (((i + (M + 1) : ℕ) : ℝ) * Real.pi / L) ^ 2 := by
        rw [hD]
        have : ((M + 1 : ℕ) : ℝ) * Real.pi / L ≤ ((i + (M + 1) : ℕ) : ℝ) * Real.pi / L := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact mul_le_mul_of_nonneg_right hω Real.pi_pos.le
        have h0 : 0 ≤ ((M + 1 : ℕ) : ℝ) * Real.pi / L := by positivity
        nlinarith
      have hpos : 0 < b ^ 2 + (((i + (M + 1) : ℕ) : ℝ) * Real.pi / L) ^ 2 := by positivity
      have h2L : 0 ≤ (2 / L) := by positivity
      calc 2 / L * (rc L f (i + (M + 1)) ^ 2 / (b ^ 2 + ((↑(i + (M + 1))) * Real.pi / L) ^ 2))
          = (2 / L * rc L f (i + (M + 1)) ^ 2) / (b ^ 2 + ((↑(i + (M + 1))) * Real.pi / L) ^ 2) := by ring
        _ ≤ (2 / L * rc L f (i + (M + 1)) ^ 2) / D :=
          div_le_div_of_nonneg_left (by positivity) hDpos hD'
    have hs1 : Summable fun i : ℕ => (2 / L * (rc L f (i + (M + 1))) ^ 2) / D :=
      ((summable_nat_add_iff (M + 1)).mpr hPs).div_const D
    calc ∑' i : ℕ, mode b L f (i + (M + 1))
        ≤ ∑' i : ℕ, (2 / L * (rc L f (i + (M + 1))) ^ 2) / D :=
          Summable.tsum_le_tsum hle ((summable_nat_add_iff (M + 1)).mpr hGs.summable) hs1
      _ = (∑' i : ℕ, (2 / L * (rc L f (i + (M + 1))) ^ 2)) / D := tsum_div_const
      _ ≤ (∫ x in (0 : ℝ)..L, (f x) ^ 2) / D := by
          apply div_le_div_of_nonneg_right _ hDpos.le
          have := hPs.sum_add_tsum_nat_add (M + 1)
          rw [hP.tsum_eq] at this
          have h0 : 0 ≤ ∑ i ∈ Finset.range (M + 1), 2 / L * rc L f i ^ 2 :=
            Finset.sum_nonneg fun i _ => hPn i
          linarith

end GppGreenForm

#print axioms GppGreenForm.rc_Gf
#print axioms GppGreenForm.green_form
#print axioms GppGreenForm.green_tail
