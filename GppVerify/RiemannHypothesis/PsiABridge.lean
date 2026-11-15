/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Grok / Heart of the Cosmos, GPPDiscovery5)
-/
import GppVerify.RiemannHypothesis.GlobalWeilPlaces
import GppVerify.RiemannHypothesis.RungZeroPositivity
import GppVerify.RiemannHypothesis.WindowBL036
import GppVerify.RiemannHypothesis.KreinBridge

/-!
# The `ψ_a` bridge: Toeplitz forms of a shifted-autocorrelation kernel are Weil forms

For a test function `ψ` (smooth, compact support) set

  `K_ψ(d) := W(τ_d (ψ ⋆ ψ̃))`,  `(τ_d A)(u) = A(u - d)`,

where `W = weilForm` is the tree's Weil form (pole + archimedean − primes) and `ψ ⋆ ψ̃ = autocorr ψ`.

* `kform_kernelA` (**bridge**): for every finite family of points `x` and real weights `c`,
  `kform K_ψ x c = W(autocorr (Σᵢ cᵢ ψ(· − xᵢ)))`.
* `kform_kernelA_nonneg_window` (**corollary of #597**): if `ψ` vanishes outside `[-a, a]` and
  `|xᵢ − xⱼ| ≤ L` for all `i, j`, with `L + 2a ≤ 18/25`, then `kform K_ψ x c ≥ 0`. No condition
  on `c` is needed. The input is `GppWindowBL036.weilForm_autocorr_nonneg_l036_unconditional`.

**Scope.** This is one base rung: the window of total width `0.72`, where the prime `2` is
visible and no other prime is. It says nothing about wider windows. The kernel here is built
from a smooth `ψ`; the triangle `triPsi` of `KreinHPsi` is only Lipschitz and is not covered.
Weil positivity for all test functions, H_ψ and RH stay OPEN.

Specification: Heart's PR #11 comment 6888342648, item 4(a); ordered first by Turbo's audit
6888364446. Daniel Toupin / Golden Physics Project, with AI assistance from Grok
(Heart of the Cosmos, GPPDiscovery5).
-/

namespace GppPsiABridge

open MeasureTheory GppArithmeticReflection GppWeilLadder GppMeyerSpectralWeil
open GppRungZeroPositivity GppAutocorrTransport GlobalTate.Weil GppKreinBridge

/-- The shifted-autocorrelation kernel `K_ψ(d) = W(u ↦ (ψ ⋆ ψ̃)(u − d))`. -/
noncomputable def kernelA (ψ : ℝ → ℝ) (d : ℝ) : ℝ :=
  weilForm (fun u => autocorr ψ (u - d))

/-- The finite translate combination `Σᵢ cᵢ ψ(· − xᵢ)`. -/
noncomputable def combo (ψ : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, c i * ψ (y - x i)

/-! ## The test class is closed under translation and finite linear combinations -/

theorem isTestFunction_comp_sub {g : ℝ → ℝ} (hg : IsTestFunction g) (d : ℝ) :
    IsTestFunction (fun u => g (u - d)) :=
  ⟨hg.1.comp (contDiff_id.sub contDiff_const), hg.2.comp_homeomorph (Homeomorph.subRight d)⟩

theorem isTestFunction_zero' : IsTestFunction (fun _ : ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

theorem isTestFunction_smul_add {g₁ g₂ : ℝ → ℝ} (a : ℝ) (h₁ : IsTestFunction g₁)
    (h₂ : IsTestFunction g₂) : IsTestFunction (a • g₁ + g₂) := by
  refine ⟨(h₁.1.const_smul a).add h₂.1, ?_⟩
  have hs : HasCompactSupport (a • g₁) := h₁.2.mono fun y hy => by
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hy ⊢
    exact right_ne_zero_of_mul hy
  exact hs.add h₂.2

/-! ## Test functions are Weil-admissible -/

theorem exists_hasSupportIn {g : ℝ → ℝ} (hc : HasCompactSupport g) : ∃ R, HasSupportIn g R := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun x hx => ?_⟩
  by_contra h
  have hx' := hR (subset_tsupport g h)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx'
  linarith

theorem summable_primeTerm {g : ℝ → ℝ} (hg : IsTestFunction g) : Summable (primeTerm g) := by
  obtain ⟨R, hR⟩ := exists_hasSupportIn hg.2
  apply summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp R⌉₊ + 1))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have h1 : Real.exp R < n := by
    have hc := Nat.le_ceil (Real.exp R)
    have h2 : ((⌈Real.exp R⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := (Real.exp_pos R).trans h1
  exact primeSide_term_eq_zero hR ((Real.lt_log_iff_exp_lt hn0).2 h1)

theorem weilAdmissible_of_isTestFunction {g : ℝ → ℝ} (hg : IsTestFunction g) :
    WeilAdmissible g where
  pole := (hg.1.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hg.2.mul_right
  arch := integrableOn_archimedeanIntegrand hg.1 hg.2
  prime := summable_primeTerm hg

/-- Finite linearity of `weilForm` on the test class, with closure of the class. -/
theorem weilForm_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ s, IsTestFunction (g i)) :
    IsTestFunction (fun u => ∑ i ∈ s, a i * g i u) ∧
      weilForm (fun u => ∑ i ∈ s, a i * g i u) = ∑ i ∈ s, a i * weilForm (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨isTestFunction_zero', ?_⟩
    have h0 := weilAdmissible_of_isTestFunction isTestFunction_zero'
    have h := weilForm_add_smul 1 h0 h0
    have e : ((1 : ℝ) • (fun _ : ℝ => (0 : ℝ)) + fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext u; simp
    rw [e] at h
    linarith
  | @insert j s hj ih =>
    obtain ⟨ht, hw⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hgj := hg j (Finset.mem_insert_self j s)
    have e : (fun u => ∑ i ∈ insert j s, a i * g i u) =
        a j • g j + fun u => ∑ i ∈ s, a i * g i u := by
      funext u; simp [Finset.sum_insert hj]
    rw [e, Finset.sum_insert hj]
    refine ⟨isTestFunction_smul_add (a j) hgj ht, ?_⟩
    rw [weilForm_add_smul (a j) (weilAdmissible_of_isTestFunction hgj)
      (weilAdmissible_of_isTestFunction ht), hw]

theorem isTestFunction_combo {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {n : ℕ} (x c : Fin n → ℝ) :
    IsTestFunction (combo ψ x c) :=
  (weilForm_finset_sum Finset.univ c (fun i y => ψ (y - x i))
    (fun i _ => isTestFunction_comp_sub hψ (x i))).1

/-! ## The autocorrelation of a translate combination -/

theorem integral_translate_pair (ψ : ℝ → ℝ) (a b u : ℝ) :
    ∫ y, ψ (y - a) * ψ (y - u - b) = autocorr ψ (u - (a - b)) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => ψ (y - a) * ψ (y - u - b)) a
  try dsimp only at h
  rw [← h]
  simp only [autocorr]
  congr 1
  funext z
  rw [show z + a - a = z by ring, show z + a - u - b = z - (u - (a - b)) by ring]

theorem autocorr_combo {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {n : ℕ} (x c : Fin n → ℝ) (u : ℝ) :
    autocorr (combo ψ x c) u = ∑ i, ∑ j, c i * c j * autocorr ψ (u - (x i - x j)) := by
  have hint : ∀ i j, Integrable (fun y => c i * c j * (ψ (y - x i) * ψ (y - u - x j))) := by
    intro i j
    refine (((integrable_mul_shift hψ.1 hψ.2 (u + x j - x i)).comp_sub_right (x i)).const_mul
      (c i * c j)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [show y - x i - (u + x j - x i) = y - u - x j by ring]
  calc autocorr (combo ψ x c) u
      = ∫ y, ∑ i, ∑ j, c i * c j * (ψ (y - x i) * ψ (y - u - x j)) := by
        simp only [autocorr, combo]
        congr 1
        funext y
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, ∫ y, c i * c j * (ψ (y - x i) * ψ (y - u - x j)) := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finset_sum _ (fun j _ => hint i j)]
    _ = ∑ i, ∑ j, c i * c j * autocorr ψ (u - (x i - x j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_translate_pair]

/-! ## The bridge -/

/-- **Bridge.** `kform K_ψ x c = W(autocorr (Σᵢ cᵢ ψ(· − xᵢ)))`. -/
theorem kform_kernelA {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {n : ℕ} (x c : Fin n → ℝ) :
    kform (kernelA ψ) x c = weilForm (autocorr (combo ψ x c)) := by
  have hA := isTestFunction_autocorr hψ
  have e : autocorr (combo ψ x c) =
      fun u => ∑ p : Fin n × Fin n, c p.1 * c p.2 * autocorr ψ (u - (x p.1 - x p.2)) := by
    funext u
    rw [autocorr_combo hψ x c u, Fintype.sum_prod_type]
  have key := weilForm_finset_sum Finset.univ (fun p : Fin n × Fin n => c p.1 * c p.2)
    (fun p u => autocorr ψ (u - (x p.1 - x p.2)))
    (fun p _ => isTestFunction_comp_sub hA (x p.1 - x p.2))
  rw [e, key.2, Fintype.sum_prod_type]
  rfl

/-- Translating every point leaves the Toeplitz form unchanged. -/
theorem kform_add_const (K : ℝ → ℝ) {n : ℕ} (x c : Fin n → ℝ) (t : ℝ) :
    kform K (fun i => x i + t) c = kform K x c := by
  simp only [kform, add_sub_add_right_eq_sub]

/-! ## The base rung from #597 -/

/-- Centered form of the base rung: points with `|xᵢ| + a ≤ 9/25`. -/
theorem kform_kernelA_nonneg_of_centered {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {a : ℝ}
    (hsa : HasSupportIn ψ a) {n : ℕ} (x c : Fin n → ℝ) (hx : ∀ i, |x i| + a ≤ 9 / 25) :
    0 ≤ kform (kernelA ψ) x c := by
  rw [kform_kernelA hψ]
  refine GppWindowBL036.weilForm_autocorr_nonneg_l036_unconditional (isTestFunction_combo hψ x c)
    fun y hy => ?_
  simp only [combo]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := hx i
  have h2 := abs_sub_abs_le_abs_sub y (x i)
  rw [hsa (y - x i) (by linarith), mul_zero]

/-- **Base rung (corollary of #597).** If `ψ` vanishes outside `[-a, a]`, the points lie in a
window of width `L`, and `L + 2a ≤ 18/25`, then `kform K_ψ x c ≥ 0`, with no condition on `c`. -/
theorem kform_kernelA_nonneg_window {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {a L : ℝ}
    (hsa : HasSupportIn ψ a) (hLa : L + 2 * a ≤ 18 / 25) {n : ℕ} (x c : Fin n → ℝ)
    (hx : ∀ i j, |x i - x j| ≤ L) : 0 ≤ kform (kernelA ψ) x c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [kform]
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ x hne
    obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ x hne
    rw [← kform_add_const _ x c (-(x i0 + x j0) / 2)]
    refine kform_kernelA_nonneg_of_centered hψ hsa _ c fun i => ?_
    have h1 := hi0 i (Finset.mem_univ _)
    have h2 := hj0 i (Finset.mem_univ _)
    have h3 := (le_abs_self _).trans (hx i0 j0)
    have h4 : |x i + -(x i0 + x j0) / 2| ≤ L / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith

/-- Non-vacuity: for every `a > 0` there is a test function `ψ_a`, vanishing outside `[-a, a]`,
with `ψ_a 0 = 1`. -/
theorem exists_psiA {a : ℝ} (ha : 0 < a) :
    ∃ ψ : ℝ → ℝ, IsTestFunction ψ ∧ HasSupportIn ψ a ∧ ψ 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨a / 2, a, by positivity, by linarith⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, fun x hx => ?_,
    b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)⟩
  apply b.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]
  exact hx.le

end GppPsiABridge

#print axioms GppPsiABridge.kform_kernelA
#print axioms GppPsiABridge.kform_kernelA_nonneg_window
#print axioms GppPsiABridge.exists_psiA
