/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import GppVerify.RiemannHypothesis.HeartRound23Elementary
import GppVerify.RiemannHypothesis.ZetaGibbsSummability
import GppVerify.Upstream.DigammaGaussSeries
import GppVerify.RiemannHypothesis.DigammaQuarterValue

/-!
# The Laplace identity for the box Weil form (Round 23 F11)

Notation (Round 23): `b_k = 2k + ½`, `T(L) = Σ_k e^{−b_k L}/b_k²`, `S = HR23_S`
(`S(L) = Σ_{n ≤ e^L} Λ(n) n^{−1/2} (L − log n)`), `c₁ = (ψ(¼) − log π)/2`, `C₂ = Σ_k 1/b_k² = ψ′(¼)/4`,
`D(L) = 4(e^{L/2} − 2 + e^{−L/2}) + c₁ L + C₂ − T(L) − S(L)`, `ξ(z) = ½ z (z − 1) Λ(z)` (`Λ` Mathlib's
completed zeta).

* `F11_laplace_identity`: for real `σ > ½`,
  `∫₀^∞ e^{−σL} D(L) dL = (ξ′/ξ)(½ + σ) / σ²`.
* `tendsto_Dfun_zero`, `Dfun_zero`: `D(0⁺) = 0`.
* `deriv_digamma_quarter`: `ψ′(¼) = 4 C₂`, i.e. `C₂ = ψ′(¼)/4` as in the filing.

Pieces: `laplace_T` (`Σ_k 1/(b_k²(σ + b_k))`), `laplace_S` (`σ⁻² Σ_n Λ(n) n^{−(σ+½)}`) with the
integrability of each weighted piece (`integrableOn_T`, `integrableOn_S`); the digamma side
(`digamma_diff_series`: `ψ(¼+σ/2) − ψ(¼) = Σ_k 2σ/(b_k(σ+b_k))`, `digamma_side`); the `ξ′/ξ` side
(`logDeriv_xiC`: `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ′/ζ(s)`, `zeta_logDeriv_eq`:
`ζ′/ζ(s) = −Σ Λ(n) n^{−s}`); the termwise algebra
`C₂ σ − σ² Σ_k 1/(b_k²(σ+b_k)) = Σ_k σ/(b_k(σ+b_k))` closes the identity.

Scope: real `σ > ½` only (`s = ½ + σ > 1`); the continuation to `Re σ > ½` is not part of this file.
No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartLaplace

open MeasureTheory Set ArithmeticFunction GppHeartRound23

/-- `b_k = 2k + ½`. -/
noncomputable def bk (k : ℕ) : ℝ := 2 * (k : ℝ) + 1 / 2

theorem bk_pos (k : ℕ) : 0 < bk k := by unfold bk; positivity

/-- `T(L) = Σ_k e^{−b_k L} / b_k²`. -/
noncomputable def Tfun (L : ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(bk k * L)) / bk k ^ 2

theorem summable_inv_bk_sq : Summable (fun k : ℕ => 1 / bk k ^ 2) := by
  have h4 : Summable (fun k : ℕ => 4 * (1 / (((k + 1 : ℕ) : ℝ)) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this.mul_left 4
  refine Summable.of_nonneg_of_le (fun k => by have := bk_pos k; positivity) (fun k => ?_) h4
  have hb := bk_pos k
  have hk : ((k + 1 : ℕ) : ℝ) / 2 ≤ bk k := by unfold bk; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have e : 4 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) * bk k ^ 2 = 4 * bk k ^ 2 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    ring
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith


/-- `∫₀^∞ e^{−cL} dL = 1/c` for `c > 0`. -/
theorem integral_exp_neg_Ioi_zero' {c : ℝ} (hc : 0 < c) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-c * L) = 1 / c := by
  rw [integral_exp_mul_Ioi (by linarith : -c < 0) 0]
  simp

/-- Laplace transform of `T`: `∫₀^∞ e^{−σL} T(L) dL = Σ_k 1 / (b_k² (σ + b_k))`. -/
theorem laplace_T {σ : ℝ} (hσ : 0 < σ) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * Tfun L
      = ∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k)) := by
  set F : ℕ → ℝ → ℝ := fun k L => Real.exp (-σ * L) * (Real.exp (-(bk k * L)) / bk k ^ 2) with hF
  have hFeq : ∀ k L, F k L = (1 / bk k ^ 2) * Real.exp (-(σ + bk k) * L) := by
    intro k L
    simp only [hF]
    rw [show -(σ + bk k) * L = -σ * L + -(bk k * L) by ring, Real.exp_add]
    ring
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := by
    intro k
    have h : IntegrableOn (fun L : ℝ => (1 / bk k ^ 2) * Real.exp (-(σ + bk k) * L)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith [bk_pos k] : 0 < σ + bk k)).const_mul
        (1 / bk k ^ 2)
    exact h.congr_fun (fun L _ => (hFeq k L).symm) measurableSet_Ioi
  have hval : ∀ k, ∫ L in Ioi (0 : ℝ), F k L = 1 / (bk k ^ 2 * (σ + bk k)) := by
    intro k
    simp_rw [hFeq k]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero' (by linarith [bk_pos k])]
    have := bk_pos k
    field_simp
  have hnorm : ∀ k, ∫ L in Ioi (0 : ℝ), ‖F k L‖ = 1 / (bk k ^ 2 * (σ + bk k)) := by
    intro k
    rw [← hval k]
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    simp only [hFeq]
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := bk_pos k; positivity)]
  have hsum : Summable (fun k : ℕ => ∫ L in Ioi (0 : ℝ), ‖F k L‖) := by
    simp_rw [hnorm]
    refine Summable.of_nonneg_of_le (fun k => by have := bk_pos k; positivity) (fun k => ?_)
      (summable_inv_bk_sq.mul_left (1 / σ))
    have := bk_pos k
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / σ * (1 / bk k ^ 2) * (bk k ^ 2 * (σ + bk k)) = (σ + bk k) / σ := by
      field_simp
    rw [e, le_div_iff₀ hσ]
    linarith
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hrhs : ∀ L : ℝ, Real.exp (-σ * L) * Tfun L = ∑' k, F k L := by
    intro L
    unfold Tfun
    rw [← tsum_mul_left]
  simp_rw [hrhs]
  rw [← h]
  exact tsum_congr hval


/-! ### The prime-power sum `S` -/

/-- Coefficients `Λ(n)/√n`. -/
noncomputable def aN (n : ℕ) : ℝ := (vonMangoldt n) / Real.sqrt n

theorem aN_nonneg (n : ℕ) : 0 ≤ aN n := by
  unfold aN; have := vonMangoldt_nonneg (n := n); positivity

theorem S_eq_tsum (L : ℝ) : HR23_S L = ∑' n : ℕ, aN n * max (L - Real.log n) 0 := by
  unfold HR23_S
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp L⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hle : (n : ℝ) ≤ Real.exp L :=
      (Nat.le_floor_iff (Real.exp_pos L).le).mp hn.2 |> fun h => by exact_mod_cast h
    have : Real.log n ≤ L := by
      rw [Real.log_le_iff_le_exp hn0]; exact hle
    rw [max_eq_left (by linarith)]
    rfl
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with h | h
    · have : n = 0 := by omega
      subst this
      simp [aN]
    · have hn' : Real.exp L < n := by
        exact (Nat.floor_lt (Real.exp_pos L).le).mp (not_le.mp h)
      have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos L) hn'
      have : L < Real.log n := by rw [Real.lt_log_iff_exp_lt hn0]; exact hn'
      rw [max_eq_right (by linarith)]
      simp


theorem integrable_pos_part {σ a : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * max (L - a) 0) (Ioi 0) := by
  have hint : IntegrableOn (fun L : ℝ => (2 / σ) * Real.exp (-(σ / 2) * L)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : 0 < σ / 2)).const_mul (2 / σ)
  have hcont : Continuous (fun L : ℝ => Real.exp (-σ * L) * max (L - a) 0) := by fun_prop
  refine hint.mono' hcont.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun L hL => ?_
  have hL0 : 0 < L := hL
  have h1 : max (L - a) 0 ≤ L := max_le (by linarith) hL0.le
  have h2 : L ≤ (2 / σ) * Real.exp (σ / 2 * L) := by
    have h := Real.add_one_le_exp (σ / 2 * L)
    have e : (2 / σ) * Real.exp (σ / 2 * L) = (2 * Real.exp (σ / 2 * L)) / σ := by ring
    rw [e, le_div_iff₀ hσ]
    nlinarith [h]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (-σ * L) * max (L - a) 0 ≤ Real.exp (-σ * L) * L :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (-σ * L) * ((2 / σ) * Real.exp (σ / 2 * L)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (2 / σ) * Real.exp (-(σ / 2) * L) := by
        rw [← mul_assoc, mul_comm (Real.exp (-σ * L)), mul_assoc, ← Real.exp_add]
        congr 2; ring


theorem summable_vonMangoldt_rpow {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ β) := by
  have hs := GppZetaGibbsSummability.summable_gibbsWeight_mul_logEnergy hβ
  have hN : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ β) := by
    rw [← summable_nat_add_iff 1]
    refine hs.congr fun n => ?_
    simp only [GppZetaGibbsSummability.gibbsWeight, GppZetaGibbsSummability.logEnergy]
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hN
  · have := vonMangoldt_nonneg (n := n); positivity
  · by_cases hn : n = 0
    · subst hn; simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact vonMangoldt_le_log

theorem aN_mul_exp {σ : ℝ} (n : ℕ) :
    aN n * Real.exp (-σ * Real.log n) = vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) := by
  by_cases hn : n = 0
  · subst hn; simp [aN]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold aN
    rw [Real.sqrt_eq_rpow, Real.rpow_add hn0, show -σ * Real.log n = Real.log n * (-σ) by ring,
      ← Real.rpow_def_of_pos hn0, Real.rpow_neg hn0.le]
    field_simp

/-- Laplace transform of `S`: `∫₀^∞ e^{−σL} S(L) dL = σ⁻² Σ_n Λ(n) n^{−(σ + ½)}` for `σ > ½`. -/
theorem laplace_S {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * HR23_S L
      = (1 / σ ^ 2) * ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) := by
  have hσ0 : 0 < σ := by linarith
  set F : ℕ → ℝ → ℝ := fun n L => Real.exp (-σ * L) * (aN n * max (L - Real.log n) 0) with hF
  have hloga : ∀ n : ℕ, 0 ≤ Real.log n := fun n => Real.log_natCast_nonneg n
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have h : IntegrableOn (fun L : ℝ => aN n * (Real.exp (-σ * L) * max (L - Real.log n) 0))
        (Ioi 0) := (integrable_pos_part hσ0 (hloga n)).const_mul (aN n)
    exact h.congr_fun (fun L _ => by simp only [hF]; ring) measurableSet_Ioi
  have hval : ∀ n, ∫ L in Ioi (0 : ℝ), F n L = (1 / σ ^ 2) * (vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2)) := by
    intro n
    have h1 : ∀ L, F n L = aN n * (Real.exp (-σ * L) * max (L - Real.log n) 0) := by
      intro L; simp only [hF]; ring
    simp_rw [h1]
    rw [integral_const_mul, HR23_F5b_laplace_positive_part hσ0 (hloga n), ← aN_mul_exp (σ := σ) n]
    ring
  have hnorm : ∀ n, ∫ L in Ioi (0 : ℝ), ‖F n L‖ = (1 / σ ^ 2) * (vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2)) := by
    intro n
    rw [← hval n]
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    simp only [hF]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have := aN_nonneg n
    positivity
  have hsum : Summable (fun n : ℕ => ∫ L in Ioi (0 : ℝ), ‖F n L‖) := by
    simp_rw [hnorm]
    exact (summable_vonMangoldt_rpow (by linarith : 1 < σ + 1 / 2)).mul_left _
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hrhs : ∀ L : ℝ, Real.exp (-σ * L) * HR23_S L = ∑' n, F n L := by
    intro L
    rw [S_eq_tsum, ← tsum_mul_left]
  simp_rw [hrhs]
  rw [← h, tsum_congr hval, tsum_mul_left]


/-! ### The digamma side -/

private theorem ne_neg_nat_pos {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- Termwise Gauss series difference: for `σ > 0`,
`ψ(¼ + σ/2) − ψ(¼) = Σ_k 2σ / (b_k (σ + b_k))`. -/
theorem digamma_diff_series {σ : ℝ} (hσ : 0 < σ) :
    Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ) - Complex.digamma (((1 / 4 : ℝ)) : ℂ)
      = ((∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ) := by
  have ha : (0 : ℝ) < 1 / 4 := by norm_num
  have hz : (0 : ℝ) < 1 / 4 + σ / 2 := by positivity
  set a : ℂ := ((1 / 4 : ℝ) : ℂ) with ha_def
  set z : ℂ := ((1 / 4 + σ / 2 : ℝ) : ℂ) with hz_def
  have hsa := Complex.hasSum_digamma (ne_neg_nat_pos ha)
  have hsz := Complex.hasSum_digamma (ne_neg_nat_pos hz)
  have h1 : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1 + a) - 1 / ((n : ℂ) + 1 + z))
      ((Complex.digamma z + Real.eulerMascheroniConstant + 1 / z)
        - (Complex.digamma a + Real.eulerMascheroniConstant + 1 / a)) := by
    have hfun : (fun n : ℕ => (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + z))
        - (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + a)))
        = fun n : ℕ => 1 / ((n : ℂ) + 1 + a) - 1 / ((n : ℂ) + 1 + z) := funext fun n => by ring
    rw [← hfun]
    exact hsz.sub hsa
  set f : ℕ → ℂ := fun k => 1 / ((k : ℂ) + a) - 1 / ((k : ℂ) + z) with hf
  have h1' : HasSum (fun n : ℕ => f (n + 1))
      ((Complex.digamma z + Real.eulerMascheroniConstant + 1 / z)
        - (Complex.digamma a + Real.eulerMascheroniConstant + 1 / a)) := by
    convert h1 using 1
    funext n
    simp only [hf]
    push_cast
    rfl
  have h2 := (hasSum_nat_add_iff 1).mp h1'
  simp only [Finset.sum_range_one] at h2
  have ha0 : a ≠ 0 := by rw [ha_def]; exact_mod_cast ha.ne'
  have hz0 : z ≠ 0 := by rw [hz_def]; exact_mod_cast hz.ne'
  -- identify `f k` with the real expression
  have hfk : ∀ k : ℕ, f k = ((2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ) := by
    intro k
    have hb := bk_pos k
    have e1 : (k : ℂ) + a = ((bk k / 2 : ℝ) : ℂ) := by
      simp only [ha_def, bk]; push_cast; ring
    have e2 : (k : ℂ) + z = (((bk k + σ) / 2 : ℝ) : ℂ) := by
      simp only [hz_def, bk]; push_cast; ring
    simp only [hf]
    rw [e1, e2]
    have hb' : (bk k : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbs : ((bk k + σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : bk k + σ ≠ 0)
    have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have hs' : (σ : ℂ) + (bk k : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ + bk k ≠ 0)
    push_cast at hbs ⊢
    field_simp
    ring
  have hval : ((Complex.digamma z + Real.eulerMascheroniConstant + 1 / z)
        - (Complex.digamma a + Real.eulerMascheroniConstant + 1 / a)) + f 0
      = Complex.digamma z - Complex.digamma a := by
    simp only [hf, Nat.cast_zero, zero_add]
    ring
  rw [hval] at h2
  have h3 : HasSum (fun k : ℕ => ((2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ))
      (Complex.digamma z - Complex.digamma a) := by
    have : (fun k : ℕ => ((2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ)) = f :=
      funext fun k => (hfk k).symm
    rw [this]
    exact h2
  rw [← h3.tsum_eq, Complex.ofReal_tsum]


theorem summable_inv_bk_sq_mul {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun k : ℕ => 1 / (bk k ^ 2 * (σ + bk k))) := by
  refine Summable.of_nonneg_of_le (fun k => by have := bk_pos k; positivity) (fun k => ?_)
    (summable_inv_bk_sq.mul_left (1 / σ))
  have := bk_pos k
  rw [div_le_iff₀ (by positivity)]
  have e : 1 / σ * (1 / bk k ^ 2) * (bk k ^ 2 * (σ + bk k)) = (σ + bk k) / σ := by
    field_simp
  rw [e, le_div_iff₀ hσ]
  linarith

/-- `σ C₂ − σ² Σ_k 1/(b_k²(σ+b_k)) = Σ_k σ/(b_k(σ+b_k))` with `C₂ = Σ_k 1/b_k²`. -/
theorem C2_sigma_identity {σ : ℝ} (hσ : 0 < σ) :
    σ * (∑' k : ℕ, 1 / bk k ^ 2) - σ ^ 2 * ∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k))
      = ∑' k : ℕ, σ / (bk k * (σ + bk k)) := by
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub
    (summable_inv_bk_sq.mul_left σ) ((summable_inv_bk_sq_mul hσ).mul_left (σ ^ 2))]
  refine tsum_congr fun k => ?_
  have hb := bk_pos k
  have hs : σ + bk k ≠ 0 := by linarith
  field_simp
  ring

/-- **Digamma side of F11.** For `σ > 0`, with `c₁ = (Re ψ(¼) − log π)/2` and `C₂ = Σ_k 1/b_k²`:
`c₁ + C₂ σ − σ² Σ_k 1/(b_k²(σ+b_k)) = −½ log π + ½ Re ψ(¼ + σ/2)`. -/
theorem digamma_side {σ : ℝ} (hσ : 0 < σ) :
    ((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re - Real.log Real.pi) / 2
      + σ * (∑' k : ℕ, 1 / bk k ^ 2) - σ ^ 2 * ∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k))
      = -(1 / 2) * Real.log Real.pi + (1 / 2) * (Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ)).re := by
  have h := digamma_diff_series hσ
  have hre := congrArg Complex.re h
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have hsum : ∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) = 2 * ∑' k : ℕ, σ / (bk k * (σ + bk k)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    ring
  rw [hsum] at hre
  have hid := C2_sigma_identity hσ
  linarith


/-! ### The `ξ′/ξ` side -/

/-- Riemann's `ξ(z) = ½ z (z − 1) Λ(z)` with `Λ` Mathlib's completed zeta. -/
noncomputable def xiC (z : ℂ) : ℂ := (1 / 2) * z * (z - 1) * completedRiemannZeta z

theorem logDeriv_Gammaℝ {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ s = -(1 / 2) * Complex.log (Real.pi : ℂ) + (1 / 2) * Complex.digamma (s / 2) := by
  have hfun : Complex.Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; exact Complex.Gammaℝ_def z
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hd1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have h0 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
      have := ((hasDerivAt_id s).neg).div_const 2
      simpa using this
    exact h0.const_cpow (Or.inl hpi)
  have hd2 : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    have h0 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact (Complex.differentiableAt_Gamma _ hs).hasDerivAt.comp s h0
  have hg1 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]; exact Complex.exp_ne_zero _
  have hg2 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have hm : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2) * Complex.Gamma (s / 2)
        + (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2) * (1 / 2))) s := hd1.mul hd2
  rw [hfun, logDeriv_apply, hm.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp


theorem logDeriv_xiC {s : ℝ} (hs : 1 < s) :
    logDeriv xiC (s : ℂ) = 1 / (s : ℂ) + 1 / ((s : ℂ) - 1)
      - (1 / 2) * ((Real.log Real.pi : ℝ) : ℂ) + (1 / 2) * Complex.digamma ((s : ℂ) / 2)
      + deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) := by
  set z : ℂ := (s : ℂ) with hz
  have hs0 : (0 : ℝ) < s := by linarith
  have hz0 : z ≠ 0 := by rw [hz]; exact_mod_cast hs0.ne'
  have hz1 : z ≠ 1 := by rw [hz]; exact_mod_cast hs.ne'
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hre : 0 < z.re := by simpa [hz] using hs0
  have hre1 : 1 < z.re := by simpa [hz] using hs
  have hGam : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hzeta : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1.le
  have hΛeq : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hz0]; field_simp
  have hΛ0 : completedRiemannZeta z ≠ 0 := by rw [hΛeq]; exact mul_ne_zero hGam hzeta
  have hΛd : HasDerivAt completedRiemannZeta (deriv completedRiemannZeta z) z :=
    (differentiableAt_completedZeta hz0 hz1).hasDerivAt
  -- Λ agrees with Γℝ · ζ near z
  have hev : completedRiemannZeta =ᶠ[nhds z] fun w => Complex.Gammaℝ w * riemannZeta w := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw
    have hwG : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
    rw [riemannZeta_def_of_ne_zero hw0]; field_simp
  have hGd : HasDerivAt Complex.Gammaℝ
      (Complex.Gammaℝ z * logDeriv Complex.Gammaℝ z) z := by
    have hdiff : DifferentiableAt ℂ Complex.Gammaℝ z := by
      have hfun : Complex.Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
        funext w; exact Complex.Gammaℝ_def w
      rw [hfun]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z := by
        have h0 : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) z := by
          simpa using ((hasDerivAt_id z).neg).div_const 2
        exact (h0.const_cpow (Or.inl hpi)).differentiableAt
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
        have hsm : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := fun m => by
          intro h
          have := congrArg Complex.re h
          simp at this
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        exact (Complex.differentiableAt_Gamma _ hsm).comp z (by fun_prop)
      exact h1.mul h2
    have := hdiff.hasDerivAt
    rw [logDeriv_apply, mul_div_cancel₀ _ hGam]
    exact this
  have hζd : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
    (differentiableAt_riemannZeta hz1).hasDerivAt
  have hΛ' : deriv completedRiemannZeta z
      = Complex.Gammaℝ z * logDeriv Complex.Gammaℝ z * riemannZeta z
        + Complex.Gammaℝ z * deriv riemannZeta z := by
    rw [hev.deriv_eq]
    exact (hGd.mul hζd).deriv
  -- the logarithmic derivative of ξ
  have hxi : HasDerivAt xiC
      ((1 / 2) * (z * (z - 1) * deriv completedRiemannZeta z + (2 * z - 1) * completedRiemannZeta z)) z := by
    have h1 : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1)) ((1 / 2) * (2 * z - 1)) z :=
      ((((hasDerivAt_id z).const_mul (1 / 2 : ℂ)).mul ((hasDerivAt_id z).sub_const 1))).congr_deriv
        (by simp; ring)
    have hx : xiC = fun w : ℂ => ((1 / 2 : ℂ) * w * (w - 1)) * completedRiemannZeta w := rfl
    rw [hx]
    exact (h1.mul hΛd).congr_deriv (by ring)
  have hxi0 : xiC z ≠ 0 := by
    unfold xiC
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz0) hz1') hΛ0
  have hlogG := logDeriv_Gammaℝ (s := z) (fun m => by
    intro h
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  rw [logDeriv_apply, hxi.deriv]
  unfold xiC
  rw [hΛ', hΛeq]
  have hlogG' : logDeriv Complex.Gammaℝ z = -(1 / 2) * ((Real.log Real.pi : ℝ) : ℂ)
      + (1 / 2) * Complex.digamma (z / 2) := by
    rw [hlogG, Complex.ofReal_log Real.pi_pos.le]
  rw [hlogG']
  field_simp
  ring


/-! ### Integrability of the series pieces -/

/-- Integrability of a nonnegative series `Σ_i F_i` from summability of the integrals. -/
theorem integrableOn_tsum_nonneg {F : ℕ → ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hint : ∀ i, IntegrableOn (F i) s) (hnn : ∀ i x, 0 ≤ F i x)
    (hsum : Summable fun i => ∫ x in s, F i x)
    (hpt : ∀ x ∈ s, Summable fun i => F i x)
    (hmeas : AEStronglyMeasurable (fun x => ∑' i, F i x) (volume.restrict s)) :
    IntegrableOn (fun x => ∑' i, F i x) s := by
  have hnn' : ∀ x, 0 ≤ ∑' i, F i x := fun x => tsum_nonneg fun i => hnn i x
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn')]
  have h1 : ∀ᵐ x ∂(volume.restrict s), ENNReal.ofReal (∑' i, F i x) = ∑' i, ENNReal.ofReal (F i x) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => hnn i x) (hpt x hx)
  have hlt : ∫⁻ x, ∑' i, ENNReal.ofReal (F i x) ∂(volume.restrict s)
      = ∑' i, ∫⁻ x, ENNReal.ofReal (F i x) ∂(volume.restrict s) :=
    lintegral_tsum (f := fun i x => ENNReal.ofReal (F i x)) (fun i =>
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hint i).1.aemeasurable))
  rw [lintegral_congr_ae h1, hlt]
  have h2 : ∀ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂(volume.restrict s) = ENNReal.ofReal (∫ x in s, F i x) := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (hnn i))]
  simp_rw [h2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun x => hnn i x) hsum]
  exact ENNReal.ofReal_lt_top


/-- Integrability of `e^{−σL} T(L)` on `(0, ∞)`. -/
theorem integrableOn_T {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * Tfun L) (Ioi 0) := by
  set F : ℕ → ℝ → ℝ := fun k L => Real.exp (-σ * L) * (Real.exp (-(bk k * L)) / bk k ^ 2) with hF
  have hFeq : ∀ k L, F k L = (1 / bk k ^ 2) * Real.exp (-(σ + bk k) * L) := by
    intro k L
    simp only [hF]
    rw [show -(σ + bk k) * L = -σ * L + -(bk k * L) by ring, Real.exp_add]
    ring
  have hint : ∀ k, IntegrableOn (F k) (Ioi 0) := by
    intro k
    have h : IntegrableOn (fun L : ℝ => (1 / bk k ^ 2) * Real.exp (-(σ + bk k) * L)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith [bk_pos k] : 0 < σ + bk k)).const_mul (1 / bk k ^ 2)
    exact h.congr_fun (fun L _ => (hFeq k L).symm) measurableSet_Ioi
  have hnn : ∀ k L, 0 ≤ F k L := fun k L => by have := bk_pos k; simp only [hF]; positivity
  have hval : ∀ k, ∫ L in Ioi (0 : ℝ), F k L = 1 / (bk k ^ 2 * (σ + bk k)) := by
    intro k
    simp_rw [hFeq k]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero' (by linarith [bk_pos k])]
    have := bk_pos k
    field_simp
  have hsum : Summable fun k => ∫ L in Ioi (0 : ℝ), F k L := by
    simp_rw [hval]; exact summable_inv_bk_sq_mul hσ
  have hbound : ∀ k, ∀ L ∈ Ioi (0 : ℝ), ‖F k L‖ ≤ 1 / bk k ^ 2 := by
    intro k L hL
    have hL0 : 0 < L := hL
    have hb := bk_pos k
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn k L)]
    simp only [hF]
    have h1 : Real.exp (-σ * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : Real.exp (-(bk k * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h3 : Real.exp (-(bk k * L)) / bk k ^ 2 ≤ 1 / bk k ^ 2 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    calc Real.exp (-σ * L) * (Real.exp (-(bk k * L)) / bk k ^ 2)
        ≤ 1 * (1 / bk k ^ 2) :=
          mul_le_mul h1 h3 (by positivity) zero_le_one
      _ = 1 / bk k ^ 2 := one_mul _
  have hpt : ∀ L ∈ Ioi (0 : ℝ), Summable fun k => F k L := fun L hL =>
    Summable.of_norm_bounded summable_inv_bk_sq (fun k => hbound k L hL)
  have hcont : ContinuousOn (fun L : ℝ => ∑' k, F k L) (Ioi 0) :=
    continuousOn_tsum (fun k => by simp only [hF]; fun_prop) summable_inv_bk_sq hbound
  have := integrableOn_tsum_nonneg measurableSet_Ioi hint hnn hsum hpt
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  refine this.congr_fun (fun L _ => ?_) measurableSet_Ioi
  unfold Tfun
  simp only [hF]
  rw [tsum_mul_left]


/-- Integrability of `e^{−σL} S(L)` on `(0, ∞)`, `σ > ½`. -/
theorem integrableOn_S {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * HR23_S L) (Ioi 0) := by
  have hσ0 : 0 < σ := by linarith
  set F : ℕ → ℝ → ℝ := fun n L => Real.exp (-σ * L) * (aN n * max (L - Real.log n) 0) with hF
  have hloga : ∀ n : ℕ, 0 ≤ Real.log n := fun n => Real.log_natCast_nonneg n
  have hint : ∀ n, IntegrableOn (F n) (Ioi 0) := by
    intro n
    have h : IntegrableOn (fun L : ℝ => aN n * (Real.exp (-σ * L) * max (L - Real.log n) 0))
        (Ioi 0) := (integrable_pos_part hσ0 (hloga n)).const_mul (aN n)
    exact h.congr_fun (fun L _ => by simp only [hF]; ring) measurableSet_Ioi
  have hnn : ∀ n L, 0 ≤ F n L := fun n L => by
    have := aN_nonneg n
    simp only [hF]; positivity
  have hval : ∀ n, ∫ L in Ioi (0 : ℝ), F n L = (1 / σ ^ 2) * (vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2)) := by
    intro n
    have h1 : ∀ L, F n L = aN n * (Real.exp (-σ * L) * max (L - Real.log n) 0) := by
      intro L; simp only [hF]; ring
    simp_rw [h1]
    rw [integral_const_mul, HR23_F5b_laplace_positive_part hσ0 (hloga n), ← aN_mul_exp (σ := σ) n]
    ring
  have hsum : Summable fun n => ∫ L in Ioi (0 : ℝ), F n L := by
    simp_rw [hval]
    exact (summable_vonMangoldt_rpow (by linarith : 1 < σ + 1 / 2)).mul_left _
  have hpt : ∀ L ∈ Ioi (0 : ℝ), Summable fun n => F n L := by
    intro L _
    refine summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp L⌋₊ + 1)) fun n hn => ?_
    have hn1 : ⌊Real.exp L⌋₊ + 1 ≤ n := by
      rw [Finset.mem_range, not_lt] at hn; exact hn
    have hn0 : 0 < n := by omega
    have hnR : Real.exp L < n := by
      have := Nat.lt_floor_add_one (Real.exp L)
      have h2 : ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast at h2
      linarith
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have : L < Real.log n := by rw [Real.lt_log_iff_exp_lt hn0R]; exact hnR
    simp only [hF]
    rw [max_eq_right (by linarith)]
    simp
  have hfun : (fun L : ℝ => ∑' n, F n L) = fun L => Real.exp (-σ * L) * HR23_S L := by
    funext L
    simp only [hF]
    rw [S_eq_tsum, ← tsum_mul_left]
  have hcont : Continuous (fun L : ℝ => Real.exp (-σ * L) * HR23_S L) :=
    (by fun_prop : Continuous fun L : ℝ => Real.exp (-σ * L)).mul HR23_S_continuous
  have := integrableOn_tsum_nonneg measurableSet_Ioi hint hnn hsum hpt
    (by rw [hfun]; exact hcont.aestronglyMeasurable)
  rw [hfun] at this
  exact this


/-! ### The assembled Laplace transform of `D` -/

/-- `c₁ = (Re ψ(¼) − log π)/2`. -/
noncomputable def c1 : ℝ := ((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re - Real.log Real.pi) / 2

/-- `C₂ = Σ_k 1/b_k²` (`= ψ′(¼)/4`). -/
noncomputable def C2 : ℝ := ∑' k : ℕ, 1 / bk k ^ 2

/-- Round 23's `D(L) = 4(e^{L/2} − 2 + e^{−L/2}) + c₁ L + C₂ − T(L) − S(L)`. -/
noncomputable def Dfun (L : ℝ) : ℝ :=
  4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)) + c1 * L + C2 - Tfun L - HR23_S L

theorem integrableOn_arch {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2))))
      (Ioi 0) := by
  have hfun : ∀ L : ℝ, Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)))
      = 4 * Real.exp (-(σ - 1 / 2) * L) - 8 * Real.exp (-σ * L)
        + 4 * Real.exp (-(σ + 1 / 2) * L) := by
    intro L
    have e1 : Real.exp (-σ * L) * Real.exp (L / 2) = Real.exp (-(σ - 1 / 2) * L) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-σ * L) * Real.exp (-L / 2) = Real.exp (-(σ + 1 / 2) * L) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)))
        = 4 * (Real.exp (-σ * L) * Real.exp (L / 2)) - 8 * Real.exp (-σ * L)
          + 4 * (Real.exp (-σ * L) * Real.exp (-L / 2)) := by ring
      _ = _ := by rw [e1, e2]
  have h1 := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ - 1 / 2)).const_mul 4
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ)).const_mul 8
  have h3 := (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < σ + 1 / 2)).const_mul 4
  have h : IntegrableOn (fun L : ℝ => 4 * Real.exp (-(σ - 1 / 2) * L) - 8 * Real.exp (-σ * L)
        + 4 * Real.exp (-(σ + 1 / 2) * L)) (Ioi 0) := (h1.sub h2).add h3
  exact h.congr_fun (fun L _ => (hfun L).symm) measurableSet_Ioi

theorem integrableOn_linear {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun L : ℝ => Real.exp (-σ * L) * L) (Ioi 0) := by
  have h := integrable_pos_part hσ (le_refl (0 : ℝ))
  refine h.congr_fun (fun L hL => ?_) measurableSet_Ioi
  have hL0 : 0 < L := hL
  simp [max_eq_left hL0.le]

theorem integral_linear {σ : ℝ} (hσ : 0 < σ) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * L = 1 / σ ^ 2 := by
  have h := HR23_F5b_laplace_positive_part hσ (le_refl (0 : ℝ))
  simp only [mul_zero, Real.exp_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
  have hL0 : 0 < L := hL
  simp [max_eq_left hL0.le]


/-- **Laplace transform of `D`** (real `σ > ½`), in series form. -/
theorem laplace_D {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * Dfun L
      = 2 / (σ * (σ ^ 2 - 1 / 4)) + c1 / σ ^ 2 + C2 / σ
        - (∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k)))
        - (1 / σ ^ 2) * ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) := by
  have hσ0 : 0 < σ := by linarith
  have hA := integrableOn_arch hσ
  have hLin := (integrableOn_linear hσ0).const_mul c1
  have hE := (exp_neg_integrableOn_Ioi 0 hσ0).const_mul C2
  have hT := integrableOn_T hσ0
  have hS := integrableOn_S hσ
  have hexpand : ∀ L : ℝ, Real.exp (-σ * L) * Dfun L
      = ((Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)))
          + c1 * (Real.exp (-σ * L) * L)) + C2 * Real.exp (-σ * L))
        - Real.exp (-σ * L) * Tfun L - Real.exp (-σ * L) * HR23_S L := by
    intro L; unfold Dfun; ring
  set a : ℝ → ℝ := fun L => Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2))) with ha
  set b : ℝ → ℝ := fun L => c1 * (Real.exp (-σ * L) * L) with hb
  set c : ℝ → ℝ := fun L => C2 * Real.exp (-σ * L) with hc
  set t : ℝ → ℝ := fun L => Real.exp (-σ * L) * Tfun L with ht
  set u : ℝ → ℝ := fun L => Real.exp (-σ * L) * HR23_S L with hu
  have hint_ab : IntegrableOn (fun L => a L + b L) (Ioi 0) := hA.add hLin
  have hint_abc : IntegrableOn (fun L => a L + b L + c L) (Ioi 0) := hint_ab.add hE
  have hint_abct : IntegrableOn (fun L => a L + b L + c L - t L) (Ioi 0) := hint_abc.sub hT
  have e : (fun L : ℝ => Real.exp (-σ * L) * Dfun L) = fun L => a L + b L + c L - t L - u L := by
    funext L; simp only [ha, hb, hc, ht, hu]; exact hexpand L
  rw [e]
  have i1 : ∫ L in Ioi (0 : ℝ), (a L + b L + c L - t L - u L)
      = (∫ L in Ioi (0 : ℝ), (a L + b L + c L - t L)) - ∫ L in Ioi (0 : ℝ), u L :=
    integral_sub hint_abct hS
  have i2 : ∫ L in Ioi (0 : ℝ), (a L + b L + c L - t L)
      = (∫ L in Ioi (0 : ℝ), (a L + b L + c L)) - ∫ L in Ioi (0 : ℝ), t L :=
    integral_sub hint_abc hT
  have i3 : ∫ L in Ioi (0 : ℝ), (a L + b L + c L)
      = (∫ L in Ioi (0 : ℝ), (a L + b L)) + ∫ L in Ioi (0 : ℝ), c L := integral_add hint_ab hE
  have i4 : ∫ L in Ioi (0 : ℝ), (a L + b L)
      = (∫ L in Ioi (0 : ℝ), a L) + ∫ L in Ioi (0 : ℝ), b L := integral_add hA hLin
  have iA : ∫ L in Ioi (0 : ℝ), a L = 2 / (σ * (σ ^ 2 - 1 / 4)) := HR23_F5a_laplace_arch hσ
  have iB : ∫ L in Ioi (0 : ℝ), b L = c1 / σ ^ 2 := by
    simp only [hb]; rw [integral_const_mul, integral_linear hσ0]; ring
  have iC : ∫ L in Ioi (0 : ℝ), c L = C2 / σ := by
    simp only [hc]; rw [integral_const_mul, integral_exp_neg_Ioi_zero' hσ0]; ring
  have iT : ∫ L in Ioi (0 : ℝ), t L = ∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k)) := laplace_T hσ0
  have iU : ∫ L in Ioi (0 : ℝ), u L
      = (1 / σ ^ 2) * ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) := laplace_S hσ
  rw [i1, i2, i3, i4, iA, iB, iC, iT, iU]


/-- `ζ′/ζ(s) = −Σ_n Λ(n) n^{−s}` for real `s > 1`. -/
theorem zeta_logDeriv_eq {s : ℝ} (hs : 1 < s) :
    deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      = -((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s : ℝ) : ℂ) := by
  have hre : 1 < (s : ℂ).re := by simpa using hs
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hneg : deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      = -LSeries (fun n => (vonMangoldt n : ℂ)) (s : ℂ) := by
    rw [h]; ring
  rw [hneg]
  congr 1
  unfold LSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hn0]


/-- `ψ(¼ + σ/2)` is the real number `Re ψ(¼) + Σ_k 2σ/(b_k(σ+b_k))`. -/
theorem digamma_real_form {σ : ℝ} (hσ : 0 < σ) :
    Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ)
      = ((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re
          + ∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) : ℝ) := by
  have h := digamma_diff_series hσ
  have ha := GppDigammaQuarter.digamma_quarter_real
  have hcast : Complex.digamma (((1 / 4 : ℝ)) : ℂ)
      = (((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re : ℝ) : ℂ) := by
    rw [ha, Complex.ofReal_re]
  have this : Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ)
      = Complex.digamma (((1 / 4 : ℝ)) : ℂ) + ((∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ) := by
    rw [← h]; ring
  calc Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ)
      = Complex.digamma (((1 / 4 : ℝ)) : ℂ) + ((∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ) := this
    _ = (((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re : ℝ) : ℂ)
        + ((∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) : ℝ) : ℂ) := by rw [← hcast]
    _ = _ := (Complex.ofReal_add _ _).symm

/-- **F11 (Round 23, Theorems 1–2 core): the Laplace identity.** For real `σ > ½`,
`∫₀^∞ e^{−σL} D(L) dL = (ξ′/ξ)(½ + σ) / σ²`, with `ξ(z) = ½ z (z − 1) Λ(z)`
(`Λ` Mathlib's completed zeta) and `D` as in `Dfun`. -/
theorem F11_laplace_identity {σ : ℝ} (hσ : 1 / 2 < σ) :
    (((∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * Dfun L : ℝ)) : ℂ)
      = logDeriv xiC (((1 / 2 + σ : ℝ)) : ℂ) / ((σ : ℂ) ^ 2) := by
  have hσ0 : 0 < σ := by linarith
  set s : ℝ := 1 / 2 + σ with hsdef
  have hs : 1 < s := by rw [hsdef]; linarith
  have hx := logDeriv_xiC hs
  have hz : (s : ℂ) / 2 = ((1 / 4 + σ / 2 : ℝ) : ℂ) := by
    rw [hsdef]; push_cast; ring
  rw [hz] at hx
  have hψ := digamma_real_form hσ0
  have hζ := zeta_logDeriv_eq hs
  have hsum : ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s = ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) := by
    rw [hsdef, add_comm]
  rw [hsum] at hζ
  rw [hx, hψ, hζ]
  have hR := laplace_D hσ
  have hdg := digamma_side hσ0
  have hF5c := HR23_F5c_partial_fractions hσ
  have hψre : (Complex.digamma (((1 / 4 + σ / 2 : ℝ)) : ℂ)).re
      = (Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re + ∑' k : ℕ, 2 * σ / (bk k * (σ + bk k)) := by
    rw [hψ, Complex.ofReal_re]
  rw [hψre] at hdg
  have hσne : σ ≠ 0 := hσ0.ne'
  have hsig : σ ^ 2 - 1 / 4 ≠ 0 := by nlinarith
  set Sg : ℝ := ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (σ + 1 / 2) with hSg
  set ST : ℝ := ∑' k : ℕ, 1 / (bk k ^ 2 * (σ + bk k)) with hST
  have hreal : (∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * Dfun L)
      = (1 / s + 1 / (s - 1) - (1 / 2) * Real.log Real.pi
          + (1 / 2) * ((Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re
              + ∑' k : ℕ, 2 * σ / (bk k * (σ + bk k))) - Sg) / σ ^ 2 := by
    rw [hR]
    have h1 : 1 / s + 1 / (s - 1) = 2 * σ / (σ ^ 2 - 1 / 4) := by
      rw [← hF5c, hsdef]; ring_nf
    rw [h1]
    unfold c1 C2
    field_simp
    linear_combination 2 * hdg
  rw [hreal]
  push_cast
  ring


/-! ### `D(0⁺) = 0` -/

theorem continuousOn_Tfun : ContinuousOn Tfun (Ici 0) := by
  unfold Tfun
  refine continuousOn_tsum (fun k => by fun_prop) summable_inv_bk_sq ?_
  intro k L hL
  have hL0 : 0 ≤ L := hL
  have hb := bk_pos k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem Tfun_zero : Tfun 0 = C2 := by
  unfold Tfun C2
  simp

theorem Dfun_zero : Dfun 0 = 0 := by
  unfold Dfun
  have hS : HR23_S 0 = 0 := by
    unfold HR23_S
    simp
  rw [hS, Tfun_zero]
  norm_num

/-- **`D(0⁺) = 0`.** -/
theorem tendsto_Dfun_zero : Filter.Tendsto Dfun (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hT : ContinuousWithinAt Tfun (Ici 0) 0 := continuousOn_Tfun 0 (Set.mem_Ici.mpr le_rfl)
  have hD : ContinuousWithinAt Dfun (Ici 0) 0 := by
    unfold Dfun
    refine ((ContinuousWithinAt.sub ?_ hT).sub HR23_S_continuous.continuousWithinAt)
    fun_prop
  have := (hD.mono Set.Ioi_subset_Ici_self).tendsto
  rwa [Dfun_zero] at this


/-! ### `C₂ = ψ′(¼)/4` -/

theorem hasDerivAt_digamma_quarter :
    HasDerivAt Complex.digamma
      (1 / (((1 / 4 : ℝ) : ℂ)) ^ 2 + ∑' n : ℕ, 1 / ((n : ℂ) + 1 + ((1 / 4 : ℝ) : ℂ)) ^ 2)
      (((1 / 4 : ℝ)) : ℂ) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have ha : ((1 / 4 : ℝ) : ℂ) ∈ U := by simp [hU]
  have hne : ∀ n : ℕ, ∀ z ∈ U, (n : ℂ) + 1 + z ≠ 0 := by
    intro n z hz h
    have := congrArg Complex.re h
    simp at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 0 < z.re := hz
    linarith
  set g : ℕ → ℂ → ℂ := fun n z => ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + 1 + z)⁻¹ with hg
  set g' : ℕ → ℂ → ℂ := fun n z => (((n : ℂ) + 1 + z) ^ 2)⁻¹ with hg'
  have hu : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hder : ∀ (n : ℕ) (z : ℂ), z ∈ U → HasDerivAt (g n) (g' n z) z := by
    intro n z hz
    have hw := hne n z hz
    have h1 : HasDerivAt (fun w : ℂ => (n : ℂ) + 1 + w) 1 z := (hasDerivAt_id z).const_add _
    have h2 := h1.inv hw
    refine (h2.const_sub (((n : ℂ) + 1)⁻¹)).congr_deriv ?_
    simp only [hg']
    field_simp
  have hbd : ∀ (n : ℕ) (z : ℂ), z ∈ U → ‖g' n z‖ ≤ 1 / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
    intro n z hz
    have hz0 : 0 < z.re := hz
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hle : ((n : ℝ) + 1) ≤ ‖(n : ℂ) + 1 + z‖ := by
      calc ((n : ℝ) + 1) ≤ ((n : ℂ) + 1 + z).re := by simp; linarith
        _ ≤ ‖(n : ℂ) + 1 + z‖ := Complex.re_le_norm _
    simp only [hg']
    rw [norm_inv, norm_pow]
    push_cast
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) hle 2
  have hg0 : Summable (fun n : ℕ => g n ((1 / 4 : ℝ) : ℂ)) := by
    have := (Complex.hasSum_digamma (ne_neg_nat_pos (by norm_num : (0 : ℝ) < 1 / 4))).summable
    simpa [hg, one_div] using this
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu hUo hUc hder hbd ha hg0 ha
  -- digamma agrees with `−γ − 1/z + Σ g` on `U`
  have hev : (fun z : ℂ => -(Real.eulerMascheroniConstant : ℂ) - z⁻¹ + ∑' n : ℕ, g n z)
      =ᶠ[nhds ((1 / 4 : ℝ) : ℂ)] Complex.digamma := by
    filter_upwards [hUo.mem_nhds ha] with z hz
    have hz' : ∀ m : ℕ, z ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      have hz0 : 0 < z.re := hz
      simp at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [Complex.digamma_eq_tsum hz']
    simp only [hg, one_div]
  have hz0 : ((1 / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≠ 0)
  have hinv : HasDerivAt (fun z : ℂ => -(Real.eulerMascheroniConstant : ℂ) - z⁻¹)
      ((((1 / 4 : ℝ) : ℂ) ^ 2)⁻¹) ((1 / 4 : ℝ) : ℂ) :=
    ((hasDerivAt_inv hz0).const_sub (-(Real.eulerMascheroniConstant : ℂ))).congr_deriv (by ring)
  have hfinal := (hinv.add hderiv).congr_of_eventuallyEq hev.symm
  refine hfinal.congr_deriv ?_
  simp only [hg', one_div]


/-- **`ψ′(¼) = 4 C₂`**, i.e. `C₂ = ψ′(¼)/4` (`C₂ = Σ_k 1/b_k²`). -/
theorem deriv_digamma_quarter : deriv Complex.digamma (((1 / 4 : ℝ)) : ℂ) = ((4 * C2 : ℝ) : ℂ) := by
  rw [hasDerivAt_digamma_quarter.deriv]
  set q : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1 / 4) ^ 2 with hq
  have hqb : ∀ k : ℕ, q k = 4 * (1 / bk k ^ 2) := by
    intro k
    simp only [hq, bk]
    have : (k : ℝ) + 1 / 4 = (2 * (k : ℝ) + 1 / 2) / 2 := by ring
    rw [this]
    have hb : (0 : ℝ) < 2 * (k : ℝ) + 1 / 2 := by positivity
    field_simp
    norm_num
  have hqs : Summable q := by
    have : q = fun k => 4 * (1 / bk k ^ 2) := funext hqb
    rw [this]; exact summable_inv_bk_sq.mul_left 4
  have hsum : ∑' k : ℕ, q k = 4 * C2 := by
    simp_rw [hqb]; rw [tsum_mul_left]; rfl
  have hshift := hqs.tsum_eq_zero_add
  have hq0 : q 0 = 16 := by simp [hq]; norm_num
  have hreal : ∑' n : ℕ, q (n + 1) = 4 * C2 - 16 := by
    rw [← hsum, hshift, hq0]; ring
  have hcast : ∑' n : ℕ, 1 / ((n : ℂ) + 1 + ((1 / 4 : ℝ) : ℂ)) ^ 2 = ((∑' n : ℕ, q (n + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [hq]
    push_cast
    ring_nf
  rw [hcast, hreal]
  push_cast
  norm_num

end GppHeartLaplace

#print axioms GppHeartLaplace.F11_laplace_identity
#print axioms GppHeartLaplace.deriv_digamma_quarter
#print axioms GppHeartLaplace.tendsto_Dfun_zero
#print axioms GppHeartLaplace.laplace_T
#print axioms GppHeartLaplace.laplace_S
#print axioms GppHeartLaplace.digamma_diff_series
#print axioms GppHeartLaplace.digamma_side
