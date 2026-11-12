/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6827583106, "next exact question".

# `Regularity` split along the mollification route

`Regularity` (HEFIdentSplit) is `explicit_formula_even`'s conclusion for the `C²_c` even
function `g_d`. Mollify: `φ_n = (bumpN n).normed` (even, `≥ 0`, `∫ = 1`, support in
`(−ε_n, ε_n)`, `ε_n = 1/(n+1)`), `g_{d,n} = φ_n ⋆ g_d`. Then `IsTestFunction g_{d,n}` and
`g_{d,n}` is even (PROVED), so `explicit_formula_even` applies to `g_{d,n}`; let `n → ∞`.

Named Props, stated exactly (Turbo's (a), (b), (c)):

* `MollC1` ((a)): mollifiers of a `C¹_c` function converge in `C¹` (uniformly, with derivative).
* `StripConv` ((b)): `|φ̂_n(s)| ≤ e^{ε_n/2}` on `0 < Re s < 1` and
  `ĝ_{d,n}(s) = ĝ_d(s) · φ̂_n(s)`.
* `DomReal` / `DomZero` ((c)): dominated convergence for the real-place integral on `(0, ∞)`
  and for the zero-side `tsum`.

PROVED here (std axioms, 0 sorry): `stripConv : StripConv`, `domReal : DomReal` and
`domZero : DomZero` (Mathlib: `tendsto_integral_of_dominated_convergence`, Tannery
`tendsto_tsum_of_dominated_convergence`), `phiHat_tendsto` (`φ̂_n(s) → 1`, Mathlib
`ContDiffBump.convolution_tendsto_right_of_continuous`), `isTest_moll`, `moll_even`,
`zeroSide_summable` (the summability half of `Regularity`, unconditional: `transform` +
`cosToExp` + `toEquiv`), `zeroLimit` (zero side, from (b) + `DomZero` + `phiHat_tendsto`),
`poleLimit : PoleLimit`, `primeLimit : PrimeLimit`, and the assembly
`regularity_of_archLimit : ArchLimit → Regularity` (limit uniqueness against
`explicit_formula_even` at every `n`).

Named premises, NOT proved: `ArchLimit` (real-place term of `g_{d,n}` → that of `g_d`) and
`MollC1` ((a); not in Mathlib in this form). `ArchLimit ⇐ (a) + DomReal` is CHECKED on paper
(mean-value bound near `u = 0`, uniform support for the tail), not formalised.
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.HEFIdentSplit
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Group.Tannery

namespace GppRegularitySplit

open MeasureTheory Filter Topology GppHEFIdentSplit GppKreinHPsi
open scoped ContDiff

/-! ## 0. Mollifiers -/

/-- `ε_n = 1/(n+1)`. -/
noncomputable def epsN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsN_pos (n : ℕ) : 0 < epsN n := by unfold epsN; positivity

theorem epsN_le_one (n : ℕ) : epsN n ≤ 1 := by
  unfold epsN
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_epsN : Tendsto epsN atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The bump with `rIn = ε_n/2`, `rOut = ε_n`. -/
noncomputable def bumpN (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := epsN n / 2
  rOut := epsN n
  rIn_pos := by have := epsN_pos n; positivity
  rIn_lt_rOut := by have := epsN_pos n; linarith

/-- `φ_n`: even, `≥ 0`, `∫ φ_n = 1`, support `(−ε_n, ε_n)`, `C^∞`. -/
noncomputable def phiN (n : ℕ) : ℝ → ℝ := (bumpN n).normed volume

/-- `g_{d,n} = φ_n ⋆ g`. -/
noncomputable def moll (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution (phiN n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem moll_apply (n : ℕ) (g : ℝ → ℝ) (u : ℝ) :
    moll n g u = ∫ t, phiN n t * g (u - t) := rfl

theorem phiN_nonneg (n : ℕ) (t : ℝ) : 0 ≤ phiN n t := ContDiffBump.nonneg_normed _ _

theorem phiN_integral (n : ℕ) : ∫ t, phiN n t = 1 := ContDiffBump.integral_normed _

theorem phiN_integrable (n : ℕ) : Integrable (phiN n) :=
  ContDiffBump.integrable_normed (bumpN n)

theorem phiN_eq_zero {n : ℕ} {t : ℝ} (h : epsN n ≤ |t|) : phiN n t = 0 := by
  have : t ∉ Function.support (phiN n) := by
    unfold phiN
    rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact h
  exact Function.notMem_support.1 this

/-! ## 1. Facts on `triG` and `g_d` -/

theorem triG_continuous : Continuous triG := by
  have e : triG = fun y : ℝ => if |y| ≤ 1 then 2 / 3 - |y| ^ 2 + |y| ^ 3 / 2
      else if |y| ≤ 2 then (2 - |y|) ^ 3 / 6 else 0 := by
    funext y; unfold triG; rw [sq_abs]
  rw [e]
  refine Continuous.if_le (by fun_prop)
    (Continuous.if_le (by fun_prop) continuous_const continuous_abs continuous_const ?_)
    continuous_abs continuous_const ?_
  · intro y h; rw [h]; norm_num
  · intro y h; rw [h]; norm_num

theorem gd_continuous (d : ℝ) : Continuous (gd d) := by
  unfold gd
  exact ((triG_continuous.comp (continuous_id.sub continuous_const)).add
    (triG_continuous.comp (continuous_id.add continuous_const))).div_const 2

theorem abs_gd_le (d u : ℝ) : |gd d u| ≤ 1 := by
  unfold gd
  have h1 := abs_triG_le (u - d)
  have h2 := abs_triG_le (u + d)
  rw [abs_div, abs_two]
  calc |triG (u - d) + triG (u + d)| / 2 ≤ (|triG (u - d)| + |triG (u + d)|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ 1 := by linarith

theorem gd_eq_zero {d u : ℝ} (h : |d| + 2 < |u|) : gd d u = 0 := by
  have h1 := abs_sub_abs_le_abs_sub u d
  have h2 := abs_sub_abs_le_abs_sub u (-d)
  rw [abs_neg, sub_neg_eq_add] at h2
  unfold gd
  rw [triG_eq_zero (by linarith), triG_eq_zero (by linarith)]
  simp

theorem gd_hasCompactSupport (d : ℝ) : HasCompactSupport (gd d) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (|d| + 2)) fun u hu => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hu
  exact gd_eq_zero hu

/-! ## 2. Facts on `g_{d,n}` -/

theorem abs_moll_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (n : ℕ) (u : ℝ) : |moll n g u| ≤ 1 := by
  rw [moll_apply, ← Real.norm_eq_abs, ← phiN_integral n]
  refine norm_integral_le_of_norm_le (phiN_integrable n) (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (phiN_nonneg n t)]
  exact mul_le_of_le_one_right (phiN_nonneg n t) (hg _)

theorem moll_gd_eq_zero {d u : ℝ} (n : ℕ) (h : |d| + 3 < |u|) : moll n (gd d) u = 0 := by
  rw [moll_apply]
  have hz : ∀ t, phiN n t * gd d (u - t) = 0 := by
    intro t
    by_cases ht : epsN n ≤ |t|
    · rw [phiN_eq_zero ht, zero_mul]
    · push Not at ht
      have h1 := epsN_le_one n
      have h2 := abs_sub_abs_le_abs_sub u t
      rw [gd_eq_zero (by linarith), mul_zero]
  simp only [hz, integral_zero]

theorem moll_contDiff (n : ℕ) (d : ℝ) : ContDiff ℝ ∞ (moll n (gd d)) :=
  (ContDiffBump.hasCompactSupport_normed _).contDiff_convolution_left _
    (bumpN n).contDiff_normed (gd_continuous d).locallyIntegrable

theorem moll_continuous (n : ℕ) (d : ℝ) : Continuous (moll n (gd d)) :=
  (moll_contDiff n d).continuous

/-- **`g_{d,n}` is a test function (PROVED).** -/
theorem isTest_moll (n : ℕ) (d : ℝ) : GppMeyerSpectralWeil.IsTestFunction (moll n (gd d)) :=
  ⟨moll_contDiff n d,
    (ContDiffBump.hasCompactSupport_normed _).convolution _ (gd_hasCompactSupport d)⟩

/-- **`g_{d,n}` is even (PROVED).** -/
theorem moll_even (n : ℕ) (d u : ℝ) : moll n (gd d) (-u) = moll n (gd d) u := by
  rw [moll_apply, moll_apply]
  refine (integral_neg_eq_self (fun t => phiN n t * gd d (-u - t)) volume).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only []
  rw [show -u - -t = -(u - t) by ring, gd_even]
  unfold phiN
  rw [ContDiffBump.normed_neg]

/-- Pointwise convergence `g_{n} → g` for continuous `g` (Mathlib). -/
theorem moll_tendsto {g : ℝ → ℝ} (hg : Continuous g) (u : ℝ) :
    Tendsto (fun n => moll n g u) atTop (𝓝 (g u)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (φ := bumpN) tendsto_epsN hg u

/-! ## 3. The three named Props (a), (b), (c) -/

/-- **(a) `MollC1`** (named, NOT proved here): for a `C¹_c` function, the mollifiers converge
to it in `C¹` (uniformly together with the first derivative). -/
def MollC1 : Prop := ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
  TendstoUniformly (fun n => moll n g) g atTop ∧
    TendstoUniformly (fun n => deriv (moll n g)) (deriv g) atTop

/-- **(b) `StripConv`**: strip bound and convolution identity. -/
def StripConv : Prop := ∀ (n : ℕ) (d : ℝ) (s : ℂ), 0 < s.re → s.re < 1 →
  ‖GppMeyerSpectralWeil.spectralTransform (phiN n) s‖ ≤ Real.exp (epsN n / 2) ∧
    GppMeyerSpectralWeil.spectralTransform (moll n (gd d)) s =
      GppMeyerSpectralWeil.spectralTransform (gd d) s *
        GppMeyerSpectralWeil.spectralTransform (phiN n) s

/-- **(c), real place `DomReal`**: dominated convergence for integrals over `(0, ∞)`. -/
def DomReal : Prop := ∀ (F : ℕ → ℝ → ℝ) (f bound : ℝ → ℝ),
  IntegrableOn bound (Set.Ioi 0) →
  (∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.Ioi 0))) →
  (∀ n, ∀ u ∈ Set.Ioi (0 : ℝ), |F n u| ≤ bound u) →
  (∀ u ∈ Set.Ioi (0 : ℝ), Tendsto (fun n => F n u) atTop (𝓝 (f u))) →
  Tendsto (fun n => ∫ u in Set.Ioi 0, F n u) atTop (𝓝 (∫ u in Set.Ioi 0, f u))

/-- **(c), zero side `DomZero`**: dominated convergence for the zero-side `tsum`. -/
def DomZero : Prop := ∀ (F : ℕ → GppWeilCriterion.nontrivialZeros → ℂ)
  (f : GppWeilCriterion.nontrivialZeros → ℂ) (bound : GppWeilCriterion.nontrivialZeros → ℝ),
  Summable bound → (∀ n ρ, ‖F n ρ‖ ≤ bound ρ) → (∀ ρ, Tendsto (fun n => F n ρ) atTop (𝓝 (f ρ))) →
  Tendsto (fun n => ∑' ρ, F n ρ) atTop (𝓝 (∑' ρ, f ρ))

/-! ## 4. Discharges of (b) and (c) -/

/-- **(c) real place PROVED** (Mathlib dominated convergence). -/
theorem domReal : DomReal := by
  intro F f bound hb hm hle hlim
  refine tendsto_integral_of_dominated_convergence bound hm hb (fun n => ?_) ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs]; exact hle n u hu
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hlim)

/-- **(c) zero side PROVED** (Mathlib, Tannery's theorem). -/
theorem domZero : DomZero := fun _ _ _ hs hle hlim =>
  tendsto_tsum_of_dominated_convergence hs hlim (Eventually.of_forall hle)

/-- Strip bound `|φ̂_n(s)| ≤ e^{ε_n/2}` on `0 < Re s < 1` (PROVED). -/
theorem norm_phiHat_le (n : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖GppMeyerSpectralWeil.spectralTransform (phiN n) s‖ ≤ Real.exp (epsN n / 2) := by
  unfold GppMeyerSpectralWeil.spectralTransform
  calc ‖∫ u : ℝ, (phiN n u : ℂ) * Complex.exp ((s - 1 / 2) * u)‖
        ≤ ∫ u : ℝ, phiN n u * Real.exp (epsN n / 2) := by
        refine norm_integral_le_of_norm_le ((phiN_integrable n).mul_const _)
          (Eventually.of_forall fun u => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phiN_nonneg n u),
          Complex.norm_exp]
        by_cases hu : epsN n ≤ |u|
        · rw [phiN_eq_zero hu]; simp
        · push Not at hu
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (phiN_nonneg n u)
          have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by
            simp [Complex.mul_re]
          rw [hre]
          have hs : |s.re - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
          calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
            _ = |s.re - 1 / 2| * |u| := abs_mul _ _
            _ ≤ 1 / 2 * epsN n := mul_le_mul hs hu.le (abs_nonneg _) (by norm_num)
            _ = epsN n / 2 := by ring
    _ = Real.exp (epsN n / 2) := by rw [integral_mul_const, phiN_integral, one_mul]

theorem phiN_continuous (n : ℕ) : Continuous (phiN n) :=
  ((bumpN n).contDiff_normed (μ := volume) (n := 0)).continuous

/-- Convolution identity `ĝ_{d,n}(s) = ĝ_d(s) φ̂_n(s)` for every `s` (PROVED, Fubini via
Mathlib `integral_convolution`). -/
theorem convIdentity (n : ℕ) (d : ℝ) (s : ℂ) :
    GppMeyerSpectralWeil.spectralTransform (moll n (gd d)) s =
      GppMeyerSpectralWeil.spectralTransform (gd d) s *
        GppMeyerSpectralWeil.spectralTransform (phiN n) s := by
  set a : ℂ := s - 1 / 2 with ha
  set F : ℝ → ℂ := fun t => (phiN n t : ℂ) * Complex.exp (a * t) with hF
  set G : ℝ → ℂ := fun v => (gd d v : ℂ) * Complex.exp (a * v) with hG
  have hFi : Integrable F := by
    refine Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_ofReal.comp (phiN_continuous n)).mul (by fun_prop)) ?_
    exact (ContDiffBump.hasCompactSupport_normed (bumpN n)).comp_left
      Complex.ofReal_zero |>.mul_right
  have hGi : Integrable G := integrable_gd_exp d a
  have hpt : ∀ u : ℝ, (moll n (gd d) u : ℂ) * Complex.exp (a * u) =
      MeasureTheory.convolution F G (ContinuousLinearMap.lsmul ℂ ℂ) volume u := by
    intro u
    rw [convolution_lsmul, moll_apply, ← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, hG, smul_eq_mul]
    have e : Complex.exp (a * u) = Complex.exp (a * t) * Complex.exp (a * ((u - t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [e]; push_cast; ring
  unfold GppMeyerSpectralWeil.spectralTransform
  rw [← ha]
  calc ∫ u : ℝ, (moll n (gd d) u : ℂ) * Complex.exp (a * u)
      = ∫ u : ℝ, MeasureTheory.convolution F G (ContinuousLinearMap.lsmul ℂ ℂ) volume u :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ t, F t) • (∫ v, G v) := integral_convolution _ hFi hGi
    _ = _ := by rw [smul_eq_mul, mul_comm]

/-- **(b) `StripConv` PROVED.** -/
theorem stripConv : StripConv := fun n d _ h0 h1 => ⟨norm_phiHat_le n h0 h1, convIdentity n d _⟩

/-- `φ̂_n(s) → 1` (PROVED, Mathlib `ContDiffBump.convolution_tendsto_right_of_continuous`
applied to `v ↦ e^{−(s − 1/2) v}` at `0`). -/
theorem phiHat_tendsto (s : ℂ) :
    Tendsto (fun n => GppMeyerSpectralWeil.spectralTransform (phiN n) s) atTop (𝓝 1) := by
  set h : ℝ → ℂ := fun v => Complex.exp (-(s - 1 / 2) * v) with hh
  have hc : Continuous h := by fun_prop
  have hlim := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := bumpN) tendsto_epsN hc 0
  have h0 : h 0 = 1 := by simp [hh]
  rw [h0] at hlim
  refine hlim.congr fun n => ?_
  rw [convolution_lsmul]
  unfold GppMeyerSpectralWeil.spectralTransform phiN
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hh, Complex.real_smul, zero_sub]
  congr 2
  push_cast
  ring

/-! ## 5. The zero side -/

/-- **Summability half of `Regularity` (PROVED, unconditional).** -/
theorem zeroSide_summable (d : ℝ) :
    Summable (fun ρ : GppWeilCriterion.nontrivialZeros =>
      (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ) := by
  have h := (cosToExp d).1
  rw [← toEquiv.summable_iff]
  refine h.congr fun γ => ?_
  show (GppKreinPoleSplit.mult (γ : ℂ) : ℂ) * (GppKreinPoleSplit.efCoeff γ * Complex.cos (γ * d)) =
    (GppXiZeroCounting.zeroMult (GppKreinHPsiChain.rho (γ : ℂ)) : ℂ) *
      GppMeyerSpectralWeil.spectralTransform (gd d) (GppKreinHPsiChain.rho γ)
  rw [transform d γ γ.2]
  rfl

/-- **Zero-side limit (PROVED)** from (b), `DomZero` and `φ̂_n → 1`. -/
theorem zeroLimit (d : ℝ) :
    Tendsto (fun n => ∑' ρ : GppWeilCriterion.nontrivialZeros,
        (GppXiZeroCounting.zeroMult ρ : ℂ) *
          GppMeyerSpectralWeil.spectralTransform (moll n (gd d)) ρ) atTop
      (𝓝 (∑' ρ : GppWeilCriterion.nontrivialZeros,
        (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ)) := by
  have hs := zeroSide_summable d
  have hmem : ∀ ρ : GppWeilCriterion.nontrivialZeros, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => ρ.2.2
  have hrw : ∀ (n : ℕ) (ρ : GppWeilCriterion.nontrivialZeros),
      (GppXiZeroCounting.zeroMult ρ : ℂ) *
          GppMeyerSpectralWeil.spectralTransform (moll n (gd d)) ρ =
        (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ *
          GppMeyerSpectralWeil.spectralTransform (phiN n) ρ := by
    intro n ρ
    rw [(stripConv n d ρ (hmem ρ).1 (hmem ρ).2).2, mul_assoc]
  simp_rw [hrw]
  refine domZero _ _ (fun ρ => ‖(GppXiZeroCounting.zeroMult ρ : ℂ) *
      GppMeyerSpectralWeil.spectralTransform (gd d) ρ‖ * Real.exp (1 / 2))
    ((summable_norm_iff.2 hs).mul_right _) (fun n ρ => ?_) (fun ρ => ?_)
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((stripConv n d ρ (hmem ρ).1 (hmem ρ).2).1.trans
      (Real.exp_le_exp.2 ?_)) (norm_nonneg _)
    linarith [epsN_le_one n]
  · simpa using (phiHat_tendsto (ρ : ℂ)).const_mul
      ((GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ)

/-! ## 6. The right side: pole, prime, real place -/

/-- Pole term of `g_{d,n}` converges. -/
def PoleLimit : Prop := ∀ d : ℝ,
  Tendsto (fun n => GppArithmeticReflection.poleTerm (moll n (gd d))) atTop
    (𝓝 (GppArithmeticReflection.poleTerm (gd d)))

/-- Prime side of `g_{d,n}` converges. -/
def PrimeLimit : Prop := ∀ d : ℝ,
  Tendsto (fun n => GppWeilLadder.primeSide (moll n (gd d))) atTop
    (𝓝 (GppWeilLadder.primeSide (gd d)))

/-- **Real-place term of `g_{d,n}` converges** (named premise, NOT proved). On paper:
`(a)` + `DomReal` with the mean-value bound near `u = 0` and uniform support for the tail. -/
def ArchLimit : Prop := ∀ d : ℝ,
  Tendsto (fun n => GppArchimedeanFloor.archimedeanTerm (moll n (gd d))) atTop
    (𝓝 (GppArchimedeanFloor.archimedeanTerm (gd d)))

/-- **`PoleLimit` PROVED** (dominated convergence on `ℝ`, bound `2cosh(R/2)` on `[−R, R]`,
`R = |d| + 3`). -/
theorem poleLimit : PoleLimit := by
  intro d
  set R : ℝ := |d| + 3
  unfold GppArithmeticReflection.poleTerm
  refine tendsto_integral_of_dominated_convergence
    ((Set.Icc (-R) R).indicator fun _ => 2 * Real.cosh (R / 2)) (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact ((moll_continuous n d).mul (by fun_prop)).aestronglyMeasurable
  · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  · refine Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hc : |2 * Real.cosh (u / 2)| ≤ 2 * Real.cosh (R / 2) := by
        rw [abs_of_pos (by positivity)]
        have : |u / 2| ≤ |R / 2| := by
          rw [abs_div, abs_div, abs_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ R)]
          have := abs_le.2 hu; linarith
        have := Real.cosh_le_cosh.2 this
        linarith
      calc |moll n (gd d) u| * |2 * Real.cosh (u / 2)| ≤ 1 * (2 * Real.cosh (R / 2)) :=
            mul_le_mul (abs_moll_le (abs_gd_le d) n u) hc (abs_nonneg _) zero_le_one
        _ = 2 * Real.cosh (R / 2) := one_mul _
    · rw [Set.indicator_of_notMem hu, moll_gd_eq_zero n, zero_mul, norm_zero]
      by_contra hc
      exact hu (abs_le.1 (not_lt.1 hc))
  · exact Eventually.of_forall fun u => (moll_tendsto (gd_continuous d) u).mul_const _

/-- **`PrimeLimit` PROVED** (finitely many terms: `log n ≤ |d| + 3`; Tannery with a finitely
supported bound). -/
theorem primeLimit : PrimeLimit := by
  intro d
  set R : ℝ := |d| + 3
  set N : ℕ := ⌈Real.exp R⌉₊
  have hbig : ∀ k : ℕ, N < k → R < Real.log k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      have : (0 : ℕ) < k := lt_of_le_of_lt (Nat.zero_le _) hk
      exact_mod_cast this
    rw [Real.lt_log_iff_exp_lt hk0]
    calc Real.exp R ≤ N := Nat.le_ceil _
      _ < k := by exact_mod_cast hk
  have hzero : ∀ (f : ℝ → ℝ), (∀ u, R < |u| → f u = 0) → ∀ k : ℕ, N < k →
      f (Real.log k) + f (-Real.log k) = 0 := by
    intro f hf k hk
    have hl := hbig k hk
    have hpos : 0 < Real.log k := lt_of_le_of_lt (by positivity) hl
    rw [hf _ (by rw [abs_of_pos hpos]; exact hl), hf _ (by rw [abs_neg, abs_of_pos hpos]; exact hl),
      add_zero]
  set c : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k / Real.sqrt k with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  unfold GppWeilLadder.primeSide
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => if k ≤ N then c k * 2 else 0)
    ?_ (fun k => ?_) (Eventually.of_forall fun n k => ?_)
  · refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun k hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [if_neg (by omega)]
  · exact ((moll_tendsto (gd_continuous d) _).add (moll_tendsto (gd_continuous d) _)).const_mul _
  · by_cases hk : k ≤ N
    · rw [if_pos hk, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      refine mul_le_mul_of_nonneg_left ?_ (hc0 k)
      calc |moll n (gd d) (Real.log k) + moll n (gd d) (-Real.log k)|
          ≤ |moll n (gd d) (Real.log k)| + |moll n (gd d) (-Real.log k)| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (abs_moll_le (abs_gd_le d) n _) (abs_moll_le (abs_gd_le d) n _)
        _ = 2 := by norm_num
    · rw [if_neg hk, hzero (moll n (gd d)) (fun u hu => moll_gd_eq_zero n hu) k (by omega),
        mul_zero, norm_zero]

/-! ## 7. Assembly -/

/-- **`Regularity` from `ArchLimit` (PROVED).** For every `n`, `explicit_formula_even` holds
for `g_{d,n}`; the zero side converges (`zeroLimit`), the right side converges (`poleLimit`,
`ArchLimit`, `primeLimit`); limits in `ℂ` are unique. -/
theorem regularity_of_archLimit (hA : ArchLimit) : Regularity := by
  intro d
  refine ⟨zeroSide_summable d, ?_⟩
  have hZ := zeroLimit d
  have hW : Tendsto (fun n => GppArithmeticReflection.weilForm (moll n (gd d))) atTop
      (𝓝 (GppArithmeticReflection.weilForm (gd d))) := by
    unfold GppArithmeticReflection.weilForm
    exact ((poleLimit d).add (hA d)).sub (primeLimit d)
  have hWc := (Complex.continuous_ofReal.tendsto _).comp hW
  have heq : (fun n => ∑' ρ : GppWeilCriterion.nontrivialZeros,
      (GppXiZeroCounting.zeroMult ρ : ℂ) *
        GppMeyerSpectralWeil.spectralTransform (moll n (gd d)) ρ) =
      Complex.ofReal ∘ fun n => GppArithmeticReflection.weilForm (moll n (gd d)) :=
    funext fun n =>
      (GppExplicitFormulaAssembly.explicit_formula_even (isTest_moll n d) (moll_even n d)).2
  rw [heq] at hZ
  exact tendsto_nhds_unique hZ hWc

/-- **`Regularity` from (a) + (b) + (c) + `ArchLimit`'s reduction (PROVED as stated):**
whenever `(a) ∧ DomReal` yields `ArchLimit`, `Regularity` follows. (b), (c) are discharged
above, so the only remaining input is the real-place reduction `ArchReduction`.) -/
def ArchReduction : Prop := MollC1 → DomReal → ArchLimit

theorem regularity_of_abc (hR : ArchReduction) (ha : MollC1) : Regularity :=
  regularity_of_archLimit (hR ha domReal)

/-- `HEFIdent` from `ArchLimit` and `ArchMatch` (PROVED). -/
theorem hefIdent_of_archLimit (hL : ArchLimit) (hA : ArchMatch) :
    GppKreinHEFSplit.HEFIdent :=
  hefIdent_of_reg_arch (regularity_of_archLimit hL) hA

end GppRegularitySplit
#print axioms GppRegularitySplit.epsN_pos
#print axioms GppRegularitySplit.epsN_le_one
#print axioms GppRegularitySplit.tendsto_epsN
#print axioms GppRegularitySplit.moll_apply
#print axioms GppRegularitySplit.phiN_nonneg
#print axioms GppRegularitySplit.phiN_integral
#print axioms GppRegularitySplit.phiN_integrable
#print axioms GppRegularitySplit.phiN_eq_zero
#print axioms GppRegularitySplit.triG_continuous
#print axioms GppRegularitySplit.gd_continuous
#print axioms GppRegularitySplit.abs_gd_le
#print axioms GppRegularitySplit.gd_eq_zero
#print axioms GppRegularitySplit.gd_hasCompactSupport
#print axioms GppRegularitySplit.abs_moll_le
#print axioms GppRegularitySplit.moll_gd_eq_zero
#print axioms GppRegularitySplit.moll_contDiff
#print axioms GppRegularitySplit.moll_continuous
#print axioms GppRegularitySplit.isTest_moll
#print axioms GppRegularitySplit.moll_even
#print axioms GppRegularitySplit.moll_tendsto
#print axioms GppRegularitySplit.domReal
#print axioms GppRegularitySplit.domZero
#print axioms GppRegularitySplit.norm_phiHat_le
#print axioms GppRegularitySplit.phiN_continuous
#print axioms GppRegularitySplit.convIdentity
#print axioms GppRegularitySplit.stripConv
#print axioms GppRegularitySplit.phiHat_tendsto
#print axioms GppRegularitySplit.zeroSide_summable
#print axioms GppRegularitySplit.zeroLimit
#print axioms GppRegularitySplit.poleLimit
#print axioms GppRegularitySplit.primeLimit
#print axioms GppRegularitySplit.regularity_of_archLimit
#print axioms GppRegularitySplit.regularity_of_abc
#print axioms GppRegularitySplit.hefIdent_of_archLimit
