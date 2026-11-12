/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6826449670, "next exact question".

# `HEFIdent` split along the item-2 gap map of 6826356315

`HEFIdent` (KreinHEFSplit) says `Kψ(d) = Σ_γ m_γ Ψ(γ)Ψ(−γ) e^{iγd}` for every `d`. It is the
explicit formula for `g_d(u) = ½[triG(u − d) + triG(u + d)]`, `triG = ψ ⋆ ψ` (C², not C^∞).
Named Props, stated exactly:

* `Regularity` ((1)): `explicit_formula_even`'s conclusion, verbatim, for `g_d`: absolute
  summability over `nontrivialZeros` of `ρ ↦ m_ρ ĝ_d(ρ)` and `Σ_ρ m_ρ ĝ_d(ρ) = weilForm g_d`.
* `Transform` ((2)): `ĝ_d(ρ(γ)) = Ψ(γ)Ψ(−γ) cos(γd)` for `γ ∈ Zgamma`.
* `RightSide` ((4)): `weilForm g_d = Kψ(d)`, split as `PoleMatch` (pole term),
  `primeMatch` (prime term) and `ArchMatch` (real-place term).

PROVED here (std axioms, 0 sorry):

* Assembly `hefIdent_of_split : Regularity → Transform → RightSide → HEFIdent`, with (3)
  cos → exp used inside it (`cosToExp`: `γ ↦ −γ` on `Zgamma` with equal multiplicity, from
  `zeroData_symmetric`; `Ψ` even; summability from `hefSumm`), and the index transport
  `toEquiv : Zgamma ≃ nontrivialZeros`.
* `triLaplace`: `∫ triG(v) e^{zv} dv = (e^{2z} − 4e^{z} + 6 − 4e^{−z} + e^{−2z}) / z⁴`, `z ≠ 0`
  (four cubic pieces on `[−2,2]`, explicit antiderivative, FTC); hence `triFourier`
  (`∫ triG e^{iγv} = Ψ(γ)Ψ(−γ)`, `γ ≠ 0`).
* **`transform : Transform`** (translation `integral_gd_exp` + `triFourier`; `γ ≠ 0` on `Zgamma`
  from `noRealZeroStrip`).
* **`poleMatch : PoleMatch`** (`∫ g_d 2cosh(u/2) = 2Ψ(i/2)² cosh(d/2)`, `Ψ(±i/2) = 16 sinh²(1/4)`)
  and **`primeMatch`** (termwise, `triG` even). So `rightSide_of_arch : ArchMatch → RightSide`.
* `hefIdent_of_reg_arch : Regularity → ArchMatch → HEFIdent` and
  `hPsiRegArchChain : HPsi → Regularity → ArchMatch → KreinDecomp → IdentityStep → RH`.

Named premises, NOT proved: `Regularity` (the real analytic gap) and `ArchMatch`.
Mollification route for `Regularity` (paper, CHECKED on paper, not formalised): take an even
`φ ∈ C^∞_c`, supp `φ ⊆ [−1,1]`, `φ ≥ 0`, `∫φ = 1`, `φ_ε = ε⁻¹φ(·/ε)`, `g_{d,ε} = g_d ⋆ φ_ε`. Then
`IsTestFunction g_{d,ε}` and `g_{d,ε}` is even, so `explicit_formula_even` applies. Let `ε → 0`:
zero side: `ĝ_{d,ε}(ρ) = ĝ_d(ρ) φ̂_ε(ρ)` with `|φ̂_ε(ρ)| ≤ ∫φ_ε(u)e^{|u|/2} ≤ e^{ε/2}` on the strip
and `→ 1` pointwise; domination `m_ρ |ĝ_d(ρ)| e^{1/2}`, summable since `|ĝ_d(ρ)| ≤
144²·e^{|d|/2}(1+|γ|)^{−4}` (the bound of `hefSumm`) and `zeroCounting_four`; pole term: uniform
convergence on `[−|d|−3, |d|+3]`; prime side: finite sum, `log n ≤ |d|+3`, pointwise convergence;
real place: `g_{d,ε} → g_d` in C¹ on `[0,1]` (needs only `g_d ∈ C¹`) handles
`(e^{−2u}g(0) − e^{−u/2}g(u))/(1−e^{−2u})` near `u = 0` via the mean value bound, plus uniform
support for the tail. Missing in tree: the C¹ convergence lemma for mollifiers and the
`φ̂_ε` bound on the strip.
`ArchMatch` route: `GppArchimedeanId` (frequency form of `archimedeanTerm`) is proved for test
functions; extend it to `g_d` by the same mollification, then identify the frequency
integrand with `archTerm d` using `ĝ_d(1/2 + it) = Ψ(t)² cos(td)` (`transform`'s computation).
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinHEFSplit
import GppVerify.RiemannHypothesis.SpectralMatchingSplit
import GppVerify.RiemannHypothesis.NoRealZeroStrip
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly
import GppVerify.RiemannHypothesis.XiZeroSymmetry

namespace GppHEFIdentSplit

open MeasureTheory GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit
  GppKreinRepSplit GppKreinHEFSplit ComplexConjugate

/-! ## 0. The translated test function `g_d` -/

/-- `g_d(u) = ½ [triG(u − d) + triG(u + d)]`, `triG = ψ ⋆ ψ` (closed form `GppKreinHPsi.triG`). -/
noncomputable def gd (d : ℝ) (u : ℝ) : ℝ := (triG (u - d) + triG (u + d)) / 2

theorem triG_neg (y : ℝ) : triG (-y) = triG y := by
  unfold triG; rw [abs_neg]; ring_nf

theorem gd_even (d u : ℝ) : gd d (-u) = gd d u := by
  unfold gd
  rw [show -u - d = -(u + d) by ring, show -u + d = -(u - d) by ring, triG_neg, triG_neg]
  ring

theorem triG_measurable : Measurable triG := by
  unfold triG
  refine Measurable.ite ?_ (by fun_prop) (Measurable.ite ?_ (by fun_prop) measurable_const)
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const

theorem triG_eq_zero {y : ℝ} (h : 2 < |y|) : triG y = 0 := by
  unfold triG
  rw [if_neg (by linarith), if_neg (by linarith)]

theorem abs_triG_le (y : ℝ) : |triG y| ≤ 1 := by
  unfold triG
  have ha := abs_nonneg y
  split_ifs with h1 h2
  · rw [abs_le]
    have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    constructor <;> nlinarith [mul_nonneg ha ha, mul_nonneg (mul_nonneg ha ha) ha]
  · rw [abs_le]
    have h0 : 0 ≤ 2 - |y| := by linarith
    have h1' : 2 - |y| ≤ 1 := by linarith
    constructor
    · nlinarith [pow_nonneg h0 3]
    · nlinarith [pow_le_one₀ h0 h1' (n := 3)]
  · simp

/-- `u ↦ triG(u) e^{zu}` is integrable for every complex `z`. -/
theorem integrable_triG_exp (z : ℂ) :
    Integrable (fun v : ℝ => (triG v : ℂ) * Complex.exp (z * v)) := by
  have hb : Integrable ((Set.Icc (-2 : ℝ) 2).indicator fun _ => Real.exp (2 * ‖z‖)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((Complex.measurable_ofReal.comp triG_measurable).mul
      (by fun_prop)).aestronglyMeasurable
  · by_cases hv : v ∈ Set.Icc (-2 : ℝ) 2
    · rw [Set.indicator_of_mem hv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp]
      have hv' : |v| ≤ 2 := abs_le.2 hv
      have hre : (z * v).re ≤ 2 * ‖z‖ := by
        calc (z * v).re ≤ ‖z * (v : ℂ)‖ := Complex.re_le_norm _
          _ = ‖z‖ * |v| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ ‖z‖ * 2 := mul_le_mul_of_nonneg_left hv' (norm_nonneg _)
          _ = 2 * ‖z‖ := by ring
      calc |triG v| * Real.exp (z * v).re ≤ 1 * Real.exp (2 * ‖z‖) :=
            mul_le_mul (abs_triG_le v) (Real.exp_le_exp.2 hre) (by positivity) zero_le_one
        _ = Real.exp (2 * ‖z‖) := one_mul _
    · rw [Set.indicator_of_notMem hv]
      have hv' : 2 < |v| := by
        by_contra hc; exact hv (abs_le.1 (not_lt.1 hc))
      rw [triG_eq_zero hv']; simp

theorem integrable_sub_shift (d : ℝ) (z : ℂ) :
    Integrable fun u : ℝ => (triG (u - d) : ℂ) * Complex.exp (z * u) := by
  have := ((integrable_triG_exp z).comp_sub_right d).const_mul (Complex.exp (z * d))
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [show (z * u : ℂ) = z * ((u - d : ℝ) : ℂ) + z * d by push_cast; ring, Complex.exp_add]
  ring

theorem integrable_add_shift (d : ℝ) (z : ℂ) :
    Integrable fun u : ℝ => (triG (u + d) : ℂ) * Complex.exp (z * u) := by
  have := ((integrable_triG_exp z).comp_add_right d).const_mul (Complex.exp (-(z * d)))
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [show (z * u : ℂ) = z * ((u + d : ℝ) : ℂ) + -(z * d) by push_cast; ring, Complex.exp_add]
  ring

/-- **Translation (PROVED).** `∫ g_d(u) e^{zu} du = ½(e^{zd} + e^{−zd}) ∫ triG(v) e^{zv} dv`. -/
theorem integral_gd_exp (d : ℝ) (z : ℂ) :
    ∫ u : ℝ, (gd d u : ℂ) * Complex.exp (z * u) =
      (Complex.exp (z * d) + Complex.exp (-(z * d))) / 2 *
        ∫ v : ℝ, (triG v : ℂ) * Complex.exp (z * v) := by
  set F : ℝ → ℂ := fun v => (triG v : ℂ) * Complex.exp (z * v) with hF
  have hI := integrable_triG_exp z
  have h1 : ∫ u : ℝ, (triG (u - d) : ℂ) * Complex.exp (z * u) =
      Complex.exp (z * d) * ∫ v, F v := by
    rw [← integral_sub_right_eq_self (μ := volume) F d, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF]
    rw [show (z * u : ℂ) = z * ((u - d : ℝ) : ℂ) + z * d by push_cast; ring, Complex.exp_add]
    ring
  have h2 : ∫ u : ℝ, (triG (u + d) : ℂ) * Complex.exp (z * u) =
      Complex.exp (-(z * d)) * ∫ v, F v := by
    rw [← integral_add_right_eq_self (μ := volume) F d, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF]
    rw [show (z * u : ℂ) = z * ((u + d : ℝ) : ℂ) + -(z * d) by push_cast; ring, Complex.exp_add]
    ring
  have i1 := integrable_sub_shift d z
  have i2 := integrable_add_shift d z
  have hsplit : (fun u : ℝ => (gd d u : ℂ) * Complex.exp (z * u)) = fun u =>
      (1 / 2 : ℂ) * ((triG (u - d) : ℂ) * Complex.exp (z * u)) +
        (1 / 2 : ℂ) * ((triG (u + d) : ℂ) * Complex.exp (z * u)) := by
    funext u; unfold gd; push_cast; ring
  rw [hsplit, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul, h1, h2]
  ring

theorem integrable_gd_exp (d : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (gd d u : ℂ) * Complex.exp (z * u)) := by
  refine (((integrable_sub_shift d z).add (integrable_add_shift d z)).div_const 2).congr
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  unfold gd; push_cast; ring

/-! ## 1. The three named Props of the split -/

/-- **(1) `Regularity`** (named premise, NOT proved): Weil's explicit formula
`explicit_formula_even` (in tree for `IsTestFunction` = `C^∞_c`) holds for the `C²_c` even
function `g_d`, conclusion verbatim (absolute summability over the nontrivial zeros, and the
`tsum` equals `weilForm g_d`). -/
def Regularity : Prop := ∀ d : ℝ,
  Summable (fun ρ : GppWeilCriterion.nontrivialZeros =>
      (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ) ∧
    ∑' ρ : GppWeilCriterion.nontrivialZeros,
        (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ =
      (GppArithmeticReflection.weilForm (gd d) : ℂ)

/-- **(2) `Transform`**: `ĝ_d(ρ(γ)) = Ψ(γ)Ψ(−γ) cos(γd)` on the zero set. -/
def Transform : Prop := ∀ d : ℝ, ∀ γ ∈ Zgamma,
  GppMeyerSpectralWeil.spectralTransform (gd d) (rho γ) = efCoeff γ * Complex.cos (γ * d)

/-- **(4) `RightSide`**: `weilForm g_d = Kψ(d)`. -/
def RightSide : Prop := ∀ d : ℝ, GppArithmeticReflection.weilForm (gd d) = Kpsi d

/-! ## 2. (3) cos → exp (PROVED) -/

theorem neg_mem_mult {γ : ℂ} (h : γ ∈ Zgamma) : -γ ∈ Zgamma ∧ mult (-γ) = mult γ := by
  have hρ : rho γ ∈ GppWeilCriterion.nontrivialZeros := h
  obtain ⟨-, -, hc, hcm⟩ := GppXiZeroCounting.zeroData_symmetric hρ
  obtain ⟨hι, hιm, -, -⟩ := GppXiZeroCounting.zeroData_symmetric hc
  have he : GppWeilCriterion.zetaInvolution (conj (rho γ)) = rho (-γ) := by
    rw [rho_neg]; simp [GppWeilCriterion.zetaInvolution]
  refine ⟨Zgamma_neg h, ?_⟩
  unfold mult
  rw [← he, hιm, hcm]

/-- `γ ↦ −γ` on the zero set. -/
noncomputable def negEquiv : Zgamma ≃ Zgamma where
  toFun γ := ⟨-(γ : ℂ), (neg_mem_mult γ.2).1⟩
  invFun γ := ⟨-(γ : ℂ), (neg_mem_mult γ.2).1⟩
  left_inv _ := Subtype.ext (neg_neg _)
  right_inv _ := Subtype.ext (neg_neg _)

theorem efCoeff_neg (γ : ℂ) : efCoeff (-γ) = efCoeff γ := by
  unfold efCoeff; rw [neg_neg, mul_comm]

theorem cos_eq_expTerm (d : ℝ) (γ : ℂ) :
    Complex.cos (γ * d) = (expTerm d γ + expTerm d (-γ)) / 2 := by
  unfold expTerm; rw [Complex.cos]; ring_nf

/-- **(3) PROVED.** The cosine family is summable and has the same sum as the exponential
family (uses `γ ↦ −γ` with equal multiplicity, `Ψ` even, and `hefSumm`). -/
theorem cosToExp (d : ℝ) :
    ZeroSummable (fun γ => efCoeff γ * Complex.cos (γ * d)) ∧
      zeroSum (fun γ => efCoeff γ * Complex.cos (γ * d)) =
        zeroSum (fun γ => efCoeff γ * expTerm d γ) := by
  set F : Zgamma → ℂ := fun γ => (mult (γ : ℂ) : ℂ) * (efCoeff γ * expTerm d γ) with hFd
  have hF : Summable F := hefSumm d
  have hG : Summable (F ∘ negEquiv) := negEquiv.summable_iff.2 hF
  have hGt : ∑' γ, (F ∘ negEquiv) γ = ∑' γ, F γ := negEquiv.tsum_eq F
  have hfun : (fun γ : Zgamma => (mult (γ : ℂ) : ℂ) * (efCoeff γ * Complex.cos (γ * d))) =
      fun γ => (F γ + (F ∘ negEquiv) γ) / 2 := by
    funext γ
    simp only [hFd, Function.comp, negEquiv, Equiv.coe_fn_mk]
    rw [(neg_mem_mult γ.2).2, efCoeff_neg, cos_eq_expTerm]
    ring
  refine ⟨?_, ?_⟩
  · unfold ZeroSummable; rw [hfun]; exact (hF.add hG).div_const 2
  · unfold zeroSum; rw [hfun, tsum_div_const, hF.tsum_add hG, hGt]
    ring

/-- `Zgamma ≃ nontrivialZeros` along `γ ↦ 1/2 + iγ` (index transport, definitional membership). -/
noncomputable def toEquiv : Zgamma ≃ GppWeilCriterion.nontrivialZeros where
  toFun := toRho
  invFun ρ := ⟨-Complex.I * ((ρ : ℂ) - 1 / 2), by
    show rho _ ∈ GppWeilCriterion.nontrivialZeros
    rw [rho_of_s]; exact ρ.2⟩
  left_inv γ := Subtype.ext (by
    show -Complex.I * (rho (γ : ℂ) - 1 / 2) = γ
    unfold rho; ring_nf; rw [Complex.I_sq]; ring)
  right_inv ρ := Subtype.ext (rho_of_s (ρ : ℂ))

/-! ## 3. Assembly `HEFIdent ⇐ (1) + (2) + (4)` (PROVED) -/

theorem hefIdent_of_split (hR : Regularity) (hT : Transform) (hW : RightSide) : HEFIdent := by
  intro d
  obtain ⟨-, hsum⟩ := hR d
  have hre : ∑' ρ : GppWeilCriterion.nontrivialZeros,
      (GppXiZeroCounting.zeroMult ρ : ℂ) * GppMeyerSpectralWeil.spectralTransform (gd d) ρ =
      zeroSum (fun γ => efCoeff γ * Complex.cos (γ * d)) := by
    refine (toEquiv.tsum_eq (fun ρ : GppWeilCriterion.nontrivialZeros =>
      (GppXiZeroCounting.zeroMult ρ : ℂ) *
        GppMeyerSpectralWeil.spectralTransform (gd d) ρ)).symm.trans ?_
    unfold zeroSum
    refine tsum_congr fun γ => ?_
    show (GppXiZeroCounting.zeroMult (rho (γ : ℂ)) : ℂ) *
      GppMeyerSpectralWeil.spectralTransform (gd d) (rho γ) = _
    rw [hT d γ γ.2]
    rfl
  rw [← hW d, ← hsum, hre, (cosToExp d).2]

/-! ## 4. Discharges: (2) and the pole part of (4) reduce to one Fourier identity for `triG` -/

/-- **`TriFourier`**: `∫ triG(v) e^{iγv} dv = Ψ(γ)Ψ(−γ)` for complex `γ ≠ 0`
(`triG = ψ ⋆ ψ`, `ψ̂ = Ψ = (sin(γ/2)/(γ/2))²`; `γ ≠ 0` because `GppKreinLaplace.triPsi 0 = 0`
by Lean's `x/0 = 0`, while the integral there is `1`). -/
def TriFourier : Prop := ∀ γ : ℂ, γ ≠ 0 →
  ∫ v : ℝ, (triG v : ℂ) * Complex.exp (Complex.I * γ * v) = efCoeff γ

theorem ne_zero_of_mem {γ : ℂ} (h : γ ∈ Zgamma) : γ ≠ 0 := fun h0 =>
  Zgamma_re_ne_zero GppNoRealZeroStrip.noRealZeroStrip h (by rw [h0]; rfl)

/-! ## 4a. The Laplace transform of `triG` in closed form (PROVED) -/

theorem hasDerivAt_cubicExp (z : ℂ) (hz : z ≠ 0) (a0 a1 a2 a3 : ℂ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (z * w) *
        ((a0 / z - a1 / z ^ 2 + 2 * a2 / z ^ 3 - 6 * a3 / z ^ 4) +
          (a1 / z - 2 * a2 / z ^ 2 + 6 * a3 / z ^ 3) * w +
          (a2 / z - 3 * a3 / z ^ 2) * w ^ 2 + (a3 / z) * w ^ 3))
      ((a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) * Complex.exp (z * w)) w := by
  have he : HasDerivAt (fun w : ℂ => Complex.exp (z * w)) (Complex.exp (z * w) * z) w := by
    simpa using ((hasDerivAt_id w).const_mul z).cexp
  have hp := (((hasDerivAt_const w (a0 / z - a1 / z ^ 2 + 2 * a2 / z ^ 3 - 6 * a3 / z ^ 4)).add
    ((hasDerivAt_id w).const_mul (a1 / z - 2 * a2 / z ^ 2 + 6 * a3 / z ^ 3))).add
    ((hasDerivAt_pow 2 w).const_mul (a2 / z - 3 * a3 / z ^ 2))).add
    ((hasDerivAt_pow 3 w).const_mul (a3 / z))
  have h := (he.mul hp).congr_deriv (show _ = (a0 + a1 * w + a2 * w ^ 2 + a3 * w ^ 3) *
      Complex.exp (z * w) by
    simp only [Pi.add_apply, id, Nat.cast_ofNat]
    norm_num
    field_simp
    ring)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.mul_apply, id]

/-- `∫_a^b P(v) e^{zv} dv` for a cubic `P`, by the explicit antiderivative. -/
theorem integral_cubicExp (z : ℂ) (hz : z ≠ 0) (a0 a1 a2 a3 : ℂ) (a b : ℝ) :
    ∫ v in a..b, (a0 + a1 * v + a2 * (v : ℂ) ^ 2 + a3 * (v : ℂ) ^ 3) * Complex.exp (z * v) =
      (fun w : ℂ => Complex.exp (z * w) *
        ((a0 / z - a1 / z ^ 2 + 2 * a2 / z ^ 3 - 6 * a3 / z ^ 4) +
          (a1 / z - 2 * a2 / z ^ 2 + 6 * a3 / z ^ 3) * w +
          (a2 / z - 3 * a3 / z ^ 2) * w ^ 2 + (a3 / z) * w ^ 3)) b -
      (fun w : ℂ => Complex.exp (z * w) *
        ((a0 / z - a1 / z ^ 2 + 2 * a2 / z ^ 3 - 6 * a3 / z ^ 4) +
          (a1 / z - 2 * a2 / z ^ 2 + 6 * a3 / z ^ 3) * w +
          (a2 / z - 3 * a3 / z ^ 2) * w ^ 2 + (a3 / z) * w ^ 3)) a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hasDerivAt_cubicExp z hz a0 a1 a2 a3 x).comp_ofReal) ?_
  exact (by fun_prop : Continuous fun v : ℝ =>
    (a0 + a1 * v + a2 * (v : ℂ) ^ 2 + a3 * (v : ℂ) ^ 3) * Complex.exp (z * v)).intervalIntegrable _ _

theorem triG_on1 {v : ℝ} (h : v ∈ Set.uIcc (-2 : ℝ) (-1)) :
    triG v = 4 / 3 + 2 * v + v ^ 2 + v ^ 3 / 6 := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  unfold triG
  rw [abs_of_nonpos (by linarith)]
  split_ifs with a b
  · have : v = -1 := by linarith
    subst this; norm_num
  · ring
  · exact absurd (by linarith : -v ≤ 2) b

theorem triG_on2 {v : ℝ} (h : v ∈ Set.uIcc (-1 : ℝ) 0) :
    triG v = 2 / 3 + 0 * v - v ^ 2 + (-1 / 2) * v ^ 3 := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  unfold triG
  rw [abs_of_nonpos h2, if_pos (by linarith)]
  ring

theorem triG_on3 {v : ℝ} (h : v ∈ Set.uIcc (0 : ℝ) 1) :
    triG v = 2 / 3 + 0 * v - v ^ 2 + (1 / 2) * v ^ 3 := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  unfold triG
  rw [abs_of_nonneg h1, if_pos h2]
  ring

theorem triG_on4 {v : ℝ} (h : v ∈ Set.uIcc (1 : ℝ) 2) :
    triG v = 4 / 3 - 2 * v + v ^ 2 - v ^ 3 / 6 := by
  rw [Set.uIcc_of_le (by norm_num)] at h
  obtain ⟨h1, h2⟩ := h
  unfold triG
  rw [abs_of_nonneg (by linarith)]
  split_ifs with a
  · have : v = 1 := by linarith
    subst this; norm_num
  · ring

/-- **`triLaplace` (PROVED).** For `z ≠ 0`:
`∫ triG(v) e^{zv} dv = (e^{2z} − 4e^{z} + 6 − 4e^{−z} + e^{−2z}) / z⁴`. -/
theorem triLaplace (z : ℂ) (hz : z ≠ 0) :
    ∫ v : ℝ, (triG v : ℂ) * Complex.exp (z * v) =
      (Complex.exp z ^ 2 - 4 * Complex.exp z + 6 - 4 * (Complex.exp z)⁻¹ +
        ((Complex.exp z)⁻¹) ^ 2) / z ^ 4 := by
  set f : ℝ → ℂ := fun v => (triG v : ℂ) * Complex.exp (z * v) with hf
  have hI : Integrable f := integrable_triG_exp z
  have hzero : ∀ v, v ∉ Set.Icc (-2 : ℝ) 2 → f v = 0 := by
    intro v hv
    have hv' : 2 < |v| := by by_contra hc; exact hv (abs_le.1 (not_lt.1 hc))
    simp only [hf, triG_eq_zero hv', Complex.ofReal_zero, zero_mul]
  have hfull : ∫ v, f v = ∫ v in (-2 : ℝ)..2, f v := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have ii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hI.intervalIntegrable
  rw [hfull, ← intervalIntegral.integral_add_adjacent_intervals (ii (-2) (-1)) (ii (-1) 2),
    ← intervalIntegral.integral_add_adjacent_intervals (ii (-1) 0) (ii 0 2),
    ← intervalIntegral.integral_add_adjacent_intervals (ii 0 1) (ii 1 2)]
  have p1 : ∫ v in (-2 : ℝ)..(-1), f v = ∫ v in (-2 : ℝ)..(-1),
      ((4 / 3 : ℂ) + 2 * v + 1 * (v : ℂ) ^ 2 + (1 / 6) * (v : ℂ) ^ 3) * Complex.exp (z * v) :=
    intervalIntegral.integral_congr fun v hv => by
      simp only [hf, triG_on1 hv]; push_cast; ring
  have p2 : ∫ v in (-1 : ℝ)..0, f v = ∫ v in (-1 : ℝ)..0,
      ((2 / 3 : ℂ) + 0 * v + (-1) * (v : ℂ) ^ 2 + (-1 / 2) * (v : ℂ) ^ 3) * Complex.exp (z * v) :=
    intervalIntegral.integral_congr fun v hv => by
      simp only [hf, triG_on2 hv]; push_cast; ring
  have p3 : ∫ v in (0 : ℝ)..1, f v = ∫ v in (0 : ℝ)..1,
      ((2 / 3 : ℂ) + 0 * v + (-1) * (v : ℂ) ^ 2 + (1 / 2) * (v : ℂ) ^ 3) * Complex.exp (z * v) :=
    intervalIntegral.integral_congr fun v hv => by
      simp only [hf, triG_on3 hv]; push_cast; ring
  have p4 : ∫ v in (1 : ℝ)..2, f v = ∫ v in (1 : ℝ)..2,
      ((4 / 3 : ℂ) + (-2) * v + 1 * (v : ℂ) ^ 2 + (-1 / 6) * (v : ℂ) ^ 3) * Complex.exp (z * v) :=
    intervalIntegral.integral_congr fun v hv => by
      simp only [hf, triG_on4 hv]; push_cast; ring
  rw [p1, p2, p3, p4, integral_cubicExp z hz, integral_cubicExp z hz, integral_cubicExp z hz,
    integral_cubicExp z hz]
  have hE : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  have e2 : Complex.exp (z * ((2 : ℝ) : ℂ)) = Complex.exp z ^ 2 := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have e1 : Complex.exp (z * ((1 : ℝ) : ℂ)) = Complex.exp z := by push_cast; rw [mul_one]
  have e0 : Complex.exp (z * ((0 : ℝ) : ℂ)) = 1 := by push_cast; rw [mul_zero, Complex.exp_zero]
  have em1 : Complex.exp (z * ((-1 : ℝ) : ℂ)) = (Complex.exp z)⁻¹ := by
    rw [← Complex.exp_neg]; push_cast; ring_nf
  have em2 : Complex.exp (z * ((-2 : ℝ) : ℂ)) = ((Complex.exp z)⁻¹) ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; push_cast; ring_nf
  simp only []
  rw [e2, e1, e0, em1, em2]
  push_cast
  field_simp
  ring

theorem efCoeff_eq (γ : ℂ) (hγ : γ ≠ 0) :
    efCoeff γ = (Complex.exp (Complex.I * γ) ^ 2 - 4 * Complex.exp (Complex.I * γ) + 6 -
      4 * (Complex.exp (Complex.I * γ))⁻¹ + ((Complex.exp (Complex.I * γ))⁻¹) ^ 2) /
        (Complex.I * γ) ^ 4 := by
  have hT : GppKreinLaplace.triPsi γ = (2 - Complex.exp (Complex.I * γ) -
      (Complex.exp (Complex.I * γ))⁻¹) / γ ^ 2 := by
    unfold GppKreinLaplace.triPsi
    have hsin : Complex.sin (γ / 2) = ((Complex.exp (γ / 2 * Complex.I))⁻¹ -
        Complex.exp (γ / 2 * Complex.I)) * Complex.I / 2 := by
      rw [Complex.sin, ← Complex.exp_neg]; ring_nf
    have hE : Complex.exp (Complex.I * γ) = Complex.exp (γ / 2 * Complex.I) ^ 2 := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hsin, hE]
    have hw : Complex.exp (γ / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring_nf
  unfold efCoeff
  rw [triPsi_neg, hT, mul_pow, Complex.I_pow_four]
  have hE : Complex.exp (Complex.I * γ) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

/-- **`TriFourier` PROVED** (from `triLaplace` at `z = iγ`). -/
theorem triFourier : TriFourier := by
  intro γ hγ
  have hz : Complex.I * γ ≠ 0 := mul_ne_zero Complex.I_ne_zero hγ
  rw [triLaplace _ hz, efCoeff_eq γ hγ]

/-- **(2) from `TriFourier` (PROVED).** -/
theorem transform_of_triFourier (hF : TriFourier) : Transform := by
  intro d γ hγ
  unfold GppMeyerSpectralWeil.spectralTransform
  have hz : rho γ - 1 / 2 = Complex.I * γ := by unfold rho; ring
  rw [hz, integral_gd_exp, hF γ (ne_zero_of_mem hγ), Complex.cos]
  ring_nf

theorem triPsi_I_half : GppKreinLaplace.triPsi (Complex.I / 2) = (bigPsiI2 : ℂ) := by
  unfold GppKreinLaplace.triPsi bigPsiI2
  rw [show Complex.I / 2 / 2 = ((1 / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]
  push_cast
  field_simp
  ring

theorem efCoeff_I_half : efCoeff (Complex.I / 2) = (bigPsiI2 : ℂ) ^ 2 := by
  unfold efCoeff; rw [triPsi_neg, triPsi_I_half]; ring

/-- Pole part of (4). -/
def PoleMatch : Prop := ∀ d : ℝ, GppArithmeticReflection.poleTerm (gd d) = poleTerm d

/-- **Pole part of (4) from `TriFourier` (PROVED).**
`∫ g_d(u) 2cosh(u/2) du = 2 Ψ(i/2)² cosh(d/2)`. -/
theorem poleMatch_of_triFourier (hF : TriFourier) : PoleMatch := by
  intro d
  have e1 : ∫ v : ℝ, (triG v : ℂ) * Complex.exp ((1 / 2 : ℂ) * v) = (bigPsiI2 : ℂ) ^ 2 := by
    have := hF (-(Complex.I / 2)) (by simp)
    rw [show Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) by ring_nf; rw [Complex.I_sq]; ring,
      efCoeff_neg, efCoeff_I_half] at this
    exact this
  have e2 : ∫ v : ℝ, (triG v : ℂ) * Complex.exp ((-1 / 2 : ℂ) * v) = (bigPsiI2 : ℂ) ^ 2 := by
    have := hF (Complex.I / 2) (by simp)
    rw [show Complex.I * (Complex.I / 2) = (-1 / 2 : ℂ) by ring_nf; rw [Complex.I_sq]; ring,
      efCoeff_I_half] at this
    exact this
  apply Complex.ofReal_injective
  unfold GppArithmeticReflection.poleTerm
  rw [← integral_complex_ofReal]
  have hsplit : (fun u : ℝ => ((gd d u * (2 * Real.cosh (u / 2)) : ℝ) : ℂ)) = fun u =>
      (gd d u : ℂ) * Complex.exp ((1 / 2 : ℂ) * u) +
        (gd d u : ℂ) * Complex.exp ((-1 / 2 : ℂ) * u) := by
    funext u; push_cast; rw [Complex.cosh]; ring_nf
  rw [hsplit, integral_add (integrable_gd_exp d _) (integrable_gd_exp d _), integral_gd_exp,
    integral_gd_exp, e1, e2]
  unfold poleTerm
  push_cast
  rw [Complex.cosh]
  ring_nf

/-- **Prime part of (4) PROVED** (termwise, `triG` even). -/
theorem primeMatch (d : ℝ) : GppWeilLadder.primeSide (gd d) = primeTerm d := by
  unfold GppWeilLadder.primeSide primeTerm
  refine tsum_congr fun n => ?_
  unfold gd
  rw [show -Real.log (n : ℝ) - d = -(Real.log n + d) by ring,
    show Real.log (n : ℝ) - d = -(-Real.log n + d) by ring, triG_neg, triG_neg]
  ring

/-- Archimedean part of (4) (named premise, NOT proved): the physical form of the real-place
term on `g_d` equals the frequency form `archTerm d`. -/
def ArchMatch : Prop := ∀ d : ℝ, GppArchimedeanFloor.archimedeanTerm (gd d) = archTerm d

/-- **(4) from its parts (PROVED).** -/
theorem rightSide_of_parts (hP : PoleMatch) (hA : ArchMatch) : RightSide := by
  intro d
  unfold GppArithmeticReflection.weilForm Kpsi
  rw [hP d, hA d, primeMatch d]
  ring

/-! ## 5. What is discharged, what remains, and the chain -/

/-- **(2) `Transform` PROVED** (unconditional). -/
theorem transform : Transform := transform_of_triFourier triFourier

/-- **Pole part of (4) PROVED** (unconditional). -/
theorem poleMatch : PoleMatch := poleMatch_of_triFourier triFourier

/-- **(4) `RightSide` from `ArchMatch` alone (PROVED).** -/
theorem rightSide_of_arch (hA : ArchMatch) : RightSide := rightSide_of_parts poleMatch hA

/-- **`HEFIdent` from the two remaining named premises (PROVED).** -/
theorem hefIdent_of_reg_arch (hR : Regularity) (hA : ArchMatch) : HEFIdent :=
  hefIdent_of_split hR transform (rightSide_of_arch hA)

/-- The fine chain with `HEFIdent` split. Remaining premises: `HPsi`, `Regularity`, `ArchMatch`,
`KreinDecomp`, `IdentityStep`. -/
def HPsiRegArchChain : Prop :=
  GppKreinHPsi.HPsi → Regularity → ArchMatch → KreinDecomp →
    GppSpectralMatchingSplit.IdentityStep → RiemannHypothesis

theorem hPsiRegArchChain : HPsiRegArchChain := fun h hR hA hD hI =>
  GppSpectralMatchingSplit.hPsiIdentityChain h (hef_of_ident (hefIdent_of_reg_arch hR hA)) hD hI

end GppHEFIdentSplit

#print axioms GppHEFIdentSplit.triG_neg
#print axioms GppHEFIdentSplit.gd_even
#print axioms GppHEFIdentSplit.triG_measurable
#print axioms GppHEFIdentSplit.triG_eq_zero
#print axioms GppHEFIdentSplit.abs_triG_le
#print axioms GppHEFIdentSplit.integrable_triG_exp
#print axioms GppHEFIdentSplit.integrable_sub_shift
#print axioms GppHEFIdentSplit.integrable_add_shift
#print axioms GppHEFIdentSplit.integral_gd_exp
#print axioms GppHEFIdentSplit.integrable_gd_exp
#print axioms GppHEFIdentSplit.neg_mem_mult
#print axioms GppHEFIdentSplit.efCoeff_neg
#print axioms GppHEFIdentSplit.cos_eq_expTerm
#print axioms GppHEFIdentSplit.cosToExp
#print axioms GppHEFIdentSplit.hefIdent_of_split
#print axioms GppHEFIdentSplit.ne_zero_of_mem
#print axioms GppHEFIdentSplit.hasDerivAt_cubicExp
#print axioms GppHEFIdentSplit.integral_cubicExp
#print axioms GppHEFIdentSplit.triG_on1
#print axioms GppHEFIdentSplit.triG_on2
#print axioms GppHEFIdentSplit.triG_on3
#print axioms GppHEFIdentSplit.triG_on4
#print axioms GppHEFIdentSplit.triLaplace
#print axioms GppHEFIdentSplit.efCoeff_eq
#print axioms GppHEFIdentSplit.triFourier
#print axioms GppHEFIdentSplit.transform_of_triFourier
#print axioms GppHEFIdentSplit.triPsi_I_half
#print axioms GppHEFIdentSplit.efCoeff_I_half
#print axioms GppHEFIdentSplit.poleMatch_of_triFourier
#print axioms GppHEFIdentSplit.primeMatch
#print axioms GppHEFIdentSplit.rightSide_of_parts
#print axioms GppHEFIdentSplit.transform
#print axioms GppHEFIdentSplit.poleMatch
#print axioms GppHEFIdentSplit.rightSide_of_arch
#print axioms GppHEFIdentSplit.hefIdent_of_reg_arch
#print axioms GppHEFIdentSplit.hPsiRegArchChain
