/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6825368446, "next exact question".

# `HEF` split: summability (PROVED) + the explicit-formula identity (named premise)

`KreinPoleSplit.HEF` bundles two statements for every `d`:

* `HEFSumm` — the multiplicity-weighted family `γ ↦ m_γ Ψ(γ)Ψ(−γ) e^{iγd}` is summable over
  `Zgamma`;
* `HEFIdent` — `Kψ(d) = Σ_γ m_γ Ψ(γ)Ψ(−γ) e^{iγd}` (the `tsum`).

PROVED here:

* `hef_of_split : HEFSumm → HEFIdent → HEF` (assembly) and `hef_iff_split` (both directions).
* `hefSumm : HEFSumm` — **unconditionally, from files on the branch**. Proof: on the strip
  `|Im γ| < 1/2`, `‖Ψ(γ)‖ ≤ 144 (1+‖γ‖)^{-2}` (`‖sin z‖ ≤ 2‖z‖` for `‖z‖ ≤ 1` from
  `Complex.norm_exp_sub_one_le`, and `‖sin z‖ ≤ e^{|Im z|} < 3`), `‖e^{iγd}‖ ≤ e^{|d|/2}`, and
  `Σ_ρ m_ρ (1+‖ρ‖)^{-4} < ∞` (Jensen + order ≤ 2 of ξ; the proof of
  `GppXiZeroCounting.zeroCountingPolynomial`, re-run here as `zeroCounting_four` because that
  theorem exports only `∃ N`). Transfer `Zgamma → nontrivialZeros` along `γ ↦ 1/2 + iγ`.
* `hef_of_ident : HEFIdent → HEF` and
  `hPsiIdentChain : HPsi → HEFIdent → KreinDecomp → SpectralMatching → RiemannHypothesis`.

Named premise, NOT proved: `HEFIdent`. Paper: Weil's explicit formula for the compactly
supported test function `g = ψ * ψ̃` translated by `d` (CHECKED, secondary: Connes
arXiv:1509.05576 §2.1.1 citing Weil); NUMERICAL to 1.02e−8 (`hef_tri.py`, GPPDiscovery5).
Lean blocker (genuinely open analysis, not in Mathlib): the contour-shift input, i.e. a
partial-fraction / horizontal-segment bound for `ζ'/ζ` — there are `T_k → ∞` with
`sup_{−1 ≤ σ ≤ 2} ‖ζ'/ζ(σ + i T_k)‖ ≤ C log² T_k` — together with the resulting
`(1/2πi)∮ (ζ'/ζ) · ĝ` residue identity.

Honesty check: `HEFSumm` is unconditional (proved). `HEFIdent` is not derived from RH and is not
claimed to follow from it: RH fixes the location of zeros, while `HEFIdent` is an identity
between a zero sum and a prime/Γ expression that holds unconditionally on paper; RH supplies
neither the contour bound nor the residue computation.
H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinRepSplit

namespace GppKreinHEFSplit

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit GppKreinRepSplit
  ComplexConjugate

/-! ## 1. The two sub-premises and the assembly -/

/-- **`HEFSumm`**: summability of the explicit-formula zero family at every `d`. -/
def HEFSumm : Prop := ∀ d : ℝ, ZeroSummable (fun γ => efCoeff γ * expTerm d γ)

/-- **`HEFIdent`** (named premise): the explicit-formula identity at every `d`. -/
def HEFIdent : Prop :=
  ∀ d : ℝ, ((Kpsi d : ℝ) : ℂ) = zeroSum (fun γ => efCoeff γ * expTerm d γ)

theorem hef_of_split (hS : HEFSumm) (hI : HEFIdent) : HEF := fun d => ⟨hS d, hI d⟩

theorem hef_iff_split : HEF ↔ HEFSumm ∧ HEFIdent :=
  ⟨fun h => ⟨fun d => (h d).1, fun d => (h d).2⟩, fun h => hef_of_split h.1 h.2⟩

/-! ## 2. Pointwise bounds on the strip -/

theorem norm_sin_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.sin z‖ ≤ 2 * ‖z‖ := by
  have e1 : ‖-z * Complex.I‖ = ‖z‖ := by simp
  have e2 : ‖z * Complex.I‖ = ‖z‖ := by simp
  have h1 := Complex.norm_exp_sub_one_le (x := -z * Complex.I) (by rw [e1]; exact hz)
  have h2 := Complex.norm_exp_sub_one_le (x := z * Complex.I) (by rw [e2]; exact hz)
  rw [e1] at h1; rw [e2] at h2
  have hs : Complex.sin z = ((Complex.exp (-z * Complex.I) - 1) -
      (Complex.exp (z * Complex.I) - 1)) * Complex.I / 2 := by
    rw [Complex.sin]; ring_nf
  rw [hs, norm_div, norm_mul, Complex.norm_I, mul_one]
  have : ‖(Complex.exp (-z * Complex.I) - 1) - (Complex.exp (z * Complex.I) - 1)‖ ≤ 4 * ‖z‖ :=
    (norm_sub_le _ _).trans (by linarith)
  simp only [Complex.norm_ofNat]
  linarith

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hs : Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) *
      Complex.I / 2 := by rw [Complex.sin]
  have a1 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp; exact le_abs_self _
  have a2 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp; exact neg_le_abs _
  rw [hs, norm_div, norm_mul, Complex.norm_I, mul_one]
  simp only [Complex.norm_ofNat]
  have := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  linarith

theorem norm_sinc_le {z : ℂ} (hz : |z.im| ≤ 1 / 4) :
    ‖Complex.sin z / z‖ ≤ 6 / (1 + ‖z‖) := by
  have hn := norm_nonneg z
  rcases le_or_gt ‖z‖ 1 with h | h
  · rcases eq_or_ne z 0 with h0 | h0
    · subst h0; simp
    · have hp : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [norm_div, div_le_div_iff₀ hp (by positivity)]
      have := norm_sin_le_two_mul h
      nlinarith
  · have hp : 0 < ‖z‖ := by linarith
    have hexp : Real.exp |z.im| ≤ 3 := by
      have := Real.exp_one_lt_d9
      have : Real.exp |z.im| ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      linarith
    have := (norm_sin_le_exp z).trans hexp
    rw [norm_div, div_le_div_iff₀ hp (by positivity)]
    nlinarith

theorem im_lt_of_mem {γ : ℂ} (h : γ ∈ Zgamma) : |γ.im| < 1 / 2 := by
  obtain ⟨-, h0, h1⟩ := h
  rw [rho_re] at h0 h1
  rw [abs_lt]; constructor <;> linarith

theorem norm_triPsi_le {γ : ℂ} (h : |γ.im| ≤ 1 / 2) :
    ‖GppKreinLaplace.triPsi γ‖ ≤ 144 / (1 + ‖γ‖) ^ 2 := by
  unfold GppKreinLaplace.triPsi
  have hz : |(γ / 2).im| ≤ 1 / 4 := by
    rw [Complex.div_ofNat_im, abs_div]; norm_num; linarith
  have hb := norm_sinc_le hz
  have hn : ‖γ / 2‖ = ‖γ‖ / 2 := by rw [norm_div]; simp
  rw [hn] at hb
  have hg := norm_nonneg γ
  have hb' : ‖Complex.sin (γ / 2) / (γ / 2)‖ ≤ 12 / (1 + ‖γ‖) := by
    refine hb.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [norm_pow]
  calc ‖Complex.sin (γ / 2) / (γ / 2)‖ ^ 2 ≤ (12 / (1 + ‖γ‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb' 2
    _ = 144 / (1 + ‖γ‖) ^ 2 := by rw [div_pow]; norm_num

theorem norm_expTerm_le (d : ℝ) {γ : ℂ} (h : |γ.im| ≤ 1 / 2) :
    ‖expTerm d γ‖ ≤ Real.exp (|d| / 2) := by
  unfold expTerm
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (Complex.I * γ * (d : ℂ)).re = -(γ.im * d) := by simp [Complex.mul_re]
  rw [this]
  have h1 : |γ.im * d| ≤ |d| / 2 := by
    rw [abs_mul]; nlinarith [abs_nonneg d, abs_nonneg γ.im]
  linarith [neg_abs_le (γ.im * d), neg_le_abs (γ.im * d)]

/-! ## 3. Zero counting with exponent 4 (proof of `zeroCountingPolynomial`, re-run with `N = 4`) -/

open GppLogDerivZeroFree GppXiZeroCounting in
theorem zeroCounting_four :
    Summable (fun ρ : GppWeilCriterion.nontrivialZeros =>
      (zeroMult ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ 4)⁻¹) := by
  obtain ⟨A, B, hB, hcount⟩ := sum_zeroMult_le
  let ι := Σ ρ : GppWeilCriterion.nontrivialZeros, Fin (zeroMult ρ)
  let a : ι → ℝ := fun i => 1 + ‖(i.1 : ℂ)‖
  have hpos : ∀ i, 0 < a i := fun i => by simp only [a]; positivity
  have hZfin : ∀ r : ℝ, {ρ : GppWeilCriterion.nontrivialZeros | ‖(ρ : ℂ)‖ ≤ r}.Finite := by
    intro r
    by_cases hr : 0 < r
    · have hfin := (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)).finiteSupport
        (isCompact_closedBall 0 r)
      refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
      refine hfin.subset ?_
      rintro _ ⟨ρ, hρ, rfl⟩
      have hmem : (ρ : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by simpa using hρ
      rw [Function.mem_support, divisor_xi_apply hmem, ← zeroMult_eq_orderNat_xi ρ.2]
      have := one_le_zeroMult ρ.2
      omega
    · refine (Set.finite_empty).subset ?_
      intro ρ hρ
      exfalso
      have : ‖(ρ : ℂ)‖ ≤ r := hρ
      have hρ0 : (ρ : ℂ) ≠ 0 := fun h => by
        have := ρ.2.2.1; simp [h] at this
      have := norm_pos_iff.2 hρ0
      exact hr (lt_of_lt_of_le this ‹_›)
  have hfin : ∀ r : ℝ, {i : ι | a i ≤ r}.Finite := by
    intro r
    refine ((hZfin (r - 1)).biUnion (fun ρ _ => Set.finite_range (Sigma.mk ρ))).subset ?_
    intro i hi
    have : ‖(i.1 : ℂ)‖ ≤ r - 1 := by have : a i ≤ r := hi; simp only [a] at this; linarith
    exact Set.mem_biUnion (x := i.1) this ⟨i.2, rfl⟩
  have hcard : ∀ r : ℝ, 0 < r →
      (((hfin r).toFinset.card : ℕ) : ℝ) ≤ A + B * r ^ ((2 : ℝ) + 1) := by
    intro r hr
    set Tf := (hZfin (r - 1)).toFinset with hTf
    have hsub : (hfin r).toFinset ⊆
        Tf.sigma (fun ρ => (Finset.univ : Finset (Fin (zeroMult ρ)))) := by
      intro i hi
      have hi' : a i ≤ r := (hfin r).mem_toFinset.1 hi
      have : ‖(i.1 : ℂ)‖ ≤ r - 1 := by simp only [a] at hi'; linarith
      exact Finset.mem_sigma.2 ⟨(hZfin (r - 1)).mem_toFinset.2 this, Finset.mem_univ _⟩
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_sigma] at hc1
    simp only [Finset.card_univ, Fintype.card_fin] at hc1
    set T : Finset ℂ := Tf.image Subtype.val with hT
    have hsumT : ∑ ρ ∈ T, zeroMult ρ = ∑ ρ ∈ Tf, zeroMult (ρ : ℂ) :=
      Finset.sum_image (fun x _ y _ h => Subtype.val_injective h)
    have hbound := hcount r hr T (by
      intro ρ hρ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
      refine ⟨x.2, ?_⟩
      have := (hZfin (r - 1)).mem_toFinset.1 hx
      have : ‖(x : ℂ)‖ ≤ r - 1 := this
      linarith)
    refine le_trans ?_ hbound
    rw [hsumT]
    exact_mod_cast hc1
  have hsum := Real.summable_inv_pow_of_counting_le hpos hfin hB (by norm_num : (0:ℝ) ≤ 2 + 1)
    (m := 4) (by norm_num) hcard
  have hfib := hsum.sigma
  refine hfib.congr (fun ρ => ?_)
  simp only [a, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [inv_pow]

/-! ## 4. `HEFSumm` PROVED -/

/-- `γ ↦ ρ(γ)` from `Zgamma` into the nontrivial zeros (definitionally the same membership). -/
noncomputable def toRho (γ : Zgamma) : GppWeilCriterion.nontrivialZeros := ⟨rho γ, γ.2⟩

theorem toRho_injective : Function.Injective toRho := by
  intro x y h
  have h' : rho (x : ℂ) = rho (y : ℂ) := congrArg Subtype.val h
  unfold rho at h'
  exact Subtype.ext (mul_left_cancel₀ Complex.I_ne_zero (add_left_cancel h'))

theorem one_add_norm_rho_le (γ : ℂ) : 2 * (1 + ‖rho γ‖) ≤ 3 * (1 + ‖γ‖) := by
  have : ‖rho γ‖ ≤ 1 / 2 + ‖γ‖ := by
    unfold rho
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]; norm_num
  have := norm_nonneg γ
  linarith

/-- **`HEFSumm` PROVED** (unconditional). -/
theorem hefSumm : HEFSumm := by
  intro d
  have hz := zeroCounting_four.comp_injective toRho_injective
  have hz' := hz.mul_left (144 ^ 2 * (81 / 16) * Real.exp (|d| / 2))
  refine Summable.of_norm_bounded hz' (fun γ => ?_)
  have him := (im_lt_of_mem γ.2).le
  have hT := norm_triPsi_le him
  have hE := norm_expTerm_le d him
  have hR := one_add_norm_rho_le (γ : ℂ)
  simp only [Function.comp, toRho]
  unfold efCoeff
  rw [triPsi_neg, norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  have hmeq : (GppXiZeroCounting.zeroMult (rho (γ : ℂ)) : ℝ) = (mult (γ : ℂ) : ℝ) := rfl
  rw [hmeq]
  set m : ℝ := (mult (γ : ℂ) : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set t := ‖GppKreinLaplace.triPsi (γ : ℂ)‖
  set e := ‖expTerm d (γ : ℂ)‖
  set G := 1 + ‖(γ : ℂ)‖
  set R := 1 + ‖rho (γ : ℂ)‖
  have hG : 0 < G := by positivity
  have hRp : 0 < R := by positivity
  have ht : 0 ≤ t := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have htt : t * t ≤ 144 ^ 2 * (81 / 16) * (R ^ 4)⁻¹ := by
    have h1 : t * t ≤ (144 / G ^ 2) * (144 / G ^ 2) := mul_le_mul hT hT ht (by positivity)
    refine h1.trans ?_
    have hRG : (2 * R) ^ 4 ≤ (3 * G) ^ 4 := pow_le_pow_left₀ (by positivity) hR 4
    have hR4 : 0 < R ^ 4 := by positivity
    have hG4 : 0 < G ^ 4 := by positivity
    rw [show (144 / G ^ 2) * (144 / G ^ 2) = 144 ^ 2 / G ^ 4 by ring_nf,
      show 144 ^ 2 * (81 / 16) * (R ^ 4)⁻¹ = 144 ^ 2 * 81 / (16 * R ^ 4) by field_simp,
      div_le_div_iff₀ hG4 (by positivity)]
    nlinarith [hRG]
  calc m * (t * t * e) ≤ m * (144 ^ 2 * (81 / 16) * (R ^ 4)⁻¹ * Real.exp (|d| / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hm
        exact mul_le_mul htt hE he (by positivity)
    _ = 144 ^ 2 * (81 / 16) * Real.exp (|d| / 2) * (m * (R ^ 4)⁻¹) := by ring

/-! ## 5. `HEF` from the identity alone, and the chain -/

theorem hef_of_ident (hI : HEFIdent) : HEF := hef_of_split hefSumm hI

/-- The chain with `HEF` reduced to its identity component. -/
def HPsiIdentChain : Prop :=
  HPsi → HEFIdent → KreinDecomp → SpectralMatching → RiemannHypothesis

theorem hPsiIdentChain : HPsiIdentChain := fun h hI hD hM =>
  hPsiFineChain h (hef_of_ident hI) hD hM

end GppKreinHEFSplit

#print axioms GppKreinHEFSplit.hef_of_split
#print axioms GppKreinHEFSplit.hef_iff_split
#print axioms GppKreinHEFSplit.norm_sin_le_two_mul
#print axioms GppKreinHEFSplit.norm_sin_le_exp
#print axioms GppKreinHEFSplit.norm_sinc_le
#print axioms GppKreinHEFSplit.im_lt_of_mem
#print axioms GppKreinHEFSplit.norm_triPsi_le
#print axioms GppKreinHEFSplit.norm_expTerm_le
#print axioms GppKreinHEFSplit.zeroCounting_four
#print axioms GppKreinHEFSplit.toRho_injective
#print axioms GppKreinHEFSplit.one_add_norm_rho_le
#print axioms GppKreinHEFSplit.hefSumm
#print axioms GppKreinHEFSplit.hef_of_ident
#print axioms GppKreinHEFSplit.hPsiIdentChain
