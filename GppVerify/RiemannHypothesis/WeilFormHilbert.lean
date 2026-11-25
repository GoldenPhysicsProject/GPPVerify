/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.BNBilinear
import GppVerify.RiemannHypothesis.InstantiatedFromRH

/-!
# The arithmetic Hilbert space: the completion of test functions under the Weil form

The full Weil form `weilForm = poleTerm + archimedeanTerm - primeSide` is linear on the test class
(`weil_add`, `weil_smul`: the prime side is a finite sum on compactly supported functions). Its
symmetrised polarization on cross-correlations

  `weilBilFun f g = (weilForm (f ⋆ g̃) + weilForm (g ⋆ f̃)) / 2`

is a symmetric bilinear form on the real vector space `testSubmodule` of smooth compactly supported
functions with diagonal `weilBilFun f f = weilForm (autocorr f)` (`weilBilFun_self`) and is
invariant under simultaneous translation (`weilBilFun_shift`).

No zero of `ζ` occurs in any definition here. Given arithmetic reflection positivity (the
hypothesis `harp`, equivalent to every zero lying on `Re = 1/2` by `arp_iff_rh_strip`), the form is
positive semidefinite and `exists_hilbert_weil` realizes it as a Gram form in a real Hilbert space
with dense range; `exists_hilbert_weil_of_riemannHypothesis` instantiates the hypothesis from
Mathlib's `RiemannHypothesis`.
-/

open MeasureTheory Set GppArithmeticReflection GppShiftPresentation GppMeyerSpectralWeil
  GppWeilLadder GppArchimedeanFloor
open scoped ContDiff

noncomputable section

namespace GppWeilHilbert

/-- The real vector space of smooth compactly supported test functions. -/
def testSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsTestFunction f}
  add_mem' := fun {_ _} hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hf => ⟨hf.1.const_smul c, hf.2.smul_left⟩

theorem exists_supportIn {f : ℝ → ℝ} (hf : HasCompactSupport f) : ∃ L : ℝ, HasSupportIn f L := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun x hx => ?_⟩
  by_contra hne
  have : x ∈ tsupport f := subset_tsupport f hne
  have := hR this
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

theorem summable_primeSide_terms {a : ℝ → ℝ} (ha : HasCompactSupport a) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      (a (Real.log n) + a (-(Real.log n)))) := by
  obtain ⟨L, hL⟩ := exists_supportIn ha
  refine summable_of_finite_support ?_
  refine (Set.finite_Iic ⌈Real.exp L⌉₊).subset ?_
  intro n hn
  by_contra hlt
  simp only [mem_Iic, not_le] at hlt
  apply hn
  exact primeSide_term_eq_zero hL (by
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
    have : Real.exp L < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    rwa [← Real.exp_lt_exp, Real.exp_log (by exact_mod_cast hn0)])

theorem primeSide_add {a b : ℝ → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b) :
    primeSide (a + b) = primeSide a + primeSide b := by
  unfold primeSide
  rw [← Summable.tsum_add (summable_primeSide_terms ha.2) (summable_primeSide_terms hb.2)]
  refine tsum_congr (fun n => ?_)
  simp only [Pi.add_apply]; ring

theorem primeSide_smul (c : ℝ) (a : ℝ → ℝ) : primeSide (c • a) = c * primeSide a := by
  unfold primeSide
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem weil_add {a b : ℝ → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b) :
    weilForm (a + b) = weilForm a + weilForm b := by
  unfold weilForm
  rw [poleTerm_add ha hb, archimedeanTerm_add ha hb, primeSide_add ha hb]; ring

theorem weil_smul (c : ℝ) (a : ℝ → ℝ) : weilForm (c • a) = c * weilForm a := by
  unfold weilForm
  rw [poleTerm_smul, archimedeanTerm_smul, primeSide_smul]; ring

/-- The symmetrised polarization of the Weil form. -/
def weilBilFun (f g : ℝ → ℝ) : ℝ := (weilForm (xcorr f g) + weilForm (xcorr g f)) / 2

theorem weilBilFun_symm (f g : ℝ → ℝ) : weilBilFun f g = weilBilFun g f := by
  unfold weilBilFun; ring

theorem weilBilFun_self (f : ℝ → ℝ) : weilBilFun f f = weilForm (autocorr f) := by
  unfold weilBilFun; rw [xcorr_self]; ring

theorem weilBilFun_add_left {f₁ f₂ g : ℝ → ℝ} (h₁ : IsTestFunction f₁) (h₂ : IsTestFunction f₂)
    (hg : IsTestFunction g) : weilBilFun (f₁ + f₂) g = weilBilFun f₁ g + weilBilFun f₂ g := by
  unfold weilBilFun
  rw [xcorr_add_left h₁ h₂ hg, xcorr_add_right hg h₁ h₂,
    weil_add (isTestFunction_xcorr h₁ hg) (isTestFunction_xcorr h₂ hg),
    weil_add (isTestFunction_xcorr hg h₁) (isTestFunction_xcorr hg h₂)]
  ring

theorem weilBilFun_smul_left (c : ℝ) (f g : ℝ → ℝ) :
    weilBilFun (c • f) g = c * weilBilFun f g := by
  unfold weilBilFun
  rw [xcorr_smul_left, xcorr_smul_right, weil_smul, weil_smul]; ring

/-- **The Weil form as a symmetric bilinear form on test functions.** -/
def weilBilin : testSubmodule →ₗ[ℝ] testSubmodule →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => weilBilFun f.1 g.1)
    (fun f₁ f₂ g => weilBilFun_add_left f₁.2 f₂.2 g.2)
    (fun c f g => by rw [smul_eq_mul]; exact weilBilFun_smul_left c f.1 g.1)
    (fun f g₁ g₂ => by
      rw [weilBilFun_symm, show ((g₁ + g₂ : testSubmodule) : ℝ → ℝ) = g₁.1 + g₂.1 from rfl,
        weilBilFun_add_left g₁.2 g₂.2 f.2, weilBilFun_symm g₁.1, weilBilFun_symm g₂.1])
    (fun c f g => by
      rw [weilBilFun_symm, show ((c • g : testSubmodule) : ℝ → ℝ) = c • g.1 from rfl,
        weilBilFun_smul_left, weilBilFun_symm, smul_eq_mul])

theorem weilBilin_apply (f g : testSubmodule) : weilBilin f g = weilBilFun f.1 g.1 := rfl

theorem weilBilin_self (f : testSubmodule) : weilBilin f f = weilForm (autocorr f.1) :=
  weilBilFun_self f.1

/-- Positive semidefiniteness of the Weil form, from arithmetic reflection positivity. -/
theorem psd_weilBilin (harp : ArithmeticReflectionPositivity) : GppFormGNS.PSD weilBilin where
  symm f g := weilBilFun_symm f.1 g.1
  nonneg f := by rw [weilBilin_self]; exact harp f.1 f.2.1 f.2.2

/-- **The arithmetic Hilbert space.** Given arithmetic reflection positivity, a real Hilbert space
`H` and a linear `ι` from test functions with dense range and `weilBilFun f g = ⟪ι f, ι g⟫`. No zero
of `ζ` is used in the construction. -/
theorem exists_hilbert_weil (harp : ArithmeticReflectionPositivity) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : testSubmodule →ₗ[ℝ] H),
      (∀ f g : testSubmodule, weilBilFun f.1 g.1 = inner ℝ (ι f) (ι g)) ∧ DenseRange ι :=
  GppFormGNS.exists_hilbert_of_psd (psd_weilBilin harp)

/-- The same, from Mathlib's `RiemannHypothesis`. -/
theorem exists_hilbert_weil_of_riemannHypothesis (h : RiemannHypothesis) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (ι : testSubmodule →ₗ[ℝ] H),
      (∀ f g : testSubmodule, weilBilFun f.1 g.1 = inner ℝ (ι f) (ι g)) ∧ DenseRange ι :=
  exists_hilbert_weil (GppInstantiated.arp h)

/-! ## Translation invariance -/

theorem xcorr_shift (t : ℝ) (f g : ℝ → ℝ) :
    xcorr (GppZeroHilbert.shift t f) (GppZeroHilbert.shift t g) = xcorr f g := by
  funext x
  unfold xcorr GppZeroHilbert.shift
  have := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => f y * g (y - x)) t
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  congr 2; ring

/-- **The Weil form is invariant under simultaneous translation of the log variable.** -/
theorem weilBilFun_shift (t : ℝ) (f g : ℝ → ℝ) :
    weilBilFun (GppZeroHilbert.shift t f) (GppZeroHilbert.shift t g) = weilBilFun f g := by
  unfold weilBilFun; rw [xcorr_shift, xcorr_shift]

end GppWeilHilbert

#print axioms GppWeilHilbert.weil_add
#print axioms GppWeilHilbert.psd_weilBilin
#print axioms GppWeilHilbert.exists_hilbert_weil
#print axioms GppWeilHilbert.exists_hilbert_weil_of_riemannHypothesis
#print axioms GppWeilHilbert.weilBilFun_shift
