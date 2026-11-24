/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.KernelTheory
import GppVerify.RiemannHypothesis.GravitonDeltaIdentification
import GppVerify.RiemannHypothesis.CasimirCriticalLine
import GppVerify.RiemannHypothesis.XiReflection

/-!
# BT-Σ spectral transform: Mellin/Tate Casimir diagonalisation, RP ⇔ principal series,
# ARP ⇔ RH strip, `UnitaryRealization` ⇔ ARP

Lean port (Heart of the Cosmos / Grok, GPPDiscovery5 seat) of §2–§3 of GPPDiscovery5 `65ff9c2`
(`lean/s-eq-delta/SEqDelta1d.lean`), plus the two §4 statements `gram_eq_weilForm` and
`unitaryRealization_iff_arp`, as requested by Turbo on GPP-bridge PR #11, comment 6816451142.

## What is ported (all PROVED, standard axioms)
* §1 dictionary pieces used below: `shadow`, `shadow_eq_conj_iff` (`d - Δ = Δ̄ ↔ Re Δ = d/2`),
  `one_sub_eq_conj_iff` (the `d = 1` case `1 - ρ = conj ρ ↔ Re ρ = 1/2`).
* §2 Tate/Mellin data vs the principal series:
  `spectralTransform_conj` (real tests: `conj Ψg(s) = Ψg(s̄)`), `reflect_eq_conj_on_line`
  (`Ψ(Θg)(s) = conj Ψg(s)` on `Re s = 1/2`), `melChar` with `hasDerivAt_exp_mul`,
  `melChar_casimir` (`χ/4 - χ'' = s(1-s) χ`), `melChar_unitary_iff` (`|χ_s| ≡ 1 ↔ Re s = 1/2`),
  `spectralTransform_deriv` (`Ψ_{g'} = -(s - 1/2) Ψ_g`, integration by parts) and
  `spectralTransform_casimir` (`Ψ_{g/4 - g''}(s) = s(1-s) Ψ_g(s)`, every `s`: kinematics, not
  zero location).
* §3 theorem about theories, converse direction:
  `KernelTheory'.reflectionPositive_of_principalSeries`,
  `KernelTheory'.reflectionPositive_iff_principalSeries`, `zetaTheory_conj`,
  `arp_iff_rh_strip` (ARP ↔ every nontrivial zero has `Re = 1/2`; an equivalence of statements,
  neither side asserted), `riemannHypothesis_of_strip` (strip form ⇒ Mathlib `RiemannHypothesis`).
* `gram_eq_weilForm` (the ζ Gram form is the Weil form of the autocorrelation, in-tree GW-EF-1/2),
  `UnitaryRealization` (named hypothesis Prop: a Hilbert space with states `O f` whose norms are
  the ζ Gram form) and `unitaryRealization_iff_arp` (it is exactly ARP).

## What is NOT ported (stays in GPPDiscovery5)
`SEqDelta1d`, `ArithmeticPrincipalSeriesCFT`, `ShadowIsAdjointOnSpectrum` (the GAP),
`PrincipalCasimirRealization`, `gap_equivalences`, `rh_of_s_eq_delta`, `arp_of_s_eq_delta`,
`gap_of_principalCasimirRealization`.

## Labels
Every theorem here is PROVED (standard axioms only, no `sorry`, no `axiom`, no stub).
`UnitaryRealization` is a named hypothesis Prop: OPEN (equivalent to ARP).
ARP OPEN. RH OPEN. The GAP (`ShadowIsAdjointOnSpectrum`) stays in GPPDiscovery5, OPEN.

Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo.
-/

open Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefAssembly
  GppKernelTheory GppCasimirCriticalLine

noncomputable section

namespace GppBTSigmaSpectralTransform

/-! ## §1 Dictionary pieces used below -/

/-- The `d`-dimensional shadow `Δ ↦ d - Δ`. -/
def shadow (d : ℝ) (Δ : ℂ) : ℂ := (d : ℂ) - Δ

/-- **Shadow partner = adjoint partner iff principal.** `d - Δ = Δ̄ ↔ Re Δ = d/2`. PROVED. -/
theorem shadow_eq_conj_iff (d : ℝ) (Δ : ℂ) : shadow d Δ = conj Δ ↔ Δ.re = d / 2 := by
  simp only [shadow, Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith


/-- The arithmetic case `d = 1`: `1 - ρ = conj ρ ↔ Re ρ = 1/2`. PROVED. -/
theorem one_sub_eq_conj_iff (ρ : ℂ) : 1 - ρ = conj ρ ↔ ρ.re = 1 / 2 := by
  have := shadow_eq_conj_iff 1 ρ
  simp only [shadow, Complex.ofReal_one] at this
  rw [this]

/-! ## §2 Tate/Mellin data against the principal series -/

/-- **Mellin data of real tests are conjugation-equivariant.** PROVED. -/
theorem spectralTransform_conj (g : ℝ → ℝ) (s : ℂ) :
    conj (spectralTransform g s) = spectralTransform g (conj s) := by
  unfold spectralTransform
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_sub, map_one, map_div₀,
    map_ofNat]

/-- **On the principal series the reflection `Θ` is the adjoint**:
`Ψ(Θf)(s) = conj Ψf(s)` when `Re s = 1/2`. PROVED. -/
theorem reflect_eq_conj_on_line (g : ℝ → ℝ) {s : ℂ} (hs : s.re = 1 / 2) :
    spectralTransform (fun x => g (-x)) s = conj (spectralTransform g s) := by
  rw [spectralTransform_reflect, spectralTransform_conj, (one_sub_eq_conj_iff s).2 hs]

/-- The normalised Mellin character in the log variable. -/
def melChar (s : ℂ) (u : ℝ) : ℂ := Complex.exp ((s - 1 / 2) * u)

theorem hasDerivAt_exp_mul (c : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (c * Complex.exp (c * u)) u := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * u) * c) (u : ℂ) :=
    ((hasDerivAt_id (u : ℂ)).const_mul c).cexp.congr_deriv (by simp)
  simpa [mul_comm] using h.comp_ofReal

/-- **Mellin–Casimir matching.** The Mellin character is an eigenfunction of the
log-variable Casimir `1/4 - ∂²_u` with eigenvalue the principal-series Casimir `s(1-s)`:
`χ'' = (s - 1/2)² χ`, so `χ/4 - χ'' = s(1-s) χ`. PROVED, every `s`. -/
theorem melChar_casimir (s : ℂ) (u : ℝ) :
    deriv (deriv (melChar s)) u = (s - 1 / 2) ^ 2 * melChar s u ∧
      melChar s u / 4 - deriv (deriv (melChar s)) u = casimir s * melChar s u := by
  have h1 : deriv (melChar s) = fun x => (s - 1 / 2) * melChar s x := by
    funext x; exact (hasDerivAt_exp_mul (s - 1 / 2) x).deriv
  have h2 : deriv (deriv (melChar s)) u = (s - 1 / 2) ^ 2 * melChar s u := by
    rw [h1]
    have := ((hasDerivAt_exp_mul (s - 1 / 2) u).const_mul (s - 1 / 2)).deriv
    simp only [melChar] at this ⊢
    rw [this]; ring
  refine ⟨h2, ?_⟩
  rw [h2]; simp only [casimir]; ring

/-- **Tate/Mellin data intertwine `∂_u` with `-(s - 1/2)`** (integration by parts, smooth
compactly supported tests). PROVED. -/
theorem spectralTransform_deriv (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g)
    (s : ℂ) : spectralTransform (deriv g) s = -(s - 1 / 2) * spectralTransform g s := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hu : ∀ x, HasDerivAt (fun y : ℝ => ((g y : ℝ) : ℂ)) ((deriv g x : ℝ) : ℂ) x := fun x =>
    ((hg1.differentiable one_ne_zero) x).hasDerivAt.ofReal_comp
  have hv : ∀ x, HasDerivAt (melChar s) ((s - 1 / 2) * melChar s x) x := fun x =>
    hasDerivAt_exp_mul (s - 1 / 2) x
  have hgc : Continuous fun y : ℝ => ((g y : ℝ) : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hdc : Continuous fun y : ℝ => ((deriv g y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hg1.continuous_deriv le_rfl)
  have hmc : Continuous (melChar s) := by unfold melChar; fun_prop
  have hcsu : HasCompactSupport fun y : ℝ => ((g y : ℝ) : ℂ) :=
    hcs.comp_left Complex.ofReal_zero
  have hcsd : HasCompactSupport fun y : ℝ => ((deriv g y : ℝ) : ℂ) :=
    hcs.deriv.comp_left Complex.ofReal_zero
  have i1 : Integrable ((fun y : ℝ => ((g y : ℝ) : ℂ)) * fun x => (s - 1 / 2) * melChar s x) :=
    (hgc.mul (continuous_const.mul hmc)).integrable_of_hasCompactSupport hcsu.mul_right
  have i2 : Integrable ((fun y : ℝ => ((deriv g y : ℝ) : ℂ)) * melChar s) :=
    (hdc.mul hmc).integrable_of_hasCompactSupport hcsd.mul_right
  have i3 : Integrable ((fun y : ℝ => ((g y : ℝ) : ℂ)) * melChar s) :=
    (hgc.mul hmc).integrable_of_hasCompactSupport hcsu.mul_right
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    i1 i2 i3
  unfold spectralTransform
  change ∫ x, ((deriv g x : ℝ) : ℂ) * melChar s x = -(s - 1 / 2) * ∫ x, ((g x : ℝ) : ℂ) * melChar s x
  have hk : ∫ x, ((deriv g x : ℝ) : ℂ) * melChar s x =
      -∫ x, ((g x : ℝ) : ℂ) * ((s - 1 / 2) * melChar s x) := by
    rw [key, neg_neg]
  rw [hk, neg_mul, ← integral_const_mul]
  congr 1; congr 1; funext x; ring

/-- **Mellin–Casimir matching on tests.** The log-variable Casimir `1/4 - ∂²_u` acts on Tate/Mellin
data as multiplication by the principal-series Casimir: `Ψ_{g/4 - g''}(s) = s(1-s) Ψ_g(s)`.
PROVED, every `s`, every smooth compactly supported test. -/
theorem spectralTransform_casimir (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g)
    (s : ℂ) :
    spectralTransform (fun u => g u / 4 - deriv (deriv g) u) s = casimir s * spectralTransform g s := by
  have hd : ContDiff ℝ ∞ (deriv g) := by simpa using hg.iterate_deriv 1
  have h2 : spectralTransform (deriv (deriv g)) s = (s - 1 / 2) ^ 2 * spectralTransform g s := by
    rw [spectralTransform_deriv _ hd hcs.deriv, spectralTransform_deriv _ hg hcs]; ring
  have hmc : Continuous (melChar s) := by unfold melChar; fun_prop
  have i3 : Integrable fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) :=
    ((Complex.continuous_ofReal.comp hg.continuous).mul hmc).integrable_of_hasCompactSupport
      (hcs.comp_left Complex.ofReal_zero).mul_right
  have i1 : Integrable fun u : ℝ => ((g u / 4 : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) := by
    refine (i3.const_mul (1 / 4 : ℂ)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only; push_cast; ring
  have i2 : Integrable fun u : ℝ => ((deriv (deriv g) u : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) :=
    ((Complex.continuous_ofReal.comp ((hd.of_le (by norm_num) : ContDiff ℝ 1 (deriv g)).continuous_deriv
      le_rfl)).mul hmc).integrable_of_hasCompactSupport
      (hcs.deriv.deriv.comp_left Complex.ofReal_zero).mul_right
  unfold spectralTransform at h2 ⊢
  have hsplit : (fun u : ℝ => ((g u / 4 - deriv (deriv g) u : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u)) =
      fun u => ((g u / 4 : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) -
        ((deriv (deriv g) u : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) := by
    funext u; push_cast; ring
  rw [hsplit, integral_sub i1 i2, h2]
  have h4 : ∫ u : ℝ, ((g u / 4 : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u) =
      (1 / 4 : ℂ) * ∫ u : ℝ, (g u : ℂ) * Complex.exp ((s - 1 / 2) * u) := by
    rw [← integral_const_mul]; congr 1; funext u; push_cast; ring
  rw [h4]; simp only [casimir]; ring

/-- The character is bounded (unitary) on the log line iff `Re s = 1/2`: `‖χ_s(u)‖ = 1` for
all `u` iff principal. PROVED. -/
theorem melChar_unitary_iff (s : ℂ) : (∀ u : ℝ, ‖melChar s u‖ = 1) ↔ s.re = 1 / 2 := by
  simp only [melChar, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, mul_zero, sub_zero]
  constructor
  · intro h
    have h1 := h 1
    rw [Real.exp_eq_one_iff] at h1
    norm_num at h1
    linarith
  · intro h u
    rw [h]; norm_num

/-! ## §3 The theorem about theories, converse direction -/

namespace KernelTheory'

variable (T : KernelTheory)

/-- **Converse theorem about theories.** If the character data are conjugation-equivariant and
every weight is principal, the theory is reflection positive. PROVED. -/
theorem reflectionPositive_of_principalSeries
    (hconj : ∀ f s, conj (T.Ψ f s) = T.Ψ f (conj s))
    (hps : ∀ ρ ∈ T.W, ρ.re = 1 / 2) : T.ReflectionPositive := by
  intro f
  rw [KernelTheory.gram_spectral]
  have hterm : ∀ ρ : T.W, (T.m ρ : ℂ) * (T.Ψ f ρ * T.Ψ f (1 - ρ)) =
      ((T.m ρ * Complex.normSq (T.Ψ f ρ) : ℝ) : ℂ) := by
    intro ρ
    rw [(one_sub_eq_conj_iff (ρ : ℂ)).2 (hps ρ ρ.2), ← hconj, Complex.mul_conj]
    push_cast; ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- **Reflection positivity ↔ principal series**, for conjugation-equivariant theories. PROVED. -/
theorem reflectionPositive_iff_principalSeries
    (hconj : ∀ f s, conj (T.Ψ f s) = T.Ψ f (conj s)) :
    T.ReflectionPositive ↔ ∀ ρ ∈ T.W, ρ.re = 1 / 2 :=
  ⟨T.principalSeries_of_reflectionPositive, reflectionPositive_of_principalSeries T hconj⟩

end KernelTheory'

/-- The ζ datum is conjugation-equivariant. PROVED. -/
theorem zetaTheory_conj (f : zetaTheory.Test) (s : ℂ) :
    conj (zetaTheory.Ψ f s) = zetaTheory.Ψ f (conj s) :=
  spectralTransform_conj f.1 s

/-- **ARP ↔ RH (strip form), test-function level**, via the theory. The direction RH ⇒ ARP is
the new half here. PROVED (an equivalence of statements; neither side is asserted). -/
theorem arp_iff_rh_strip :
    ArithmeticReflectionPositivity ↔ ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  rw [← zeta_obligation_iff_arp]
  exact KernelTheory'.reflectionPositive_iff_principalSeries zetaTheory zetaTheory_conj

/-- Strip form ⇒ Mathlib's `RiemannHypothesis` (through the in-tree ξ conversion). PROVED. -/
theorem riemannHypothesis_of_strip (h : ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) :
    RiemannHypothesis :=
  GppGravitonDeltaId.rh_of_graviton_zero_identification fun ρ hρ =>
    h ρ ((GppXiReflection.xi_eq_zero_iff_nontrivial ρ).1 hρ)


/-! ## The ζ Gram form and the unitary realization -/

/-- **S-matrix unitarity form.** A Hilbert space with states `O f` whose norms are the ζ Gram
form. Named hypothesis: OPEN (equivalent to ARP below). -/
def UnitaryRealization : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (O : zetaTheory.Test → H),
    ∀ f, zetaTheory.gram f = ⟪O f, O f⟫_ℂ

/-- The ζ Gram form is the (real) Weil form of the autocorrelation. PROVED (in-tree GW-EF-1/2). -/
theorem gram_eq_weilForm (f : zetaTheory.Test) :
    zetaTheory.gram f = (weilForm (autocorr f.1) : ℂ) := by
  rw [KernelTheory.gram_spectral]
  obtain ⟨-, hsum⟩ := GppExplicitFormulaAssembly.explicit_formula_zeroSum f.2
  have hfac : ∀ ρ : nontrivialZeros,
      (GppXiZeroCounting.zeroMult ρ : ℂ) * spectralTransform (autocorr f.1) ρ =
        (GppXiZeroCounting.zeroMult ρ : ℂ) *
          (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ)) := fun ρ => by
    rw [gwef2_factorisation f.2]
  simp_rw [hfac] at hsum
  exact hsum

/-- **Unitary realization ↔ ARP.** A Hilbert-space (S-matrix unitarity) realization of the ζ
Gram form is exactly ARP: unitarity gives positivity, and conversely ARP is realized on `H = ℂ`.
So a realization is only progress if built without zero input. PROVED. -/
theorem unitaryRealization_iff_arp : UnitaryRealization ↔ ArithmeticReflectionPositivity := by
  constructor
  · rintro ⟨H, _, _, O, hO⟩
    apply arp_of_reflectionPositive
    intro f
    rw [hO f]
    exact inner_self_nonneg (𝕜 := ℂ)
  · intro harp
    refine ⟨ℂ, inferInstance, inferInstance,
      fun f => ((Real.sqrt (weilForm (autocorr f.1)) : ℝ) : ℂ), fun f => ?_⟩
    have hw : 0 ≤ weilForm (autocorr f.1) := harp f.1 f.2.1 f.2.2
    rw [gram_eq_weilForm, inner_self_eq_norm_sq_to_K, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have key : ∀ w : ℝ, 0 ≤ w → (w : ℂ) = ((Real.sqrt w : ℝ) : ℂ) ^ 2 := fun w hw' => by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hw']
    exact key _ hw

end GppBTSigmaSpectralTransform

#print axioms GppBTSigmaSpectralTransform.shadow_eq_conj_iff
#print axioms GppBTSigmaSpectralTransform.one_sub_eq_conj_iff
#print axioms GppBTSigmaSpectralTransform.spectralTransform_conj
#print axioms GppBTSigmaSpectralTransform.reflect_eq_conj_on_line
#print axioms GppBTSigmaSpectralTransform.hasDerivAt_exp_mul
#print axioms GppBTSigmaSpectralTransform.melChar_casimir
#print axioms GppBTSigmaSpectralTransform.melChar_unitary_iff
#print axioms GppBTSigmaSpectralTransform.spectralTransform_deriv
#print axioms GppBTSigmaSpectralTransform.spectralTransform_casimir
#print axioms GppBTSigmaSpectralTransform.KernelTheory'.reflectionPositive_of_principalSeries
#print axioms GppBTSigmaSpectralTransform.KernelTheory'.reflectionPositive_iff_principalSeries
#print axioms GppBTSigmaSpectralTransform.zetaTheory_conj
#print axioms GppBTSigmaSpectralTransform.arp_iff_rh_strip
#print axioms GppBTSigmaSpectralTransform.riemannHypothesis_of_strip
#print axioms GppBTSigmaSpectralTransform.gram_eq_weilForm
#print axioms GppBTSigmaSpectralTransform.unitaryRealization_iff_arp
