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
# `s = Δ₁`: the reduction `rh_of_s_eq_delta` and the exact remaining gap

Daniel's thesis: the zeta zeros are the conformal dimensions of the arithmetic principal series;
the one key step is `s = Δ₁` (zeta's `s` is the dimension of a one-dimensional celestial CFT,
celestial `Δ₂ = 2s` in `d = 2`), and unitarity of the S-matrix gives the positivity that is ARP.

This file makes that sentence precise against the in-tree `KernelTheory` (`zetaTheory`,
`rh_of_arp'`) and `GravitonDeltaIdentification` (#559), and splits it into labelled pieces.
Port of GPPDiscovery5 `lean/s-eq-delta/SEqDelta1d.lean` (`65ff9c2`) together with the
principal-series model of `ArithmeticCFTRoutes.lean` (Route 3, `aaa28f5`).

## §1 Label dictionary (PROVED, holds at every `s`)
`Δ₂ = 2s` intertwines the functional-equation shadow `s ↦ 1 - s` with the `d = 2` shadow
`Δ ↦ 2 - Δ`; the `d = 2` Casimir is `-4 s(1-s)`; `Re Δ₂ = 1 ↔ Re s = 1/2`.
The shadow partner equals the Hilbert-adjoint partner (`d - Δ = Δ̄`) iff `Re Δ = d/2`.

## §2 Tate/Mellin data vs the principal series (PROVED)
* the log-variable reflection `Θ` is the shadow on Mellin data (in tree);
* for real tests, Mellin data are conjugation-equivariant: `conj Ψf(s) = Ψf(s̄)`;
* hence on the principal series `Ψ(Θf)(s) = conj Ψf(s)`: `Θ` is the adjoint there;
* the Mellin character `e^{(s-1/2)u}` is an eigenfunction of `1/4 - ∂²_u` with eigenvalue the
  principal-series Casimir `s(1-s)`;
* on tests, Tate/Mellin data intertwine `∂_u` with `-(s - 1/2)` (integration by parts), so
  `Ψ_{g/4 - g''}(s) = s(1-s) Ψ_g(s)`: the log-variable Casimir is diagonalised by the Mellin
  transform with the principal-series Casimir as eigenvalue (`spectralTransform_casimir`).
  This holds at every `s`, so it is kinematics, not zero location.

## §3 Theorem about theories, converse (PROVED)
For a kernel theory with conjugation-equivariant data, a principal-series spectrum implies
reflection positivity. With `principalSeries_of_reflectionPositive`:
`ReflectionPositive ↔ every weight has Re = 1/2`.

## §4 The CCFT datum and the reduction (PROVED, conditional)
* `ArithmeticPrincipalSeriesCFT`: dimension spectrum with multiplicities, principal-series side
  (`Re Δ = 1/2`) as a named field: this is the side Daniel counts as proved.
* `ccftTwoPoint`: the two-point function `⟪O_g, O_f⟫ = Σ m(Δ) conj Ψg(Δ) Ψf(Δ)`; unitarity gives
  positivity (`ccftTwoPoint_self_re_nonneg`).
* `SEqDelta1d C`: **the identification** — the CFT's dimensions, with multiplicity, are exactly the
  nontrivial zeros.
* `rh_of_s_eq_delta`, `arp_of_s_eq_delta`: identification ⇒ ARP ⇒ Mathlib `RiemannHypothesis`.
* `zeta_correlator_eq_ccft_of_s_eq_delta`: under the identification, the ζ Gram form with `Θ` is
  literally the unitary CFT two-point function.
* `UnitaryRealization`: the S-matrix-unitarity form (a Hilbert space `H`, states `O f`, and
  `gram f = ⟪O f, O f⟫`). `unitaryRealization_iff_arp`: this is EXACTLY ARP.

## §5 The remaining gap, isolated (GAP / OPEN)
`ShadowIsAdjointOnSpectrum`: the functional-equation shadow acts on the zeros as the Hilbert
adjoint, `1 - ρ = conj ρ` (`Δ̄ = d - Δ`, Hermitian dilation generator on the spectrum).
`gap_equivalences`: GAP ↔ `∃ C, SEqDelta1d C` ↔ ζ correlator = CFT two-point ↔ ARP
↔ `UnitaryRealization` ↔ RH (strip form). So no weaker intermediate form of `s = Δ₁` lives at
the two-point level: the identification is RH-strength, and everything other than
`ShadowIsAdjointOnSpectrum` is PROVED. A non-circular discharge must construct the CFT (the
Hilbert space and `O f`) from arithmetic data without zero input.

`PrincipalCasimirRealization` (one symmetric operator `A ≥ 1/4` with every `casimir ρ` an
eigenvalue, the Hilbert–Pólya form of the principal-series side) implies the GAP (PROVED).

## §6 Principal-series model (PROVED, conditional)
* `bilinear_shadow_pairing_invariant`: the bilinear pairing `χ_s ⊗ χ_{1-s}` is invariant for every
  `s`; it carries no positivity. `hermitian_invariant_iff`: a nonzero invariant Hermitian form on
  `χ_s` exists iff `Re s = 1/2`.
* `casimir_nonneg_real_iff`: a real Casimir eigenvalue `s(1−s) ≥ 0` forces the principal or the
  complementary series (`complementary_casimir`: the latter really occurs).
* `NonnegCasimirRealization` (one symmetric `A ≥ 0`, weaker than Hilbert–Pólya `≥ 1/4`:
  `nonnegCasimir_of_principalCasimir`) together with `NoRealStripZeros` (STANDARD, not in Mathlib)
  gives the GAP (`gap_of_nonnegCasimir_noReal`) and RH (`rh_of_nonnegCasimir_noReal`).

Labels: everything stated as a theorem is PROVED (standard axioms). `SEqDelta1d`,
`ShadowIsAdjointOnSpectrum`, `UnitaryRealization`, `PrincipalCasimirRealization`,
`NonnegCasimirRealization`, `NoRealStripZeros` are named hypothesis Props, never asserted: OPEN
(`NoRealStripZeros` STANDARD). ARP OPEN. RH OPEN. No `sorry`, no axiom, no stub.

Daniel Toupin / Golden Physics Project … This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo.
-/

open Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff
open GppMeyerSpectralWeil GppWeilCriterion GppArithmeticReflection GppGwefAssembly
  GppKernelTheory GppCasimirCriticalLine

noncomputable section

namespace GppSEqDelta

/-! ## §1 Label dictionary -/

/-- The `d = 2` celestial dimension of the arithmetic variable: `Δ₂ = 2s`. -/
def celestialDelta (s : ℂ) : ℂ := 2 * s

/-- The `d`-dimensional shadow `Δ ↦ d - Δ`. -/
def shadow (d : ℝ) (Δ : ℂ) : ℂ := (d : ℂ) - Δ

/-- **FE ↔ shadow.** `Δ₂(1 - s) = 2 - Δ₂(s)`. PROVED, every `s`. -/
theorem celestialDelta_one_sub (s : ℂ) :
    celestialDelta (1 - s) = shadow 2 (celestialDelta s) := by
  simp only [celestialDelta, shadow]; push_cast; ring

/-- `Re Δ₂ = 1 ↔ Re s = 1/2`. PROVED. -/
theorem celestialDelta_principal_iff (s : ℂ) :
    (celestialDelta s).re = 1 ↔ s.re = 1 / 2 := by
  simp only [celestialDelta, Complex.mul_re]
  norm_num
  constructor <;> intro h <;> linarith

/-- The `d = 2` Casimir `Δ(Δ - 2)` is `-4 s(1-s)`. PROVED, every `s`. -/
theorem casimir_d2 (s : ℂ) :
    celestialDelta s * (celestialDelta s - 2) = -4 * casimir s := by
  simp only [celestialDelta, casimir]; ring

/-- The Casimir is shadow invariant. PROVED. -/
theorem casimir_one_sub (s : ℂ) : casimir (1 - s) = casimir s := by
  simp only [casimir]; ring

/-- **Shadow partner = adjoint partner iff principal.** `d - Δ = Δ̄ ↔ Re Δ = d/2`. PROVED. -/
theorem shadow_eq_conj_iff (d : ℝ) (Δ : ℂ) : shadow d Δ = conj Δ ↔ Δ.re = d / 2 := by
  simp only [shadow, Complex.ext_iff, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith

/-- At `d = 2` in the arithmetic variable: `2 - Δ₂ = conj Δ₂ ↔ Re s = 1/2`. PROVED. -/
theorem celestial_shadow_eq_conj_iff (s : ℂ) :
    shadow 2 (celestialDelta s) = conj (celestialDelta s) ↔ s.re = 1 / 2 := by
  rw [shadow_eq_conj_iff, ← celestialDelta_principal_iff]
  constructor <;> intro h <;> linarith

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

/-! ## §4 The CCFT datum, the identification, the reduction -/

/-- **An arithmetic principal-series CFT (two-point level).** A dimension spectrum with
multiplicities; the principal-series side `Re Δ = d/2` (`d = 1`) is a named field, the side Daniel
counts as proved. -/
structure ArithmeticPrincipalSeriesCFT where
  Spec : Set ℂ
  mult : ℂ → ℕ
  principal : ∀ Δ ∈ Spec, Δ.re = 1 / 2

/-- The CFT two-point function of the smeared primaries in the dimension (Plancherel) basis:
`⟪O_g, O_f⟫ = Σ_Δ m(Δ) conj Ψg(Δ) Ψf(Δ)`. -/
def ccftTwoPoint (Spec : Set ℂ) (m : ℂ → ℕ) (g f : zetaTheory.Test) : ℂ :=
  ∑' Δ : Spec, (m Δ : ℂ) * (conj (spectralTransform g.1 Δ) * spectralTransform f.1 Δ)

/-- **Unitarity gives positivity**: `Re ⟪O_f, O_f⟫ ≥ 0`, for every spectrum. PROVED. -/
theorem ccftTwoPoint_self_re_nonneg (Spec : Set ℂ) (m : ℂ → ℕ) (f : zetaTheory.Test) :
    0 ≤ (ccftTwoPoint Spec m f f).re := by
  unfold ccftTwoPoint
  have hterm : ∀ Δ : Spec, (m Δ : ℂ) * (conj (spectralTransform f.1 Δ) *
      spectralTransform f.1 Δ) = ((m Δ * Complex.normSq (spectralTransform f.1 Δ) : ℝ) : ℂ) := by
    intro Δ; rw [mul_comm (conj _), Complex.mul_conj]; push_cast; ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun Δ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- **`s = Δ₁`, the identification.** The CFT's dimensions, with multiplicity, are exactly the
nontrivial zeros of `ζ`. Named hypothesis: OPEN. -/
def SEqDelta1d (C : ArithmeticPrincipalSeriesCFT) : Prop :=
  C.Spec = nontrivialZeros ∧ ∀ ρ ∈ nontrivialZeros, C.mult ρ = GppXiZeroCounting.zeroMult ρ

/-- **The reduction, strip form.** PROVED (conditional on the identification). -/
theorem rh_strip_of_s_eq_delta (C : ArithmeticPrincipalSeriesCFT) (hid : SEqDelta1d C) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ =>
  C.principal ρ (hid.1 ▸ hρ)

/-- **Identification + unitarity ⇒ ARP.** PROVED (conditional). -/
theorem arp_of_s_eq_delta (C : ArithmeticPrincipalSeriesCFT) (hid : SEqDelta1d C) :
    ArithmeticReflectionPositivity :=
  arp_iff_rh_strip.2 (rh_strip_of_s_eq_delta C hid)

/-- **`rh_of_s_eq_delta`: identification + principal series ⇒ Mathlib `RiemannHypothesis`.**
PROVED (conditional; the identification is not asserted). -/
theorem rh_of_s_eq_delta (C : ArithmeticPrincipalSeriesCFT) (hid : SEqDelta1d C) :
    RiemannHypothesis :=
  riemannHypothesis_of_strip (rh_strip_of_s_eq_delta C hid)

/-- The ζ correlator equals the CFT two-point function, termwise, once the shadow is the
adjoint on the zeros. PROVED. -/
theorem zeta_gram_eq_ccft_of_line (h : ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) (f : zetaTheory.Test) :
    zetaTheory.gram f = ccftTwoPoint nontrivialZeros GppXiZeroCounting.zeroMult f f := by
  rw [KernelTheory.gram_spectral]
  unfold ccftTwoPoint
  congr 1; funext ρ
  change (GppXiZeroCounting.zeroMult ρ : ℂ) *
      (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ)) = _
  rw [(one_sub_eq_conj_iff (ρ : ℂ)).2 (h ρ ρ.2), ← spectralTransform_conj, mul_comm
    (spectralTransform f.1 ρ)]

/-- **Under `s = Δ₁`, the ζ Gram form (with `Θ` the FE reflection) IS the unitary CFT
two-point function.** PROVED (conditional). -/
theorem zeta_correlator_eq_ccft_of_s_eq_delta (C : ArithmeticPrincipalSeriesCFT)
    (hid : SEqDelta1d C) (f : zetaTheory.Test) :
    zetaTheory.gram f = ccftTwoPoint nontrivialZeros GppXiZeroCounting.zeroMult f f :=
  zeta_gram_eq_ccft_of_line (rh_strip_of_s_eq_delta C hid) f

/-- Correlator-level identification: the ζ Gram form is the CFT two-point function on the zeros. -/
def CorrelatorSEqDelta : Prop :=
  ∀ f : zetaTheory.Test, zetaTheory.gram f = ccftTwoPoint nontrivialZeros GppXiZeroCounting.zeroMult f f

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

/-! ## §5 The remaining gap -/

/-- **THE GAP.** The functional-equation shadow acts on the ζ spectrum as the Hilbert adjoint:
`1 - ρ = conj ρ` (`Δ̄ = d - Δ`, the dilation generator is Hermitian on the spectrum).
Named hypothesis: OPEN (RH-strength, `gap_equivalences`). -/
def ShadowIsAdjointOnSpectrum : Prop := ∀ ρ ∈ nontrivialZeros, 1 - ρ = conj ρ

/-- **The gap, all forms equivalent.** GAP ↔ `∃ C, SEqDelta1d C` ↔ correlator identification
↔ ARP ↔ unitary realization ↔ RH (strip). PROVED (equivalences of statements only). -/
theorem gap_equivalences :
    (ShadowIsAdjointOnSpectrum ↔ ∃ C : ArithmeticPrincipalSeriesCFT, SEqDelta1d C) ∧
    (ShadowIsAdjointOnSpectrum ↔ CorrelatorSEqDelta) ∧
    (ShadowIsAdjointOnSpectrum ↔ ArithmeticReflectionPositivity) ∧
    (ShadowIsAdjointOnSpectrum ↔ UnitaryRealization) ∧
    (ShadowIsAdjointOnSpectrum ↔ ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) := by
  have hstrip : ShadowIsAdjointOnSpectrum ↔ ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
    forall₂_congr fun ρ _ => one_sub_eq_conj_iff ρ
  have harp : ShadowIsAdjointOnSpectrum ↔ ArithmeticReflectionPositivity :=
    hstrip.trans arp_iff_rh_strip.symm
  refine ⟨?_, ?_, harp, harp.trans unitaryRealization_iff_arp.symm, hstrip⟩
  · constructor
    · intro h
      exact ⟨⟨nontrivialZeros, GppXiZeroCounting.zeroMult, hstrip.1 h⟩, rfl, fun _ _ => rfl⟩
    · rintro ⟨C, hC⟩; exact hstrip.2 (rh_strip_of_s_eq_delta C hC)
  · constructor
    · intro h f; exact zeta_gram_eq_ccft_of_line (hstrip.1 h) f
    · intro h
      apply harp.2
      apply arp_of_reflectionPositive
      intro f
      rw [h f]
      exact ccftTwoPoint_self_re_nonneg _ _ f

/-- **Hilbert–Pólya form of the principal-series side.** One symmetric operator `A ≥ 1/4` on a
Hilbert space with every `casimir ρ` (ρ a nontrivial zero) as an eigenvalue. Named hypothesis:
OPEN. -/
def PrincipalCasimirRealization : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (A : E →ₗ[ℂ] E),
    (∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) ∧ (∀ x, (1 / 4 : ℝ) * ‖x‖ ^ 2 ≤ (⟪A x, x⟫_ℂ).re) ∧
    ∀ ρ ∈ nontrivialZeros, ∃ v : E, v ≠ 0 ∧ A v = casimir ρ • v

/-- **Casimir realization ⇒ the gap.** An eigenvalue of a symmetric `A ≥ 1/4` is real and
`≥ 1/4`, which forces `Re ρ = 1/2` (`casimir_ge_quarter_iff`). PROVED (conditional). -/
theorem gap_of_principalCasimirRealization (h : PrincipalCasimirRealization) :
    ShadowIsAdjointOnSpectrum := by
  obtain ⟨E, _, _, A, hsym, hlow, heig⟩ := h
  intro ρ hρ
  obtain ⟨v, hv0, hAv⟩ := heig ρ hρ
  rw [one_sub_eq_conj_iff]
  apply (casimir_ge_quarter_iff ρ).1
  set c := casimir ρ
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hin : ⟪A v, v⟫_ℂ = conj c * ((‖v‖ : ℂ) ^ 2) := by
    rw [hAv, inner_smul_left, inner_self_eq_norm_sq_to_K]; rfl
  have hin2 : ⟪v, A v⟫_ℂ = c * ((‖v‖ : ℂ) ^ 2) := by
    rw [hAv, inner_smul_right, inner_self_eq_norm_sq_to_K]; rfl
  have hcc : conj c = c := by
    have := hsym v v
    rw [hin, hin2] at this
    have hne : ((‖v‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hn.ne'
    exact mul_right_cancel₀ hne this
  have him : c.im = 0 := by
    have := congrArg Complex.im hcc
    simp at this; linarith
  refine ⟨him, ?_⟩
  have hl := hlow v
  rw [hin, hcc] at hl
  have hre : (c * ((‖v‖ : ℂ) ^ 2)).re = c.re * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre] at hl
  nlinarith

/-- **Casimir realization ⇒ ARP ⇒ RH.** PROVED (conditional). -/
theorem rh_of_principalCasimirRealization (h : PrincipalCasimirRealization) :
    RiemannHypothesis :=
  riemannHypothesis_of_strip ((gap_equivalences.2.2.2.2).1 (gap_of_principalCasimirRealization h))

/-- **The label dictionary does not see the line.** At an off-line point the FE↔shadow and
Casimir identities still hold, but shadow ≠ adjoint. So §1 cannot force zeros onto the line;
only `ShadowIsAdjointOnSpectrum` can (ζ vs `F_θ`). PROVED. -/
theorem dictionary_blind_off_line (s : ℂ) (hs : s.re ≠ 1 / 2) :
    celestialDelta (1 - s) = shadow 2 (celestialDelta s) ∧
      celestialDelta s * (celestialDelta s - 2) = -4 * casimir s ∧
      1 - s ≠ conj s :=
  ⟨celestialDelta_one_sub s, casimir_d2 s, fun h => hs ((one_sub_eq_conj_iff s).1 h)⟩

/-! ## Principal-series model (from GPPDiscovery5 `ArithmeticCFTRoutes.lean`, Route 3) -/

section PrincipalSeriesModel

open GppCasimirCriticalLine

/-- The log-scale character `χ_s(a) = e^{(s − 1/2) a}`. -/
def chi (s : ℂ) (a : ℝ) : ℂ := Complex.exp ((s - 1 / 2) * a)

/-- **The bilinear shadow pairing is invariant for every `s`.** PROVED. -/
theorem bilinear_shadow_pairing_invariant (s : ℂ) (a : ℝ) : chi s a * chi (1 - s) a = 1 := by
  unfold chi; rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero

/-- **A nonzero invariant Hermitian form on `χ_s` exists iff `Re s = 1/2`.** PROVED. -/
theorem hermitian_invariant_iff (s : ℂ) {b : ℂ} (hb : b ≠ 0) :
    (∀ a : ℝ, conj (chi s a) * chi s a * b = b) ↔ s.re = 1 / 2 := by
  have key : ∀ a : ℝ, conj (chi s a) * chi s a = ((Real.exp ((2 * s.re - 1) * a) : ℝ) : ℂ) := by
    intro a
    unfold chi
    rw [← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    apply Complex.ext <;> simp; ring
  constructor
  · intro h
    have h1 := h 1
    rw [key 1] at h1
    have h2 : ((Real.exp ((2 * s.re - 1) * 1) : ℝ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hb (h1.trans (one_mul b).symm)
      exact this
    have h3 : Real.exp ((2 * s.re - 1) * 1) = 1 := by exact_mod_cast h2
    rw [Real.exp_eq_one_iff] at h3
    linarith
  · intro hs a
    rw [key a, hs]; norm_num

/-- **Nonnegative real Casimir ⇔ principal or complementary.** `s(1−s)` is real and `≥ 0` iff
`Re s = 1/2`, or `s` is real in `[0, 1]`. PROVED. -/
theorem casimir_nonneg_real_iff (ρ : ℂ) :
    ((casimir ρ).im = 0 ∧ 0 ≤ (casimir ρ).re) ↔
      ρ.re = 1 / 2 ∨ (ρ.im = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1) := by
  rw [casimir_real_iff, casimir_re]
  constructor
  · rintro ⟨h | h, hre⟩
    · exact Or.inl h
    · rw [h] at hre
      refine Or.inr ⟨h, ?_, ?_⟩ <;> nlinarith
  · rintro (h | ⟨h, h0, h1⟩)
    · refine ⟨Or.inl h, ?_⟩; rw [h]; nlinarith [sq_nonneg ρ.im]
    · refine ⟨Or.inr h, ?_⟩; rw [h]; nlinarith

/-- **The complementary series is really there:** for real `s ∈ (0,1)`, `s(1−s) ∈ (0, 1/4]` is
real. So a nonnegative Casimir realization does not by itself exclude real zeros. PROVED. -/
theorem complementary_casimir (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    (casimir (σ : ℂ)).im = 0 ∧ 0 < (casimir (σ : ℂ)).re ∧ (casimir (σ : ℂ)).re ≤ 1 / 4 := by
  rw [casimir_im, casimir_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨by ring, by nlinarith, by nlinarith [sq_nonneg (σ - 1 / 2)]⟩

/-- **Named (STANDARD, not in Mathlib):** no nontrivial zero is real. -/
def NoRealStripZeros : Prop := ∀ ρ ∈ nontrivialZeros, ρ.im ≠ 0

/-- **Automorphic shape of the principal-series side:** one symmetric operator `A ≥ 0` (not
`≥ 1/4`) with every `casimir ρ` an eigenvalue. Named hypothesis: OPEN. -/
def NonnegCasimirRealization : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (A : E →ₗ[ℂ] E),
    (∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) ∧ (∀ x, 0 ≤ (⟪A x, x⟫_ℂ).re) ∧
    ∀ ρ ∈ nontrivialZeros, ∃ v : E, v ≠ 0 ∧ A v = casimir ρ • v

/-- The automorphic hypothesis is weaker than Hilbert–Pólya. PROVED. -/
theorem nonnegCasimir_of_principalCasimir (h : PrincipalCasimirRealization) :
    NonnegCasimirRealization := by
  obtain ⟨E, i1, i2, A, hs, hl, he⟩ := h
  exact ⟨E, i1, i2, A, hs, fun x => le_trans (by positivity) (hl x), he⟩

/-- Eigenvalues of a symmetric `A ≥ 0` are real and `≥ 0`. PROVED. -/
theorem eigen_real_nonneg {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (hsym : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (hpos : ∀ x, 0 ≤ (⟪A x, x⟫_ℂ).re)
    {c : ℂ} {v : E} (hv0 : v ≠ 0) (hAv : A v = c • v) : c.im = 0 ∧ 0 ≤ c.re := by
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hin : ⟪A v, v⟫_ℂ = conj c * ((‖v‖ : ℂ) ^ 2) := by
    rw [hAv, inner_smul_left, inner_self_eq_norm_sq_to_K]; rfl
  have hin2 : ⟪v, A v⟫_ℂ = c * ((‖v‖ : ℂ) ^ 2) := by
    rw [hAv, inner_smul_right, inner_self_eq_norm_sq_to_K]; rfl
  have hcc : conj c = c := by
    have := hsym v v
    rw [hin, hin2] at this
    have hne : ((‖v‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hn.ne'
    exact mul_right_cancel₀ hne this
  have him : c.im = 0 := by
    have := congrArg Complex.im hcc
    simp at this; linarith
  refine ⟨him, ?_⟩
  have hl := hpos v
  rw [hin, hcc] at hl
  have hre : (c * ((‖v‖ : ℂ) ^ 2)).re = c.re * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre] at hl
  by_contra hneg; rw [not_le] at hneg
  nlinarith

/-- **Nonnegative Casimir realization + no real zeros ⇒ the GAP.** PROVED (conditional). -/
theorem gap_of_nonnegCasimir_noReal (h : NonnegCasimirRealization) (hr : NoRealStripZeros) :
    ShadowIsAdjointOnSpectrum := by
  obtain ⟨E, _, _, A, hsym, hpos, heig⟩ := h
  intro ρ hρ
  obtain ⟨v, hv0, hAv⟩ := heig ρ hρ
  have hc := eigen_real_nonneg A hsym hpos hv0 hAv
  rcases (casimir_nonneg_real_iff ρ).1 hc with hre | ⟨him, -, -⟩
  · apply Complex.ext <;> simp [hre]; linarith
  · exact absurd him (hr ρ hρ)

/-- **… ⇒ RH (strip form) ⇒ Mathlib `RiemannHypothesis`.** PROVED (conditional). -/
theorem rh_of_nonnegCasimir_noReal (h : NonnegCasimirRealization) (hr : NoRealStripZeros) :
    RiemannHypothesis := by
  have hg := gap_of_nonnegCasimir_noReal h hr
  have hstrip : ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ => by
    have := congrArg Complex.re (hg ρ hρ)
    simp at this; linarith
  exact GppGravitonDeltaId.rh_of_graviton_zero_identification fun ρ hρ =>
    hstrip ρ ((GppXiReflection.xi_eq_zero_iff_nontrivial ρ).1 hρ)

end PrincipalSeriesModel

end GppSEqDelta
