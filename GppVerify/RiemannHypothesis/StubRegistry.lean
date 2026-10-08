import GppVerify.RiemannHypothesis.RHCriteriaAtlas
import GppVerify.RHSpectralMultiplicity
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Stub registry: retired `open_*` stubs and the precise statements that replace them

Each declaration below replaces a `theorem open_X : True := trivial` stub with the precise
statement the stub stood for, either as a `Prop` (never asserted) with its proved relation to
other criteria, or, when the content is genuinely provable, as a theorem. Nothing here claims
RH or any open conjecture. The retired stub names are given in each docstring so that old
references can be traced.

| Retired stub | Replacement |
|---|---|
| `open_haar_inversion_isometry` | `haar_inversion_integral` (proved) |
| `open_rh_pathway_target` | `rh_pathway_target_iff` (the target *is* `AtomWeightOne`) |
| `open_zero_simplicity` | `SimpleStripZeros` (existing) + `zero_simplicity_iff_deriv_ne_zero` |
| `open_generalised_rh` | `GeneralisedRH` (Prop) + `rh_of_generalisedRH` |
| `open_weil_criterion`, `open_weil_positivity_haar_squares` | `WeilPositivityAll` (Prop) + `weil_criterion_iff` |
| `open_weil_positivity_hilbert` | `weil_positivity_hilbert_imp_rh` |

Scope: `GeneralisedRH` is for Dirichlet L-functions (Mathlib's `DirichletCharacter.LFunction`);
Hecke L-functions of number fields are not in Mathlib and are not covered. Zeros of an
imprimitive character's L-function in the *open* strip are the zeros of the primitive one, since
the extra Euler factors vanish only on `Re s = 0`, so the strip statement is the right GRH.
-/

open MeasureTheory Set GppWeilCriterion

namespace GppStubRegistry

/-- **Haar inversion on `(ℝ⁺, dr/r)`.** `J : r ↦ r⁻¹` preserves the Haar measure `dr/r`:
    `∫₀^∞ f(1/r) dr/r = ∫₀^∞ f(r) dr/r` for every `f` (Bochner convention: both sides are `0`
    when not integrable). Retires `open_haar_inversion_isometry`. Proof: Mathlib's
    `integral_comp_rpow_Ioi` at exponent `p = -1`. -/
theorem haar_inversion_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ x in Ioi (0:ℝ), (x⁻¹ : ℝ) • f x⁻¹ = ∫ x in Ioi (0:ℝ), (x⁻¹ : ℝ) • f x := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => (y⁻¹ : ℝ) • f y) (p := -1) (by norm_num)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  simp only [Real.rpow_neg_one, abs_neg, abs_one, smul_smul, inv_inv]
  congr 1
  rw [show (-1 : ℝ) - 1 = -2 by norm_num]
  rw [Real.rpow_neg hx0.le, Real.rpow_two]
  field_simp

/-- Retires `open_rh_pathway_target`. The pathway's *target* (RH on the strip) and its stated
    *input* (atom weight one) are equivalent: relocating the difficulty, not reducing it. -/
theorem rh_pathway_target_iff : GppRH.RiemannHypothesisStrip ↔ GppRH.AtomWeightOne :=
  GppRH.rh_iff_atomWeightOne

/-- Retires `open_zero_simplicity`. Simplicity of the strip zeros is an **open problem**; what is
    proved is its reduction to a nonvanishing condition on `ζ'`. -/
theorem zero_simplicity_iff_deriv_ne_zero :
    GppRH.SimpleStripZeros ↔ ∀ r ∈ GppRH.stripZeros, deriv riemannZeta r ≠ 0 :=
  GppRH.simpleStripZeros_iff_deriv_ne_zero

/-- Retires `open_generalised_rh`. **GRH for Dirichlet L-functions** (Mathlib's
    `DirichletCharacter.LFunction`): every zero in the open strip has real part `1/2`.
    A statement, not a claim: it is open, and it strictly strengthens RH. -/
def GeneralisedRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    χ.LFunction s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- GRH implies RH: take the trivial character mod 1, whose L-function is `ζ`. -/
theorem rh_of_generalisedRH (h : GeneralisedRH) : GppRH.RiemannHypothesisStrip := by
  intro r hr h0 h1
  exact h 1 (1 : DirichletCharacter ℂ 1) r (by simpa using hr) h0 h1

/-- Retires `open_weil_criterion` and `open_weil_positivity_haar_squares`. **Weil positivity
    on every finite set of zeros**: the paired form is nonnegative for all coefficient
    families. (The explicit-formula side, `D_k = Σ_ρ Ω̂(ρ) + local terms`, is not formalised;
    this is the zero-side form.) -/
def WeilPositivityAll : Prop :=
  ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
    0 ≤ (pairedForm zetaInvolution S c).re

/-- **Weil's criterion, zero-side form**: `RH ↔ Weil positivity`. It is an equivalence, so
    proving Weil positivity for "Haar squares" would be proving RH. -/
theorem weil_criterion_iff :
    (∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2) ↔ WeilPositivityAll :=
  rh_iff_weil_pairedForm_nonneg

/-- Retires `open_weil_positivity_hilbert`: a Hilbert-space realization of every two-point form
    already implies RH, with no positivity statement assumed. -/
theorem weil_positivity_hilbert_imp_rh {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V]
    (h : ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
      ∃ v : V, pairedForm zetaInvolution ({ρ, zetaInvolution ρ} : Finset ℂ) c = inner ℂ v v) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 :=
  GppRHAtlas.hilbert_realization_imp_rh h

end GppStubRegistry
