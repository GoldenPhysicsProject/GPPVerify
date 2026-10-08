import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.TwoPointCriterion
import GppVerify.RiemannHypothesis.HilbertQuotientClosure
import GppVerify.RiemannHypothesis.KreinGraphClosure
import GppVerify.RiemannHypothesis.WeilInterpolationBridge
import GppVerify.RiemannHypothesis.WeilPolynomialInterpolation
import GppVerify.RiemannHypothesis.CasimirRiemannHypothesis
import GppVerify.RiemannHypothesis.ZeroQuartetHalfFlip
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree
import GppVerify.RiemannHypothesis.ExponentialSumGrowth
import GppVerify.RHSpectralMultiplicity
import GppVerify.RiemannHypothesis.ObserverPrincipalSeriesPositivity
import GppVerify.RiemannHypothesis.ObserverCasimirSpectralSurvival

/-!
# The RH criteria atlas

One place to see the machine-checked reductions of the Riemann Hypothesis in this library, ordered by how
much they assume. Every entry is a precisely stated `Prop` about the zeros (or about an object built from
them), with the proved direction named; **no entry assumes RH or a zero location**. The atlas is *living*:
each row is an `example`/`theorem` below, so renaming or breaking a criterion breaks this file.

Write `RHz : Prop := ∀ ρ ∈ nontrivialZeros, ρ.re = 1/2` (zeros in the open strip lie on the critical line,
i.e. on the principal series `Re Δ = 1`, `Δ = 2ρ`).

| # | Criterion `X` (a statement about the zeros / an object built from them) | Proved | Where |
|---|---|---|---|
| 1 | Weil positivity on **every** finite set of zeros | `X ↔ RHz` | `rh_iff_weil_pairedForm_nonneg` |
| 2 | Positivity of the form on each **reflection pair** `{ρ, 1−ρ̄}` only (strictly weaker than 1) | `X ↔ RHz` | `rh_iff_two_point_pairedForm_nonneg` |
| 3 | Every two-point form is the squared norm of a vector in **some complex Hilbert space** (weaker still: no positivity statement, only a realization) | `X → RHz` | `rh_of_honest_twoPoint_hilbert_realization` |
| 4 | Krein-graph contraction of the pair forms | `X → RHz` | `rh_of_twoPoint_kreinGraph_contraction` |
| 5 | Test-function positivity + interpolation/seed closure (finite or pair-support) | `X → RHz` | `rh_of_testPos_*` |
| 6 | **Atom weight one**: at most one strip zero per ordinate | `X ↔ RH_strip` | `rh_iff_atomWeightOne` |
| 7 | Casimir `ρ(1−ρ)` real and `≥ 1/4` at every zero | `X ↔ RH` | `riemannHypothesis_iff_casimir` |
| 8 | Centred square `(ρ−1/2)²` real and `≤ 0` at every zero | `X ↔ RH` | `riemannHypothesis_iff_centeredSq` |
| 9 | The half-flip invariant `P₋(ρ−1/2)` vanishes at every zero | `X ↔ RH` | `riemannHypothesis_iff_P_minus` |
| 10 | **Hermitian survival**: every non-real zero's Casimir is an eigenvalue of some symmetric operator | `X → (non-real zeros on the line)` | `rh_nonreal_of_hermitian_survival` (new) |
| 11 | **Slit-plane log-derivative**: `ξ(1/2+√u)` has a holomorphic logarithmic derivative on `ℂ∖(−∞,0]` | `X → RH` | `riemannHypothesis_of_slit_log_derivative` (new) |
| 13 | **Observer-positive survival**: every strip zero is a reflected pair non-amplifying in one common finite-Haar norm (`k > 1`) | `X ↔ RH_strip` | `observerPositiveZeroSurvival_iff_rh` |
| 14 | **Celestial principal-series survival**: `Re(2ρ) = 1` for every strip zero | `X ↔ RH_strip` | `celestialPrincipalZeroSurvival_iff_rh` |
| 15 | Hermitian Casimir eigenvector (single zero) | `X → Re ρ = 1/2` | `critical_of_hermitian_casimir_eigenvector` |
| 12 | Bounded finite exponential sum ⇒ no growing exponent (the abstract growth lemma behind fixed-window, cutoff-growth and Gaussian-orbit routes) | lemma | `bounded_exp_sum_re_nonpos` (new) |

Row 3 is the formal shape of "it is enough to realise the zeros in a positive Hilbert space": no positivity
of the Weil form is assumed, only that each pair form is a norm-square of *some* vector. Row 10 is the
operator-survival form: no explicit formula is used at all. Rows 1–9 are in `GppWeilCriterion`, `GppRH`,
`GppCasimirRH`, `GppZeroQuartet`.

## Scope

This file proves one new implication (row 10) and indexes the others. **No row is proved to hold**: each
criterion `X` is an open statement. The arithmetic input that would establish any of them — the Euler product
forcing positivity — is not supplied here, and the Davenport–Heilbronn function (same functional equation, no
Euler product) satisfies the symmetry facts behind every row while having off-line zeros. No RH claim.
-/

open GppWeilCriterion

namespace GppRHAtlas

/-- Zeros in the open strip lie on the critical line. -/
def RHz : Prop := ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2

/-- Row 1 ⇒ 2: two-point positivity is implied by positivity on every finite set. -/
theorem weil_all_imp_twoPoint
    (h : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm zetaInvolution S c).re) :
    ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm zetaInvolution ({ρ, zetaInvolution ρ} : Finset ℂ) c).re :=
  rh_iff_two_point_pairedForm_nonneg.mp (rh_iff_weil_pairedForm_nonneg.mpr h)

/-- Row 2 ⇒ 3 is not a conversion of positivity into realisation; the reverse is: a Hilbert realization gives
two-point positivity, hence RH. -/
theorem hilbert_realization_imp_rh {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (h : ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
      ∃ v : V, pairedForm zetaInvolution ({ρ, zetaInvolution ρ} : Finset ℂ) c = inner ℂ v v) :
    RHz :=
  rh_of_honest_twoPoint_hilbert_realization h

/-- **Row 10. Hermitian survival of the Casimir implies the principal series (for non-real zeros).**
If every non-real zero `ρ` of the strip has `ρ(1−ρ)` as an eigenvalue of a symmetric operator `A` on a
complex inner-product space, then `Re ρ = 1/2`. -/
theorem rh_nonreal_of_hermitian_survival {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →ₗ[ℂ] V) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hsurv : ∀ ρ ∈ nontrivialZeros, ρ.im ≠ 0 → ∃ v : V, v ≠ 0 ∧ A v = (ρ * (1 - ρ)) • v) :
    ∀ ρ ∈ nontrivialZeros, ρ.im ≠ 0 → ρ.re = 1 / 2 := by
  intro ρ hρ him
  obtain ⟨v, hv0, hv⟩ := hsurv ρ hρ him
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  have h1 : inner ℂ (A v) v = inner ℂ v (A v) := hA v v
  rw [hv, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : (starRingEnd ℂ) (ρ * (1 - ρ)) * ((‖v‖ : ℂ) ^ 2) = (ρ * (1 - ρ)) * ((‖v‖ : ℂ) ^ 2) := h1
  have hnz : ((‖v‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hn.ne'
  have h3 : (starRingEnd ℂ) (ρ * (1 - ρ)) = ρ * (1 - ρ) := mul_right_cancel₀ hnz h2
  have h4 := congrArg Complex.im h3
  simp at h4
  -- Im(ρ(1−ρ)) = γ(1 − 2β) = 0
  have h5 : ρ.im * (1 - 2 * ρ.re) = 0 := by nlinarith [h4]
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd h him
  · linarith

/-- With the (classical, not formalised here) fact that `ζ` has no real zeros in `(0,1)`, Hermitian
survival of every nontrivial zero gives RH. -/
theorem rhz_of_hermitian_survival {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →ₗ[ℂ] V) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hsurv : ∀ ρ ∈ nontrivialZeros, ρ.im ≠ 0 → ∃ v : V, v ≠ 0 ∧ A v = (ρ * (1 - ρ)) • v)
    (hreal : ∀ ρ ∈ nontrivialZeros, ρ.im ≠ 0) : RHz :=
  fun ρ hρ => rh_nonreal_of_hermitian_survival A hA hsurv ρ hρ (hreal ρ hρ)

/-! ### Anchors: the other rows, pinned by name so the atlas breaks if they change -/

example : GppRH.RiemannHypothesisStrip ↔ GppRH.AtomWeightOne := GppRH.rh_iff_atomWeightOne
example := @GppCasimirRH.riemannHypothesis_iff_casimir
example := @GppCasimirRH.riemannHypothesis_iff_centeredSq
example := @GppZeroQuartet.riemannHypothesis_iff_P_minus
example := @GppWeilCriterion.rh_of_twoPoint_kreinGraph_contraction
example := @GppWeilInterpolationBridge.rh_of_testPos_finiteInterpolation
example := @GppWeilInterpolationBridge.rh_of_testPos_pairSupportInterpolation
example := @GppWeilPolynomialInterpolation.rh_of_testPos_seed_polynomialClosure
example := @GppLogDerivZeroFree.riemannHypothesis_of_slit_log_derivative
example := @GppExpSumGrowth.bounded_exp_sum_re_nonpos
example {k : ℝ} (hk : 1 < k) :
    GppObserverPrincipalSeries.ObserverPositiveZeroSurvival k ↔ GppRH.RiemannHypothesisStrip :=
  GppObserverPrincipalSeries.observerPositiveZeroSurvival_iff_rh hk
example : GppObserverPrincipalSeries.CelestialPrincipalZeroSurvival ↔ GppRH.RiemannHypothesisStrip :=
  GppObserverPrincipalSeries.celestialPrincipalZeroSurvival_iff_rh
example := @GppObserverCasimirSpectralSurvival.critical_of_hermitian_casimir_eigenvector

end GppRHAtlas
