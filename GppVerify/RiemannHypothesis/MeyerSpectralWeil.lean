import GppVerify.RiemannHypothesis.WeilDistributionMultiplicative
import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.ConditionalWeightStateLine

/-!
# Meyer's spectral realization of the Weil distribution, as a named structure

Layer 2 of the full-construction brief (Daniel Toupin, via Turbo, 2026-11-06), first
deliverable: replace the stub `GppSpectralWeil.open_meyer_spectral_weil_identity : True`
by the real statement, carried as data.

**Meyer's theorem** (R. Meyer, *On a representation of the idele class group related to
primes and zeros of L-functions*, Duke Math. J. 127 (2005)): the Weil distribution is the
character of a virtual representation `π₊ ⊖ π₋` of the scaling action, with the **poles**
`s = 0, 1` carried by `π₊` and the **nontrivial zeros** carried by `π₋`, with multiplicity.
It is an external theorem; here it is a structure (`MeyerSpectralWeil`), not reproved and
not a Lean axiom. Its fields are the two traces, their spectral expansions, and the
character identity, stated as two separate equations (Turbo's audit, PR #11 comment
6701401306):

  `tr π₊ g = ĝ(0) + ĝ(1)`,  `tr π₋ g = Σ_ρ m(ρ) ĝ(ρ)`,
  `tr π₊ g − tr π₋ g = primeSide g − archimedeanTerm g`,

with the spectral transform `ĝ(s) = ∫ g(u) e^{(s − 1/2) u} du` (half-density centering, so
`ĝ(0) + ĝ(1) = poleTerm g`, proved as `poleSpectral_eq_poleTerm`) and `g` in the log-variable
test class of `GppArithmeticReflection` / `GppWeilMultiplicative`. The last equation is the
explicit formula rearranged (`Σ_ρ ĝ(ρ) = pole + arch − prime`).

**The target** (Sameness, form MEY): Meyer puts the zeros in `π₋`. The open statement is that
they also sit in a genuine unitary realization, i.e. every zero carrying `π₋`-multiplicity is a
weight state of a unitary dilation action (`MeyerTarget`). `rh_of_meyer` proves that this target
gives `Re ρ = 1/2` for every nontrivial zero. The structure alone does not; the target is
RH-strength and open.

Daniel Toupin / Golden Physics Project, with AI assistance from Turbo (statement, audit) and
Claude Code (Lean).
-/

namespace GppMeyerSpectralWeil

open MeasureTheory Complex GppWeilLadder GppArchimedeanFloor GppArithmeticReflection
  GppConditionalWeightState

/-- Spectral transform in the half-density centering: `ĝ(s) = ∫ g(u) e^{(s − 1/2) u} du`. -/
noncomputable def spectralTransform (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, (g u : ℂ) * Complex.exp ((s - 1 / 2) * u)

/-- The test class: smooth, compactly supported, in the log variable. -/
def IsTestFunction (g : ℝ → ℝ) : Prop := ContDiff ℝ ⊤ g ∧ HasCompactSupport g

/-- **Meyer's spectral realization, as data.** -/
structure MeyerSpectralWeil where
  /-- Multiplicity of a weight in `π₊`. -/
  multPlus : ℂ → ℕ
  /-- Multiplicity of a weight in `π₋`. -/
  multMinus : ℂ → ℕ
  /-- The traces of the two representations on test functions. -/
  tracePlus : (ℝ → ℝ) → ℂ
  traceMinus : (ℝ → ℝ) → ℂ
  /-- `π₊` carries exactly the poles. -/
  plus_poles : ∀ s, multPlus s ≠ 0 ↔ s = 0 ∨ s = 1
  /-- `π₋` carries exactly the nontrivial zeros. -/
  minus_zeros : ∀ s, multMinus s ≠ 0 ↔ s ∈ GppWeilCriterion.nontrivialZeros
  /-- Spectral expansion of `tr π₊`. -/
  tracePlus_spectral : ∀ g, IsTestFunction g →
    tracePlus g = spectralTransform g 0 + spectralTransform g 1
  /-- Spectral expansion of `tr π₋`, zeros counted with multiplicity. -/
  traceMinus_spectral : ∀ g, IsTestFunction g →
    traceMinus g = ∑' ρ : ℂ, (multMinus ρ : ℂ) * spectralTransform g ρ
  /-- The character identity (explicit formula, rearranged). -/
  character_identity : ∀ g, IsTestFunction g →
    tracePlus g - traceMinus g = (primeSide g : ℂ) - (archimedeanTerm g : ℂ)

/-- The target (Sameness, form MEY): the zero part of `π₋` is realized by weight states of a
unitary dilation action. Open; RH-strength. -/
def MeyerTarget (M : MeyerSpectralWeil) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (U : ℝ → H →ₗᵢ[ℂ] H), ∀ ρ, M.multMinus ρ ≠ 0 → IsWeightState U ρ

/-- **Conditional RH from Meyer's realization plus the target.** -/
theorem rh_of_meyer (M : MeyerSpectralWeil) (hT : MeyerTarget M) :
    ∀ ρ ∈ GppWeilCriterion.nontrivialZeros, ρ.re = 1 / 2 := by
  obtain ⟨H, i1, i2, U, hU⟩ := hT
  intro ρ hρ
  exact weight_state_re_half (hU ρ ((M.minus_zeros ρ).mpr hρ))

/-- The pole part of the spectral transform is the repo's `poleTerm`. -/
theorem poleSpectral_eq_poleTerm (g : ℝ → ℝ)
    (h0 : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp ((0 - 1 / 2) * u)))
    (h1 : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp ((1 - 1 / 2) * u))) :
    spectralTransform g 0 + spectralTransform g 1 = (poleTerm g : ℂ) := by
  unfold spectralTransform poleTerm
  have hc : ∀ u : ℝ, ((g u * (2 * Real.cosh (u / 2)) : ℝ) : ℂ) =
      (g u : ℂ) * Complex.exp ((0 - 1 / 2) * u) + (g u : ℂ) * Complex.exp ((1 - 1 / 2) * u) := by
    intro u
    push_cast
    rw [Complex.cosh]
    have e1 : ((0 : ℂ) - 1 / 2) * u = -((u : ℂ) / 2) := by ring
    have e2 : ((1 : ℂ) - 1 / 2) * u = (u : ℂ) / 2 := by ring
    rw [e1, e2]
    ring
  rw [show ((∫ u, g u * (2 * Real.cosh (u / 2)) : ℝ) : ℂ) =
      ∫ u, ((g u * (2 * Real.cosh (u / 2)) : ℝ) : ℂ) from integral_ofReal.symm]
  simp_rw [hc]
  exact (integral_add h0 h1).symm

end GppMeyerSpectralWeil

#print axioms GppMeyerSpectralWeil.rh_of_meyer
#print axioms GppMeyerSpectralWeil.poleSpectral_eq_poleTerm
