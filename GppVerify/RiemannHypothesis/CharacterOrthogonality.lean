import Mathlib.MeasureTheory.Group.Integral
import GppVerify.RiemannHypothesis.CompletedZetaDerivativeSymmetry
import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge

/-!
# Character orthogonality on groups with a left-invariant measure

Source: Tate's-thesis lecture notes (Warwick "tateweek4" notes, Lemma 4.15/Example 4.16)
— the classical orthogonality-of-characters fact used throughout Fourier analysis on
compact/adelic groups: for a left-invariant (e.g. Haar) measure `μ` and a multiplicative
character `χ`, `∫ χ dμ = 0` whenever `χ` is nontrivial.

This is genuine infrastructure toward the adelic/spectral machinery `AdelicL2.lean` and
`L2Constraint.lean` axiomatize (Meyer's spectral-Weil identity, Tate's functional equation),
built from Mathlib's existing left-invariant-measure integral theory rather than sourced
from any specific Golden-Physics-Project paper. The proof is pure translation-invariance
algebra — no compactness, integrability, or Haar-specific hypothesis is needed: both sides
are the Bochner-integral junk value `0` whenever `χ` fails to be integrable, so the result
holds unconditionally for any left-invariant measure.
-/

namespace GppCharacterOrthogonality

open MeasureTheory

/-- **Character orthogonality**: for a left-invariant measure `μ` on a group `G` and a
    multiplicative character `χ : G → ℂ` (`χ(g*x) = χ(g)*χ(x)` for all `g,x`), if `χ` is
    nontrivial at some point `h` (`χ(h) ≠ 1`) then `∫ χ dμ = 0`. -/
theorem integral_eq_zero_of_ne_one {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (χ : G → ℂ) (hχ : ∀ g x, χ (g * x) = χ g * χ x)
    {h : G} (hh : χ h ≠ 1) :
    ∫ x, χ x ∂μ = 0 := by
  have h1 : ∫ x, χ (h * x) ∂μ = ∫ x, χ x ∂μ := integral_mul_left_eq_self χ h
  simp_rw [hχ h] at h1
  rw [integral_const_mul] at h1
  have h2 : (χ h - 1) * ∫ x, χ x ∂μ = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hh
  · exact h3

end GppCharacterOrthogonality
