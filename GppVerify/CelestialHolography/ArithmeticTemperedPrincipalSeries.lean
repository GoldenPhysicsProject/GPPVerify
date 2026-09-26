import GppVerify.RHSpectralMultiplicity
import GppVerify.CelestialHolography.ArithmeticSplitSignature
import Mathlib

/-!
# Tempered arithmetic generalized spectrum selects the principal series

The ordinary log-scale generator on `L²(ℝ)` has continuous spectrum, so a zeta zero
should not be identified with a nonzero `L²` point eigenvector.  The correct generalized
spectral question is instead whether the centered Mellin character

  u ↦ exp((Re ρ - 1/2) u)

defines a tempered distribution on Schwartz space.  The existing theorem
`GppRH.temperedness_iff_critical_line` says this happens exactly when the real growth
exponent vanishes.  This file transports that criterion into the arithmetic split-signature
notation and isolates the precise zero-to-temperedness bridge still required.

Important dependency boundary: `GppRH.temperedness_iff_critical_line` currently depends on
the custom axiom `GppRH.exp_growth_not_tempered`.  Therefore the theorems below are exact
conditional consequences of that axiom until it is retired; they are not an unconditional
proof of RH.
-/

namespace GppArithmeticTemperedPrincipalSeries

open GppArithmeticSplitSignature

/-- The centered arithmetic Mellin character defines a tempered functional. -/
def CenteredTempered (ρ : ℂ) : Prop :=
  ∃ T : SchwartzMap ℝ ℂ →L[ℝ] ℂ,
    ∀ φ : SchwartzMap ℝ ℂ,
      T φ = ∫ u : ℝ,
        Complex.exp (((ρ.re - (1 : ℝ) / 2 : ℝ) : ℂ) * (u : ℂ)) * (φ u : ℂ)

/-- Temperedness of the centered Mellin character is equivalent to the arithmetic
principal-series condition `Re ρ = 1/2`. -/
theorem centeredTempered_iff_principal (ρ : ℂ) :
    CenteredTempered ρ ↔ ρ.re = (1 : ℝ) / 2 := by
  unfold CenteredTempered
  rw [GppRH.temperedness_iff_critical_line (ρ.re - (1 : ℝ) / 2)]
  constructor <;> intro h <;> linarith

/-- Any tempered centered arithmetic spectral point lies on the critical/principal line. -/
theorem principal_of_centeredTempered {ρ : ℂ} (hρ : CenteredTempered ρ) :
    ρ.re = (1 : ℝ) / 2 :=
  (centeredTempered_iff_principal ρ).mp hρ

/-- In split-signature notation, a tempered centered spectral point lies on the
critical null branch. -/
theorem splitNull_of_centeredTempered {ρ : ℂ} (hρ : CenteredTempered ρ) :
    splitFormA ρ = 0 := by
  exact splitFormA_zero_on_critical (principal_of_centeredTempered hρ)

/-- Exact conditional RH-style reduction on the critical strip: if every zeta zero in the
strip gives a tempered centered Mellin functional, then every such zero lies on the
principal series.  The zero hypothesis is kept explicit so the missing arithmetic bridge
cannot be hidden in notation. -/
theorem zeta_zero_principal_of_centeredTempered
    {ρ : ℂ}
    (hzero : GppRH.riemannZeta ρ = 0)
    (hstrip : 0 < ρ.re ∧ ρ.re < 1)
    (htemp : CenteredTempered ρ) :
    ρ.re = (1 : ℝ) / 2 := by
  exact principal_of_centeredTempered htemp

/-- Family version: a zero-to-temperedness theorem is sufficient to place all zeros in the
critical strip on the arithmetic principal series. -/
theorem all_strip_zeros_principal_of_tempered_bridge
    (hbridge : ∀ ρ : ℂ,
      GppRH.riemannZeta ρ = 0 →
      0 < ρ.re ∧ ρ.re < 1 →
      CenteredTempered ρ) :
    ∀ ρ : ℂ,
      GppRH.riemannZeta ρ = 0 →
      0 < ρ.re ∧ ρ.re < 1 →
      ρ.re = (1 : ℝ) / 2 := by
  intro ρ hzero hstrip
  exact principal_of_centeredTempered (hbridge ρ hzero hstrip)

end GppArithmeticTemperedPrincipalSeries

#print axioms GppArithmeticTemperedPrincipalSeries.centeredTempered_iff_principal
#print axioms GppArithmeticTemperedPrincipalSeries.all_strip_zeros_principal_of_tempered_bridge
