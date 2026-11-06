import GppVerify.RiemannHypothesis.ArithmeticConformalKinematics
import GppVerify.RiemannHypothesis.FunctionalEquation
import Mathlib.Tactic

/-!
# The one-dimensional Mellin/conformal weight and the RH-strength spectral obligation

This module makes the one-dimensional version of the arithmetic/celestial
parameter dictionary explicit. On the real scaling group, a conformal
primary of weight `Delta₁` has character `exp(x * Delta₁)` for logarithmic
scale `x`. The existing normalized arithmetic character is
`exp(x * (s - 1/2))`. Restoring its half-density Jacobian gives exactly
the primary character with `Delta₁ = s`, **without** the two-dimensional
rescaling `Delta₂ = 2s`.

This is an identity of scaling representations. It does not establish a full
one-dimensional local CFT, and an arbitrary complex Mellin label is not
automatically a unitary principal-series weight.

The second half states the zero-set question as an exact, non-circular
equivalence: all zeros of the genuine completed Riemann xi function carry
unitary one-dimensional principal weights iff all zeros lie on Re(s) = 1/2.
The forward assertion is **not** proved; it is the open arithmetic spectral
realization obligation. No axiom, sorry, or `True` stub is introduced.
-/

namespace GppOneDimensionalMellinWeight

open Complex GppArithmeticConformalKinematics GppScaleMass

/-- Scalar one-dimensional primary dilation character in logarithmic scale.
The plus-sign convention matches the (dual) Mellin character; reversing the
active/passive action inverts both characters without changing the weight. -/
noncomputable def conformalDilation (Delta₁ : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Delta₁)

/-- **Exact s = Delta₁ dilation identification.**
The normalized arithmetic mode, after restoring its half-density Jacobian,
is the one-dimensional conformal dilation character with weight exactly s. -/
theorem mellin_character_equals_1d_conformal_weight (s : ℂ) (x : ℝ) :
    logScaleCharacter s x * Complex.exp ((x : ℂ) / 2) =
      conformalDilation s x := by
  rw [logScaleCharacter_eq_exp]
  unfold conformalDilation
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The one-dimensional shadow involution Delta₁ ↦ 1 - Delta₁ is
the complementary scaling character. -/
theorem conformal_shadow_characters_multiply_to_jacobian
    (Delta₁ : ℂ) (x : ℝ) :
    conformalDilation (1 - Delta₁) x * conformalDilation Delta₁ x =
      Complex.exp (x : ℂ) := by
  unfold conformalDilation
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Principal-series condition in boundary dimension one. -/
def IsPrincipalDimensionOne (Delta₁ : ℂ) : Prop :=
  Delta₁.re = 1 / 2

/-- Exactly the one-dimensional principal axis is unitary under any
one nontrivial positive dilation, by the previously verified character norm. -/
theorem one_dimensional_principal_iff_unitary
    {s : ℂ} {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    IsPrincipalDimensionOne s ↔ ‖dilationCharacter s a‖ = 1 := by
  change s.re = 1 / 2 ↔ ‖dilationCharacter s a‖ = 1
  exact critical_line_iff_dilation_unitary ha ha1

/-- The exact completed-xi zero-location statement. This is a proposition
specifying the arithmetic spectral objective, not an asserted proof of RH. -/
def AllXiZerosPrincipalOne : Prop :=
  ∀ rho : ℂ, GppFE.riemannXi rho = 0 → IsPrincipalDimensionOne rho

/-- The corresponding one-dimensional principal-series *spectral obligation*:
each completed-zeta zero has a unit-modulus normalized character. -/
def AllXiZeroCharactersUnitaryAt (a : ℝ) : Prop :=
  ∀ rho : ℂ, GppFE.riemannXi rho = 0 → ‖dilationCharacter rho a‖ = 1

/-- **Exact bridge between RH and unitary occupancy of the 1D Mellin spectrum.**
At any fixed positive, nonidentity dilation, all xi zeros have principal-series
weights iff all xi-zero characters are unitary. Neither side is established here. -/
theorem all_xi_zeros_principal_iff_zero_characters_unitary
    {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    AllXiZerosPrincipalOne ↔ AllXiZeroCharactersUnitaryAt a := by
  change
    (∀ rho : ℂ, GppFE.riemannXi rho = 0 → IsPrincipalDimensionOne rho) ↔
    (∀ rho : ℂ, GppFE.riemannXi rho = 0 → ‖dilationCharacter rho a‖ = 1)
  constructor
  · intro h rho hz
    exact (one_dimensional_principal_iff_unitary ha ha1).mp (h rho hz)
  · intro h rho hz
    exact (one_dimensional_principal_iff_unitary ha ha1).mpr (h rho hz)

/-! ## Physical massless Klein-Gordon normalization in one boundary dimension -/

/-- The real radial growth factor in the massless Klein-Gordon overlap after
setting the positive energy scale omega = exp(u).  For boundary dimension d,
Pasterski-Shao, "A Conformal Basis for Flat Space Amplitudes", (4.7), gives
the radial density omega^(2*c-d-1) d omega. In logarithmic energy u this is
exp((2*c-d)*u) du. We record its exact scale dependence here; the
distributional delta-normalization of the full inner product is not
formalized in this module. -/
noncomputable def masslessKgLogRadialWeight (d c u : ℝ) : ℝ :=
  Real.exp ((2 * c - d) * u)

/-- For any nontrivial logarithmic rescaling, the physical radial KG weight
is scale invariant exactly at the principal-series real conformal weight. -/
theorem massless_kg_radial_scale_invariant_iff_principal
    (d c : ℝ) {u : ℝ} (hu : u ≠ 0) :
    masslessKgLogRadialWeight d c u = 1 ↔ c = d / 2 := by
  constructor
  · intro h
    have he : Real.exp ((2 * c - d) * u) = Real.exp 0 := by
      simpa [masslessKgLogRadialWeight] using h
    have hz : (2 * c - d) * u = 0 := Real.exp_injective he
    have hc : 2 * c - d = 0 := (mul_eq_zero.mp hz).resolve_right hu
    linarith
  · intro hc
    have hz : 2 * c - d = 0 := by linarith
    simp [masslessKgLogRadialWeight, hz]

/-- The physical massless one-dimensional KG radial growth is exactly
the squared norm of the existing half-density-normalized arithmetic dilation
character. This is the nontrivial norm-level bridge between the two
realizations of the same positive-scale Mellin representation. -/
theorem physical_one_dimensional_kg_growth_eq_arithmetic_norm_sq
    (s : ℂ) (u : ℝ) :
    masslessKgLogRadialWeight 1 s.re u =
      ‖dilationCharacter s (Real.exp u)‖ ^ 2 := by
  unfold masslessKgLogRadialWeight
  rw [norm_dilationCharacter, Real.log_exp, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Consequently the physical one-dimensional massless KG normalization
selects exactly the same principal axis as the arithmetic Mellin character. -/
theorem physical_massless_one_dimensional_principal_iff_kg_unitary
    {s : ℂ} {u : ℝ} (hu : u ≠ 0) :
    IsPrincipalDimensionOne s ↔ masslessKgLogRadialWeight 1 s.re u = 1 := by
  change s.re = 1 / 2 ↔ masslessKgLogRadialWeight 1 s.re u = 1
  exact (massless_kg_radial_scale_invariant_iff_principal 1 s.re hu).symm

end GppOneDimensionalMellinWeight

#print axioms GppOneDimensionalMellinWeight.mellin_character_equals_1d_conformal_weight
#print axioms GppOneDimensionalMellinWeight.conformal_shadow_characters_multiply_to_jacobian
#print axioms GppOneDimensionalMellinWeight.one_dimensional_principal_iff_unitary
#print axioms GppOneDimensionalMellinWeight.all_xi_zeros_principal_iff_zero_characters_unitary
