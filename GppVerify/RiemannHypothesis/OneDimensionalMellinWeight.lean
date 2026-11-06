import GppVerify.RiemannHypothesis.ArithmeticConformalKinematics
import GppVerify.RiemannHypothesis.FunctionalEquation
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree
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
  ∀ rho : ℂ, GppLogDerivZeroFree.xi rho = 0 → IsPrincipalDimensionOne rho

/-- The corresponding one-dimensional principal-series *spectral obligation*:
each completed-zeta zero has a unit-modulus normalized character. -/
def AllXiZeroCharactersUnitaryAt (a : ℝ) : Prop :=
  ∀ rho : ℂ, GppLogDerivZeroFree.xi rho = 0 → ‖dilationCharacter rho a‖ = 1

/-- **Exact bridge between RH and unitary occupancy of the 1D Mellin spectrum.**
At any fixed positive, nonidentity dilation, all xi zeros have principal-series
weights iff all xi-zero characters are unitary. Neither side is established here. -/
theorem all_xi_zeros_principal_iff_zero_characters_unitary
    {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    AllXiZerosPrincipalOne ↔ AllXiZeroCharactersUnitaryAt a := by
  change
    (∀ rho : ℂ, GppLogDerivZeroFree.xi rho = 0 → IsPrincipalDimensionOne rho) ↔
    (∀ rho : ℂ, GppLogDerivZeroFree.xi rho = 0 → ‖dilationCharacter rho a‖ = 1)
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


/-! ## Entire completion and endpoint regression checks

The legacy product GppFE.riemannXi has artificial zeros at 0 and 1 because
Lean assigns finite values to completedRiemannZeta at its poles. Use the
existing entire completion for all zero-location propositions above.
-/

theorem legacy_xi_zero : GppFE.riemannXi 0 = 0 := by
  simp [GppFE.riemannXi]

theorem legacy_xi_one : GppFE.riemannXi 1 = 0 := by
  simp [GppFE.riemannXi]

theorem entire_xi_zero : GppLogDerivZeroFree.xi 0 = (1 / 2 : ℂ) := by
  norm_num [GppLogDerivZeroFree.xi]

theorem entire_xi_one : GppLogDerivZeroFree.xi 1 = (1 / 2 : ℂ) := by
  norm_num [GppLogDerivZeroFree.xi]

/-- The old unrestricted zero-location target was false, independently of RH. -/
theorem legacy_all_zeros_principal_false :
    ¬ (∀ rho : ℂ, GppFE.riemannXi rho = 0 → IsPrincipalDimensionOne rho) := by
  intro h
  have h0 := h 0 legacy_xi_zero
  norm_num [IsPrincipalDimensionOne] at h0

/-- Away from the two removable singularities, the correction changes no values. -/
theorem entire_xi_eq_legacy {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    GppLogDerivZeroFree.xi s = GppFE.riemannXi s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold GppLogDerivZeroFree.xi GppFE.riemannXi
  rw [completedRiemannZeta_eq]
  field_simp
  <;> ring

/-- The precise remaining arithmetic normalization statement, with the entire xi. -/
def AllXiZerosKGNormalized : Prop :=
  ∀ rho : ℂ, GppLogDerivZeroFree.xi rho = 0 →
    masslessKgLogRadialWeight 1 rho.re 1 = 1

theorem all_xi_zeros_kg_normalized_iff_principal :
    AllXiZerosKGNormalized ↔ AllXiZerosPrincipalOne := by
  constructor
  · intro h rho hz
    exact (physical_massless_one_dimensional_principal_iff_kg_unitary
      (s := rho) (u := 1) (by norm_num)).mpr (h rho hz)
  · intro h rho hz
    exact (physical_massless_one_dimensional_principal_iff_kg_unitary
      (s := rho) (u := 1) (by norm_num)).mp (h rho hz)

/-- Conditional only: this theorem does not assert AllXiZerosKGNormalized. -/
theorem riemannHypothesis_of_all_xi_zeros_kg_normalized
    (hkg : AllXiZerosKGNormalized) : RiemannHypothesis := by
  have hprincipal := all_xi_zeros_kg_normalized_iff_principal.mp hkg
  intro s hz htriv h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hg : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      exact htriv ⟨m, by rw [hn]; push_cast; ring⟩
  exact hprincipal s (GppLogDerivZeroFree.xi_eq_zero_of_zeta_zero hz hs0 h1 hg)

#print axioms legacy_all_zeros_principal_false
#print axioms entire_xi_eq_legacy
#print axioms riemannHypothesis_of_all_xi_zeros_kg_normalized

end GppOneDimensionalMellinWeight

#print axioms GppOneDimensionalMellinWeight.mellin_character_equals_1d_conformal_weight
#print axioms GppOneDimensionalMellinWeight.conformal_shadow_characters_multiply_to_jacobian
#print axioms GppOneDimensionalMellinWeight.one_dimensional_principal_iff_unitary
#print axioms GppOneDimensionalMellinWeight.all_xi_zeros_principal_iff_zero_characters_unitary
