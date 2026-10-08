import GppVerify.RiemannHypothesis.ArrowDictionaryFiniteAlgebra
import GppVerify.RiemannHypothesis.FiniteHaarQuotientPrincipalSeries
import GppVerify.RiemannHypothesis.CasimirCriticalLine
import GppVerify.RiemannHypothesis.ShadowSymmetry
import GppVerify.RiemannHypothesis.TomitaRatioFlow
import GppVerify.RHSpectralMultiplicity
import Mathlib.Tactic

/-!
# Observer positivity, functional-equation pairing, and the principal series

This module formalizes the October 2026 "same record direction" version of the
orientation/RH idea.

The finite-Haar transport already has the exact norm law

  ||T_s(k)|| = exp(log(k) * (1/2 - Re s)).

For `k > 1`, a parameter above the critical line is contractive and one below
the line is expansive.  The functional-equation/complete-reversal companion is

  D(s) = 1 - conj(s),

which reverses the centered bias.  A thermodynamic observer uses one common
record orientation for both microscopic lifts, so the mathematically testable
positivity condition is that **both** members of the D-pair are non-amplifying
in that same observer norm.

The main finite theorem here is therefore

  ||T_s(k)|| <= 1  and  ||T_{D(s)}(k)|| <= 1
      iff Re s = 1/2.

This is strictly weaker in input than demanding a unitary realization and is
the one-sided reflected-contraction mechanism already available locally.

The module then packages three consequences:

* the observer-positive pair is fixed by complete reversal;
* its conformal Casimir is real and in the principal-series range;
* under Delta = 2s it lies on the celestial principal series Re Delta = 1.

Finally it states the exact global missing bridge.  "Every critical-strip zeta
zero survives in an observer-positive reflected pair" is equivalent to RH on
the strip.  Likewise "every zero maps to a celestial principal-series label
Delta = 2 rho" is equivalent to RH.  These equivalences are deliberately
honest: this file does not prove the zero-survival/positivity hypothesis.

For an off-line zero the classical functional equation plus conjugation gives a
second distinct zero at the same ordinate.  Such a zero cannot satisfy the
observer-positive reflected-pair condition.

No RH claim is made.
-/

namespace GppObserverPrincipalSeries

open Complex

abbrev reversal := GppRHArrowDictionary.reversal
abbrev haarQuotientCharacter :=
  GppFiniteHaarQuotientPrincipalSeries.haarQuotientCharacter

/-- Both microscopic orientations are non-amplifying in one common observer
(record-oriented) Haar norm. -/
def ObserverPositivePair (s : ℂ) (k : ℝ) : Prop :=
  ‖haarQuotientCharacter s k‖ ≤ 1 ∧
    ‖haarQuotientCharacter (reversal s) k‖ ≤ 1


/-- The two complete-reversal transport norms are exact reciprocals.  Their
product is one before imposing any positivity or zero condition. -/
theorem reflected_norm_product_eq_one (s : ℂ) (k : ℝ) :
    ‖haarQuotientCharacter s k‖ *
      ‖haarQuotientCharacter (reversal s) k‖ = 1 := by
  rw [GppFiniteHaarQuotientPrincipalSeries.norm_haarQuotientCharacter,
    GppFiniteHaarQuotientPrincipalSeries.norm_haarQuotientCharacter]
  rw [← Real.exp_add]
  have href : (reversal s).re = 1 - s.re := by
    simp [reversal, GppRHArrowDictionary.reversal]
  rw [href]
  ring_nf
  simp

/-- Away from the critical line, the complete-reversal pair is necessarily
a strict contraction/expansion pair in the same observer norm.  This is the
finite-Haar version of the statement that a common record orientation cannot
make both off-line lifts non-amplifying. -/
theorem off_critical_reflected_pair_splits
    {s : ℂ} {k : ℝ} (hk : 1 < k)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    (1 < ‖haarQuotientCharacter s k‖ ∧
        ‖haarQuotientCharacter (reversal s) k‖ < 1) ∨
      (‖haarQuotientCharacter s k‖ < 1 ∧
        1 < ‖haarQuotientCharacter (reversal s) k‖) := by
  rcases lt_or_gt_of_ne hoff with hs | hs
  · left
    constructor
    · exact GppFiniteHaarQuotientPrincipalSeries.subcritical_haar_quotient_expands hk hs
    · apply GppFiniteHaarQuotientPrincipalSeries.supercritical_haar_quotient_contracts hk
      simp [reversal, GppRHArrowDictionary.reversal]
      linarith
  · right
    constructor
    · exact GppFiniteHaarQuotientPrincipalSeries.supercritical_haar_quotient_contracts hk hs
    · apply GppFiniteHaarQuotientPrincipalSeries.subcritical_haar_quotient_expands hk
      simp [reversal, GppRHArrowDictionary.reversal]
      linarith

/-- **Two-sided observer positivity selects the principal line.**
For any nontrivial finite Haar quotient `k > 1`, simultaneous contractivity of
a parameter and its complete-reversal companion is equivalent to
`Re s = 1/2`. -/
theorem observerPositivePair_iff_critical
    {s : ℂ} {k : ℝ} (hk : 1 < k) :
    ObserverPositivePair s k ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    exact
      GppFiniteHaarQuotientPrincipalSeries.critical_line_of_reflected_quotient_contractions
        hk h.1 h.2
  · intro hs
    have hk0 : 0 < k := lt_trans zero_lt_one hk
    have hk1 : k ≠ 1 := ne_of_gt hk
    constructor
    · have hnorm :=
        (GppFiniteHaarQuotientPrincipalSeries.critical_line_iff_haar_quotient_isometry
          (s := s) (k := k) hk0 hk1).1 hs
      exact le_of_eq hnorm
    · have href : (reversal s).re = (1 : ℝ) / 2 := by
        simp [reversal, GppRHArrowDictionary.reversal, hs]
      have hnorm :=
        (GppFiniteHaarQuotientPrincipalSeries.critical_line_iff_haar_quotient_isometry
          (s := reversal s) (k := k) hk0 hk1).1 href
      exact le_of_eq hnorm

/-- The finite critical Tomita/KMS modular label `s = 1/2 + i t`
automatically satisfies observer positivity in every nontrivial finite-Haar
quotient.  This connects the existing modular-ratio principal-series theorem to
the common-record contraction criterion without any zeta-zero input. -/
theorem tomita_principal_label_observer_positive
    (t : ℝ) {k : ℝ} (hk : 1 < k) :
    ObserverPositivePair
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) k := by
  apply (observerPositivePair_iff_critical hk).2
  simp

/-- The same Tomita/KMS label maps under `Delta = 2s` to the celestial
principal series. -/
theorem tomita_principal_label_celestial
    (t : ℝ) :
    (2 * ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 1 := by
  simp

/-- Observer-positive reflected transport is pointwise fixed by the complete
anti-linear reversal `s -> 1-conj(s)`. -/
theorem observerPositivePair_forces_reversal_fixed
    {s : ℂ} {k : ℝ} (hk : 1 < k) (hobs : ObserverPositivePair s k) :
    reversal s = s := by
  have hs : s.re = (1 : ℝ) / 2 :=
    (observerPositivePair_iff_critical hk).1 hobs
  have hbias : GppRHArrowDictionary.orientationBias s = 0 :=
    (GppRHArrowDictionary.orientationBias_eq_zero_iff s).2 hs
  exact (GppRHArrowDictionary.orientationBias_eq_zero_iff_fixed s).1 hbias

/-- Complete reversal conjugates the quadratic Casimir.  Thus an off-line
D-pair carries conjugate Casimir values rather than two independent real
eigenvalues. -/
theorem casimir_reversal_eq_conj (s : ℂ) :
    GppCasimirCriticalLine.casimir (reversal s) =
      (starRingEnd ℂ) (GppCasimirCriticalLine.casimir s) := by
  simp [GppCasimirCriticalLine.casimir, reversal, GppRHArrowDictionary.reversal]
  ring

/-- For a nonreal spectral label, the two conjugate Casimir values collapse to
one value exactly on the critical line. -/
theorem casimir_reversal_collapse_iff_critical
    {s : ℂ} (him : s.im ≠ 0) :
    GppCasimirCriticalLine.casimir (reversal s) =
        GppCasimirCriticalLine.casimir s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have hc : (GppCasimirCriticalLine.casimir s).im = 0 := by
      have hi := congrArg Complex.im h
      rw [casimir_reversal_eq_conj] at hi
      simp at hi
      linarith
    exact GppCasimirCriticalLine.real_casimir_forces_half s him hc
  · intro hs
    have hfixed : reversal s = s := by
      have hbias : GppRHArrowDictionary.orientationBias s = 0 :=
        (GppRHArrowDictionary.orientationBias_eq_zero_iff s).2 hs
      exact (GppRHArrowDictionary.orientationBias_eq_zero_iff_fixed s).1 hbias
    rw [hfixed]

/-- The observer-positive pair has a real conformal Casimir in the
principal-series range `c >= 1/4`. -/
theorem observerPositivePair_forces_casimir_positive
    {s : ℂ} {k : ℝ} (hk : 1 < k) (hobs : ObserverPositivePair s k) :
    (GppCasimirCriticalLine.casimir s).im = 0 ∧
      (1 : ℝ) / 4 ≤ (GppCasimirCriticalLine.casimir s).re := by
  have hs : s.re = (1 : ℝ) / 2 :=
    (observerPositivePair_iff_critical hk).1 hobs
  exact (GppCasimirCriticalLine.casimir_ge_quarter_iff s).2 hs

/-- Under the exact celestial dictionary `Delta = 2s`, observer positivity
puts the label on the celestial principal series `Re Delta = 1`. -/
theorem observerPositivePair_forces_celestial_principal
    {s : ℂ} {k : ℝ} (hk : 1 < k) (hobs : ObserverPositivePair s k) :
    (2 * s).re = 1 := by
  have hs : s.re = (1 : ℝ) / 2 :=
    (observerPositivePair_iff_critical hk).1 hobs
  exact (GppShadow.critical_lines_coincide s).2 hs

/-- Global missing bridge: every zeta zero in the open critical strip survives
as an observer-positive reflected pair in the same finite-Haar quotient norm. -/
def ObserverPositiveZeroSurvival (k : ℝ) : Prop :=
  ∀ rho : ℂ, riemannZeta rho = 0 →
    0 < rho.re → rho.re < 1 → ObserverPositivePair rho k

/-- If the arithmetic construction supplies observer-positive survival of every
strip zero, RH on the strip follows immediately. -/
theorem rh_of_observerPositiveZeroSurvival
    {k : ℝ} (hk : 1 < k) (h : ObserverPositiveZeroSurvival k) :
    GppRH.RiemannHypothesisStrip := by
  intro rho hzero h0 h1
  exact (observerPositivePair_iff_critical hk).1 (h rho hzero h0 h1)

/-- Conversely, RH makes every strip zero an observer-positive reflected pair.
Thus the survival condition is an exact reformulation of the missing global
theorem, not an independently proved shortcut. -/
theorem observerPositiveZeroSurvival_of_rh
    {k : ℝ} (hk : 1 < k) (h : GppRH.RiemannHypothesisStrip) :
    ObserverPositiveZeroSurvival k := by
  intro rho hzero h0 h1
  exact (observerPositivePair_iff_critical hk).2 (h rho hzero h0 h1)

/-- Honest equivalence: for any `k>1`, observer-positive survival of all strip
zeros is equivalent to RH on the strip. -/
theorem observerPositiveZeroSurvival_iff_rh
    {k : ℝ} (hk : 1 < k) :
    ObserverPositiveZeroSurvival k ↔ GppRH.RiemannHypothesisStrip :=
  ⟨rh_of_observerPositiveZeroSurvival hk,
    observerPositiveZeroSurvival_of_rh hk⟩

/-- The statement that every strip zero maps under `Delta=2 rho` to the
celestial principal series. -/
def CelestialPrincipalZeroSurvival : Prop :=
  ∀ rho : ℂ, riemannZeta rho = 0 →
    0 < rho.re → rho.re < 1 → (2 * rho).re = 1

/-- "Every Riemann zero comes with the celestial principal series" is exactly
RH on the strip under the already-formalized dictionary `Delta=2s`. -/
theorem celestialPrincipalZeroSurvival_iff_rh :
    CelestialPrincipalZeroSurvival ↔ GppRH.RiemannHypothesisStrip := by
  constructor
  · intro h rho hzero h0 h1
    exact (GppShadow.critical_lines_coincide rho).1 (h rho hzero h0 h1)
  · intro h rho hzero h0 h1
    exact (GppShadow.critical_lines_coincide rho).2 (h rho hzero h0 h1)

/-- An off-line strip zero produces the distinct functional-equation/conjugate
companion at the same ordinate and simultaneously violates observer positivity.
This packages the "zeros double off the line" observation with the common-record
positivity obstruction. -/
theorem off_line_zero_pair_and_observer_obstruction
    {rho : ℂ} {k : ℝ}
    (hk : 1 < k)
    (hzero : riemannZeta rho = 0)
    (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ (1 : ℝ) / 2) :
    (∃ rho' : ℂ,
        rho' ≠ rho ∧ riemannZeta rho' = 0 ∧ rho'.im = rho.im) ∧
      ¬ ObserverPositivePair rho k := by
  constructor
  · exact GppRH.two_zeros_at_ordinate rho hzero hstrip hoff
  · intro hobs
    exact hoff ((observerPositivePair_iff_critical hk).1 hobs)

end GppObserverPrincipalSeries

#print axioms GppObserverPrincipalSeries.reflected_norm_product_eq_one
#print axioms GppObserverPrincipalSeries.off_critical_reflected_pair_splits
#print axioms GppObserverPrincipalSeries.observerPositivePair_iff_critical
#print axioms GppObserverPrincipalSeries.tomita_principal_label_observer_positive
#print axioms GppObserverPrincipalSeries.tomita_principal_label_celestial
#print axioms GppObserverPrincipalSeries.observerPositivePair_forces_reversal_fixed
#print axioms GppObserverPrincipalSeries.casimir_reversal_eq_conj
#print axioms GppObserverPrincipalSeries.casimir_reversal_collapse_iff_critical
#print axioms GppObserverPrincipalSeries.observerPositivePair_forces_casimir_positive
#print axioms GppObserverPrincipalSeries.observerPositivePair_forces_celestial_principal
#print axioms GppObserverPrincipalSeries.observerPositiveZeroSurvival_iff_rh
#print axioms GppObserverPrincipalSeries.celestialPrincipalZeroSurvival_iff_rh
#print axioms GppObserverPrincipalSeries.off_line_zero_pair_and_observer_obstruction
