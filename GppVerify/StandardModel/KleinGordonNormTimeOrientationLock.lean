import Mathlib.Tactic

/-!
# Klein--Gordon norm locks frequency orientation to Cauchy-surface time orientation

For a complex Klein--Gordon plane wave with signed frequency

    phi_eta(t) = exp(-i eta omega t),    eta = +/-1, omega > 0,

the conserved KG inner-product density on a Cauchy surface with oriented future normal
sign `s=+/-1` is proportional to

    N = 2 omega s eta.

Thus, relative to one fixed Cauchy orientation, positive- and negative-frequency modes have
opposite KG norm signs.  Reversing BOTH the surface/time orientation and the phase-frequency
orientation preserves the norm.  Positivity therefore locks the admissible frequency sign
to the chosen time orientation.

This is the continuum-QFT sign mechanism behind the project's three-sign refinement: the
microscopic frequency/time-polarization sign is naturally a GLOBAL sheet/Cauchy-orientation
datum, not a freely assignable hidden bit on each particle.  Charge/representation
conjugation remains a separate internal operation.

Only the exact plane-wave sign algebra is formalized here; the conserved KG symplectic form
and its hypersurface independence are standard field-theory input.
-/

namespace GppKleinGordonNormTimeOrientationLock

/-- Binary sign with `false=+1`, `true=-1`. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

/-- Plane-wave KG norm density up to a positive spatial normalization factor. -/
def kgNormDensity (omega : ℝ) (surface frequency : Bool) : ℝ :=
  2 * omega * sg surface * sg frequency

/-- Reversing phase frequency alone reverses the KG norm sign. -/
theorem frequency_flip_reverses_norm (omega : ℝ) (s e : Bool) :
    kgNormDensity omega s (!e) = -kgNormDensity omega s e := by
  cases s <;> cases e <;> norm_num [kgNormDensity, sg]

/-- Reversing the Cauchy/time orientation alone also reverses the norm sign. -/
theorem surface_flip_reverses_norm (omega : ℝ) (s e : Bool) :
    kgNormDensity omega (!s) e = -kgNormDensity omega s e := by
  cases s <;> cases e <;> norm_num [kgNormDensity, sg]

/-- Reversing BOTH leaves the KG norm exactly invariant. -/
theorem diagonal_time_frequency_reversal_preserves_norm
    (omega : ℝ) (s e : Bool) :
    kgNormDensity omega (!s) (!e) = kgNormDensity omega s e := by
  cases s <;> cases e <;> norm_num [kgNormDensity, sg]

/-- For positive physical frequency magnitude, positive KG norm occurs exactly when the
    frequency orientation agrees with the Cauchy-surface time orientation. -/
theorem positive_KG_norm_iff_locked
    (omega : ℝ) (homega : 0 < omega) (s e : Bool) :
    0 < kgNormDensity omega s e ↔ s = e := by
  cases s <;> cases e <;> simp [kgNormDensity, sg, homega] <;> linarith

/-- On the reference future-oriented sheet, the conventional positive-frequency branch has
    positive KG norm. -/
theorem future_positive_frequency_positive_norm
    (omega : ℝ) (homega : 0 < omega) :
    0 < kgNormDensity omega false false := by
  simp [kgNormDensity, sg, homega]
  linarith

/-- The CPT-related opposite sheet can use the opposite phase winding and still have the
    same positive norm when its Cauchy orientation is reversed too. -/
theorem opposite_sheet_opposite_frequency_same_positive_norm
    (omega : ℝ) (homega : 0 < omega) :
    kgNormDensity omega true true = kgNormDensity omega false false ∧
    0 < kgNormDensity omega true true := by
  constructor
  · norm_num [kgNormDensity, sg]
  · simp [kgNormDensity, sg, homega]
    linarith

/-- A negative-frequency mode on the SAME oriented sheet has negative KG norm before the
    usual antiparticle/Fock reinterpretation. -/
theorem same_sheet_opposite_frequency_negative_norm
    (omega : ℝ) (homega : 0 < omega) :
    kgNormDensity omega false true < 0 := by
  simp [kgNormDensity, sg, homega]
  linarith

end GppKleinGordonNormTimeOrientationLock
