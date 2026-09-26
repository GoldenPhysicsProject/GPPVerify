import GppVerify.CelestialHolography.ArithmeticOSReflection
import Mathlib.Tactic

/-!
# Split-signature arithmetic spectral plane

The centered Mellin parameter already comes with two distinguished real coordinates

  sigma_A(s) = Re(s) - 1/2,
  tau_A(s)   = Im(s).

Rather than imposing the Euclidean form sigma_A^2 + tau_A^2, this file records the
split bilinear form for which these two coordinates are null coordinates:

  B_A(s,z) = sigma_A(s) tau_A(z) + tau_A(s) sigma_A(z),
  Q_A(s)   = B_A(s,s) = 2 sigma_A(s) tau_A(s).

Its null locus is therefore exactly the union of the critical line and the real axis.
The already-formalized arithmetic operations act on the two null coordinates in a
particularly simple way:

* complex conjugation flips tau_A only;
* arithmetic OS / Weil reflection `s -> 1-conj(s)` flips sigma_A only;
* positive-real inversion `s -> 1-s` flips both.

Hence the first two reverse the sign of Q_A while inversion preserves it. Under the
project dictionary Delta = 2s, the same split form is transported to the celestial
principal plane with the expected factor of four.

This is an exact algebraic split-signature structure on the centered spectral plane.
It is not, by itself, a claim that the Riemann critical line is selected dynamically or
that RH follows from nullity.
-/

namespace GppArithmeticSplitSignature

open GppPositiveReal
open GppArithmeticOS

/-- Centered real displacement from the arithmetic critical line. -/
noncomputable def sigmaA (s : ℂ) : ℝ := s.re - (1 : ℝ) / 2

/-- Arithmetic spectral coordinate along the critical line. -/
noncomputable def tauA (s : ℂ) : ℝ := s.im

/-- Split bilinear pairing in the arithmetic null coordinates `(sigma_A,tau_A)`. -/
noncomputable def splitPairingA (s z : ℂ) : ℝ :=
  sigmaA s * tauA z + tauA s * sigmaA z

/-- Associated split quadratic form. -/
noncomputable def splitFormA (s : ℂ) : ℝ := 2 * sigmaA s * tauA s

/-- The quadratic form is the self-pairing. -/
theorem splitPairingA_self (s : ℂ) :
    splitPairingA s s = splitFormA s := by
  unfold splitPairingA splitFormA
  ring

/-- The arithmetic split-null locus is exactly the critical line together with the
real axis. -/
theorem splitFormA_eq_zero_iff (s : ℂ) :
    splitFormA s = 0 ↔
      s.re = (1 : ℝ) / 2 ∨ s.im = 0 := by
  unfold splitFormA sigmaA tauA
  constructor
  · intro h
    have hprod : (s.re - (1 : ℝ) / 2) * s.im = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hs | ht
    · left
      linarith
    · right
      exact ht
  · rintro (hs | ht)
    · rw [hs]
      norm_num
    · rw [ht]
      ring

/-- In particular every point of the critical line is split-null. -/
theorem splitFormA_zero_on_critical {s : ℂ}
    (hs : s.re = (1 : ℝ) / 2) :
    splitFormA s = 0 := by
  rw [splitFormA_eq_zero_iff]
  exact Or.inl hs

/-- The real axis is the second split-null branch. -/
theorem splitFormA_zero_on_real_axis {s : ℂ}
    (hs : s.im = 0) :
    splitFormA s = 0 := by
  rw [splitFormA_eq_zero_iff]
  exact Or.inr hs

/-- Positive-real inversion flips both arithmetic null coordinates. -/
theorem sigmaA_criticalReflection (s : ℂ) :
    sigmaA (criticalReflection s) = - sigmaA s := by
  simp [sigmaA, criticalReflection]
  ring

/-- Positive-real inversion flips both arithmetic null coordinates. -/
theorem tauA_criticalReflection (s : ℂ) :
    tauA (criticalReflection s) = - tauA s := by
  simp [tauA, criticalReflection]

/-- Therefore positive-real inversion preserves the split quadratic form. -/
theorem splitFormA_criticalReflection (s : ℂ) :
    splitFormA (criticalReflection s) = splitFormA s := by
  unfold splitFormA
  rw [sigmaA_criticalReflection, tauA_criticalReflection]
  ring

/-- Complex conjugation fixes the transverse coordinate and flips spectral time. -/
theorem sigmaA_complexConj (s : ℂ) :
    sigmaA (complexConj s) = sigmaA s := by
  simp [sigmaA, complexConj]

/-- Complex conjugation flips only the critical-line spectral coordinate. -/
theorem tauA_complexConj (s : ℂ) :
    tauA (complexConj s) = - tauA s := by
  simp [tauA, complexConj]

/-- Hence conjugation reverses the split quadratic form. -/
theorem splitFormA_complexConj (s : ℂ) :
    splitFormA (complexConj s) = - splitFormA s := by
  unfold splitFormA
  rw [sigmaA_complexConj, tauA_complexConj]
  ring

/-- Arithmetic OS reflection flips the critical displacement and fixes spectral time. -/
theorem sigmaA_osReflection (s : ℂ) :
    sigmaA (osReflection s) = - sigmaA s := by
  simp [sigmaA, osReflection, criticalReflection, complexConj]
  ring

/-- Arithmetic OS reflection fixes the critical-line spectral coordinate. -/
theorem tauA_osReflection (s : ℂ) :
    tauA (osReflection s) = tauA s := by
  simp [tauA, osReflection, criticalReflection, complexConj]

/-- Thus arithmetic OS reflection reverses the split quadratic form. -/
theorem splitFormA_osReflection (s : ℂ) :
    splitFormA (osReflection s) = - splitFormA s := by
  unfold splitFormA
  rw [sigmaA_osReflection, tauA_osReflection]
  ring

/-- The two single-coordinate reflections compose to the two-coordinate arithmetic
reflection. -/
theorem criticalReflection_eq_os_after_conj (s : ℂ) :
    criticalReflection s = osReflection (complexConj s) := by
  apply Complex.ext <;>
    simp [criticalReflection, osReflection, complexConj]

/-- Celestial centered transverse coordinate corresponding to `Re Delta = 1`. -/
noncomputable def sigmaDelta (Delta : ℂ) : ℝ := Delta.re - 1

/-- Celestial principal-series spectral coordinate. -/
noncomputable def tauDelta (Delta : ℂ) : ℝ := Delta.im

/-- Split quadratic form on the celestial principal plane. -/
noncomputable def splitFormDelta (Delta : ℂ) : ℝ :=
  2 * sigmaDelta Delta * tauDelta Delta

/-- `Delta = 2s` doubles each null coordinate. -/
theorem sigmaDelta_celestialWeight (s : ℂ) :
    sigmaDelta (celestialWeight s) = 2 * sigmaA s := by
  simp [sigmaDelta, celestialWeight, sigmaA]
  ring

/-- `Delta = 2s` doubles the spectral coordinate as well. -/
theorem tauDelta_celestialWeight (s : ℂ) :
    tauDelta (celestialWeight s) = 2 * tauA s := by
  simp [tauDelta, celestialWeight, tauA]

/-- Consequently the celestial split form is four times the arithmetic split form. -/
theorem splitFormDelta_celestialWeight (s : ℂ) :
    splitFormDelta (celestialWeight s) = 4 * splitFormA s := by
  unfold splitFormDelta splitFormA
  rw [sigmaDelta_celestialWeight, tauDelta_celestialWeight]
  ring

end GppArithmeticSplitSignature

#print axioms GppArithmeticSplitSignature.splitFormA_eq_zero_iff
#print axioms GppArithmeticSplitSignature.splitFormA_criticalReflection
#print axioms GppArithmeticSplitSignature.splitFormA_complexConj
#print axioms GppArithmeticSplitSignature.splitFormA_osReflection
#print axioms GppArithmeticSplitSignature.splitFormDelta_celestialWeight
