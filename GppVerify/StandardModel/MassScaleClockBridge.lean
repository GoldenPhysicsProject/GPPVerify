import Mathlib.Tactic
import GppVerify.StandardModel.OrientationMassTime

/-!
# Mass as a dimensionful scale and the Compton clock/ruler

A nonzero rest mass introduces the dimensionful invariant `m c^2`.  Quantum mechanics
turns that energy scale into an angular-frequency scale by division by `hbar` and into a
proper-time scale by inversion:

    omega_C = m c^2 / hbar,
    tau_C   = hbar / (m c^2).

Likewise the reduced Compton length is

    lambda_C = hbar / (m c) = c tau_C.

The exact identities below isolate the kinematic core of the program's phrase
"mass -> clock/ruler". They do not claim that every physical mass is dynamically generated
by spontaneous scale-symmetry breaking. The dynamical origin of `m` is a separate theory
question; once a nonzero mass scale exists, the reciprocal clock/ruler statements are exact.
-/

namespace GppMassScaleClockBridge

open GppOrientationMassTime

/-- Reduced Compton proper-time scale. -/
def comptonTime (m c hbar : ℝ) : ℝ := hbar / (m * c^2)

/-- The Compton clock and Compton time are exact reciprocals. -/
theorem comptonFrequency_mul_comptonTime
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    comptonFrequency m c hbar * comptonTime m c hbar = 1 := by
  simp [comptonFrequency, comptonTime]
  field_simp [hm, hc, hh]
  ring

/-- The reduced Compton ruler is light speed times the reduced Compton time. -/
theorem comptonLength_eq_c_mul_comptonTime
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    comptonLength m c hbar = c * comptonTime m c hbar := by
  simp [comptonLength, comptonTime]
  field_simp [hm, hc]
  ring

/-- Rest energy is Planck's constant times the Compton angular frequency. -/
theorem restEnergy_eq_hbar_mul_comptonFrequency
    (m c hbar : ℝ) (hh : hbar ≠ 0) :
    m * c^2 = hbar * comptonFrequency m c hbar := by
  simp [comptonFrequency]
  field_simp [hh]
  ring

/-- Scaling the mass by a nonzero factor scales the Compton frequency by the same factor. -/
theorem comptonFrequency_mass_scale
    (a m c hbar : ℝ) :
    comptonFrequency (a*m) c hbar = a * comptonFrequency m c hbar := by
  simp [comptonFrequency]
  ring

/-- Conversely the Compton time scales inversely with the mass scale. -/
theorem comptonTime_mass_scale
    (a m c hbar : ℝ) (ha : a ≠ 0) :
    comptonTime (a*m) c hbar = a⁻¹ * comptonTime m c hbar := by
  simp [comptonTime]
  field_simp [ha]
  ring

/-- Therefore the dimensionless phase product `omega_C * tau_C` is insensitive to a
reciprocal rescaling of clock and mass. -/
theorem reciprocal_mass_time_phase_invariant
    (a m c hbar : ℝ) (ha : a ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    comptonFrequency (a*m) c hbar * comptonTime (a*m) c hbar =
      comptonFrequency m c hbar * comptonTime m c hbar := by
  rw [comptonFrequency_mul_comptonTime (a*m) c hbar (mul_ne_zero ha hm) hc hh]
  rw [comptonFrequency_mul_comptonTime m c hbar hm hc hh]

end GppMassScaleClockBridge
