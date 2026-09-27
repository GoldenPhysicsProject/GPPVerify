import GppVerify.QuantumGravity.StefanBoltzmannFamily

/-!
# Normalized celestial spectral-weight moment family

This module repackages the already-proved Stefan–Boltzmann/Mellin family at the
normalization used by the bilateral celestial/chamber probability density

  rho(lam) = (2/pi) * P(lam),   P(lam) = pi*lam/sinh(pi*lam).

For exponents for which the integrand is even (in particular the integer sequence
`s = 2n+1`), the factor `4/pi` multiplying the positive half-line integral is exactly
the full-line rho moment.  The theorem below is stated for every real `s > 0` as a
half-line identity, so no parity assumption is hidden in the formal statement.
-/

namespace GppSpectralWeightMomentFamily

open MeasureTheory Real Set
open GppStefanBoltzmann

/-- The normalized doubled-half-line moment family.  It is an algebraic consequence
of `stefan_boltzmann_family`, with the probability normalization made explicit. -/
theorem normalized_doubled_halfline_moment_family {s : ℝ} (hs : 0 < s) :
    (4 / π) * ∫ lam in Ioi (0 : ℝ), lam ^ (s - 1) * P lam
      = 8 * (π ^ (-(s + 1)) * (1 - 2 ^ (-(s + 1))) * Real.Gamma (s + 1) *
          ∑' n : ℕ, 1 / (n : ℝ) ^ (s + 1)) := by
  have h := stefan_boltzmann_family (s := s) hs
  calc
    (4 / π) * ∫ lam in Ioi (0 : ℝ), lam ^ (s - 1) * P lam
        = 8 * ((1 / (2 * π)) * ∫ lam in Ioi (0 : ℝ), lam ^ (s - 1) * P lam) := by
            field_simp [Real.pi_ne_zero]
            <;> ring
    _ = 8 * (π ^ (-(s + 1)) * (1 - 2 ^ (-(s + 1))) * Real.Gamma (s + 1) *
          ∑' n : ℕ, 1 / (n : ℝ) ^ (s + 1)) := by rw [h]

/-- The celestial spectral weight has unit mass in the normalized doubled-half-line
convention: `(4/pi) * integral_0^infty P = 1`.  For the even function `P`, this is
the full-line normalization of `rho = (2/pi) P`. -/
theorem normalized_spectral_weight_mass :
    (4 / π) * ∫ lam in Ioi (0 : ℝ), P lam = 1 := by
  have h := GppStefanBoltzmann.m_one_eq
  norm_num at h ⊢
  have hp : π ≠ 0 := Real.pi_ne_zero
  calc
    (4 / π) * ∫ lam in Ioi (0 : ℝ), P lam
        = 8 * ((1 / (2 * π)) * ∫ lam in Ioi (0 : ℝ), P lam) := by
            field_simp [hp]
            <;> ring
    _ = 8 * (1 / 8) := by rw [← h]; ring
    _ = 1 := by norm_num

end GppSpectralWeightMomentFamily
