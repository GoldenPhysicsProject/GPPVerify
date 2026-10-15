import Mathlib.Tactic

/-!
# Algebraic four-orientation Dirac symbol and its massive Casimir square

Daniel Toupin / Golden Physics Project four-lift orientation carrier.
Codex/GPT discovery, 2026-10-15:
GPP-bridge/work/codex/2026-10-15_pole_density_resolvent_four_orientation_dirac.md

For a frequency a and mass b, the four-lift Clifford Dirac symbol is the
complex charge-flip block with opposite i*b couplings. Its square is
(a^2+b^2) times the identity, verified as an algebraic identity.

This file deliberately does NOT prove unbounded operator self-adjointness,
Fourier-Plancherel resolvent kernels, Weil positivity, or RH.
-/

namespace GppPoleMeanFourFaceDirac

/-- Coordinates are indexed by (q,t)=(++),(+-),(-+),(--). -/
structure FourState where
  pp : ℂ
  pm : ℂ
  mp : ℂ
  mm : ℂ

/-- Direct matrix action of a*Q + b*(i chi Q) on the complex four-lift. -/
def diracSymbol (a b : ℂ) (v : FourState) : FourState :=
  ⟨(a + b * Complex.I) * v.mp,
   (a - b * Complex.I) * v.mm,
   (a - b * Complex.I) * v.pp,
   (a + b * Complex.I) * v.pm⟩

theorem complex_mass_factor (a b : ℂ) :
    (a + b * Complex.I) * (a - b * Complex.I) = a ^ 2 + b ^ 2 := by
  calc
    (a + b * Complex.I) * (a - b * Complex.I) =
        a ^ 2 - b ^ 2 * Complex.I ^ 2 := by ring
    _ = a ^ 2 + b ^ 2 := by
      rw [Complex.I_sq]
      ring

theorem complex_mass_factor_rev (a b : ℂ) :
    (a - b * Complex.I) * (a + b * Complex.I) = a ^ 2 + b ^ 2 := by
  rw [mul_comm]
  exact complex_mass_factor a b

/-- The exact internal four-sector Clifford square.
The unbounded analytic Dirac realization remains a separate step. -/
theorem dirac_symbol_square (a b : ℂ) (v : FourState) :
    diracSymbol a b (diracSymbol a b v) =
      ⟨(a^2+b^2)*v.pp, (a^2+b^2)*v.pm,
       (a^2+b^2)*v.mp, (a^2+b^2)*v.mm⟩ := by
  cases v with
  | mk pp pm mp mm =>
    simp [diracSymbol, ← mul_assoc, complex_mass_factor, complex_mass_factor_rev]

/-- For the physical mass m=1/2 the Dirac square gives the critical
principal-series quadratic a²+1/4, algebraically, before any spectral calculus. -/
theorem critical_mass_square (a : ℂ) (v : FourState) :
    diracSymbol a (1/2) (diracSymbol a (1/2) v) =
      ⟨(a^2+1/4)*v.pp, (a^2+1/4)*v.pm,
       (a^2+1/4)*v.mp, (a^2+1/4)*v.mm⟩ := by
  convert dirac_symbol_square a (1/2 : ℂ) v using 1 <;> norm_num

end GppPoleMeanFourFaceDirac
