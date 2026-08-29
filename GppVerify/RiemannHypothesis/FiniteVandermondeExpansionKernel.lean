import Mathlib.Tactic

/-!
# Finite Vandermonde expansion kernel

Pointwise polynomial expansion underlying the arbitrary finite-support
Cauchy--Binet/Vandermonde identity.  Summing this identity against
`p i * p j * p k` converts each monomial into a product of raw moments.
-/

namespace GppFiniteVandermondeExpansionKernel

/-- Exact polynomial expansion of the squared three-point Vandermonde. -/
theorem vandermonde_sq_expansion (a b c : ℝ) :
    ((a - b) * (a - c) * (b - c)) ^ 2 =
      a^4*b^2 - 2*a^4*b*c + a^4*c^2
      - 2*a^3*b^3 + 2*a^3*b^2*c + 2*a^3*b*c^2 - 2*a^3*c^3
      + a^2*b^4 + 2*a^2*b^3*c - 6*a^2*b^2*c^2
      + 2*a^2*b*c^3 + a^2*c^4
      - 2*a*b^4*c + 2*a*b^3*c^2 + 2*a*b^2*c^3 - 2*a*b*c^4
      + b^4*c^2 - 2*b^3*c^3 + b^2*c^4 := by
  ring

end GppFiniteVandermondeExpansionKernel

#print axioms GppFiniteVandermondeExpansionKernel.vandermonde_sq_expansion
