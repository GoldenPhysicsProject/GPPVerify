import GppVerify.RiemannHypothesis.WeilInterpolationBridge
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Polynomial multiplier interpolation on finite Weil pair-supports

The preceding interpolation bridge isolates the exact finite-surjectivity target:
arbitrary values only on `S ∪ iota(S)` are needed.  Over `ℂ`, that finite
interpolation problem is algebraically automatic by Lagrange interpolation.

More importantly for an actual Mellin/Paley--Wiener test class, suppose the class
contains one transform `h` which is nonzero on the relevant finite support and is
closed under multiplication by polynomial functions of the spectral variable.
Then arbitrary data on that support can be interpolated by multiplying `h` by a
Lagrange polynomial.  Thus the remaining analytic burden is reduced from an
abstract surjectivity theorem to two concrete properties:

1. a nonvanishing seed transform on the required zero support;
2. closure of the admissible transform class under polynomial spectral multipliers.

This file proves only that algebraic reduction.  It does not assert that a specific
Weil/Mellin test class satisfies those two analytic properties, and makes no RH
claim by itself.
-/

namespace GppWeilPolynomialInterpolation

open Finset Polynomial
open GppWeilCriterion
open GppWeilInterpolationBridge

/-- Any prescribed complex data on a finite set are interpolated exactly by a
complex polynomial. -/
theorem exists_polynomial_interpolant
    (S : Finset ℂ) (c : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ z ∈ S, p.eval z = c z := by
  classical
  refine ⟨Lagrange.interpolate S (fun z : ℂ => z) c, ?_⟩
  intro z hz
  simpa using
    (Lagrange.eval_interpolate_at_node c Function.injective_id.injOn hz)

/-- If `h` has no zeros on a finite support, arbitrary values there can be
interpolated by a polynomial multiple `p(z) h(z)`. -/
theorem exists_polynomial_multiplier_interpolant
    (S : Finset ℂ) (h c : ℂ → ℂ)
    (hzero : ∀ z ∈ S, h z ≠ 0) :
    ∃ p : ℂ[X], ∀ z ∈ S, p.eval z * h z = c z := by
  obtain ⟨p, hp⟩ := exists_polynomial_interpolant S (fun z => c z / h z)
  refine ⟨p, ?_⟩
  intro z hz
  rw [hp z hz]
  field_simp [hzero z hz]

/-- Pair-support specialization: a single seed function nonvanishing on
`S ∪ iota(S)` generates arbitrary coefficient data there by polynomial
multiplication. -/
theorem exists_pairSupport_polynomial_multiplier
    (ι : ℂ → ℂ) (S : Finset ℂ) (h c : ℂ → ℂ)
    (hzero : ∀ z ∈ pairSupport ι S, h z ≠ 0) :
    ∃ p : ℂ[X], ∀ z ∈ pairSupport ι S,
      p.eval z * h z = c z := by
  exact exists_polynomial_multiplier_interpolant (pairSupport ι S) h c hzero

/-- Abstract transform-class form.  If a class has a seed element whose transform
is nonzero on a finite support, and every polynomial multiple of that seed is again
represented by an element of the class, then the class interpolates arbitrary data
on that support. -/
theorem finiteInterpolation_of_seed_polynomialClosure
    {T : Type*} (coeff : T → ℂ → ℂ)
    (S : Finset ℂ) (seed : T)
    (hzero : ∀ z ∈ S, coeff seed z ≠ 0)
    (hpoly : ∀ p : ℂ[X], ∃ f : T, ∀ z : ℂ,
      coeff f z = p.eval z * coeff seed z) :
    ∀ c : ℂ → ℂ, ∃ f : T, ∀ z ∈ S, coeff f z = c z := by
  intro c
  obtain ⟨p, hp⟩ :=
    exists_polynomial_multiplier_interpolant S (coeff seed) c hzero
  obtain ⟨f, hf⟩ := hpoly p
  refine ⟨f, ?_⟩
  intro z hz
  rw [hf z, hp z hz]

/-- **Seed-plus-polynomial-closure reduction to RH.**  Suppose admissible test
transforms are positive for every finite Weil paired form.  If, for every finite
zero support, the class contains one transform nonvanishing on the corresponding
pair-support and is closed under polynomial spectral multipliers of that seed,
then the finite interpolation hypothesis of `WeilInterpolationBridge` follows,
and hence so does the already-formalized Weil criterion conclusion.

The hypotheses are deliberately explicit: this theorem is a reduction, not a
proof that the analytic Mellin/Paley--Wiener class has these properties. -/
theorem rh_of_testPos_seed_polynomialClosure
    {T : Type*} (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ f : T,
      0 ≤ (pairedForm zetaInvolution S (coeff f)).re)
    (hseed : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros →
      ∃ seed : T, ∀ z ∈ pairSupport zetaInvolution S, coeff seed z ≠ 0)
    (hpoly : ∀ seed : T, ∀ p : ℂ[X], ∃ f : T, ∀ z : ℂ,
      coeff f z = p.eval z * coeff seed z) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_of_testPos_pairSupportInterpolation coeff htestPos
  intro S hSZ c
  obtain ⟨seed, hzero⟩ := hseed S hSZ
  exact finiteInterpolation_of_seed_polynomialClosure
    coeff (pairSupport zetaInvolution S) seed hzero (hpoly seed) c

end GppWeilPolynomialInterpolation

#print axioms GppWeilPolynomialInterpolation.exists_polynomial_interpolant
#print axioms GppWeilPolynomialInterpolation.exists_polynomial_multiplier_interpolant
#print axioms GppWeilPolynomialInterpolation.finiteInterpolation_of_seed_polynomialClosure
#print axioms GppWeilPolynomialInterpolation.rh_of_testPos_seed_polynomialClosure
