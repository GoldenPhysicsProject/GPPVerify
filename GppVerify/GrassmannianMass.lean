import Mathlib.Tactic

/-!
# The Grassmannian Chart Transition and Zitterbewegung
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

## Statement

On the big cell of the Grassmannian Gr(2,4), a 2-plane is represented in the
chart U_{01} by A = [[a,b],[c,d]], via the row-reduced matrix [I | A]. The
transition to the chart U_{23} sends [I | A] to [A' | I] where
A' = A ε / det(A), ε = [[0,1],[-1,0]] -- the same orientation map τ that
appears in the companion paper (Mass as Orientation Coupling, Theorem 3.3(i)).
In coordinates,
  τ(a,b,c,d) = (-b, a, -d, c) / (ad - bc).

This map satisfies τ∘τ = -id exactly (Theorem `transition_transition_eq_neg`
below): applying the chart transition twice negates every coordinate, so
applying it four times returns to the start. This is the precise content of
"Zitterbewegung as a discrete chart oscillation": the oscillation has period
4, realizing the same τ² = -id structure that governs the fermion's internal
orientation dynamics in the companion paper -- not a period-2 complex
structure on the full tangent space, which this map does not have (see
below).

## What was here before, and why it changed

An earlier version of this file stated, as axioms, that (a) the Jacobian of
the transition map has "mean |eigenvalue| = 1/|det(A)|" via a `JacobianSpectrum`
structure that was never actually connected to the transition map (the axiom
was true by trivial construction of an unconstrained field, regardless of
what the real Jacobian does), and (b) that at the massless locus |det A| = 1
the Jacobian satisfies J² = -I. Claim (b) is false: direct computation, even
at the specific point (a,b,c,d) = (1,0,0,1) used as the illustration, gives
J² ≠ -I (checked directly; the nonzero off-diagonal entries of J²+I are not
small). The real invariant at that locus is J⁴ = I, a period-4 structure, not
J² = -I. This file replaces both axioms with the theorem that is actually
true and provable: τ∘τ = -id, unconditionally, for every (a,b,c,d) with
ad - bc ≠ 0.

## Independent verification

Verified by direct symbolic computation (SymPy) and by finite-difference
cross-check on random samples:
- τ(τ(a,b,c,d)) = (-a,-b,-c,-d) exactly, for all (a,b,c,d) with ad-bc ≠ 0.
- The Jacobian N of τ, cleared of denominators, satisfies the exact
  polynomial identity N⁴ = (ad-bc)⁴ • I; consequently every eigenvalue of
  the (unnormalized) chart-transition Jacobian has modulus exactly
  1/|ad-bc|.

  **This is now a proved Lean theorem, not just prose**: see
  `GrassmannianJacobian.lean` (`GppGrassmannianJacobian.N_pow_four_eq_D_pow_four_smul_one`),
  which defines N explicitly and proves N² = D•K, K² = D²•1, hence
  N⁴ = D⁴•1, entrywise via `Matrix.mul_apply` + `ring`, with no axiom and
  no `sorry`. The eigenvalue-modulus consequence itself (that these
  matrix identities imply every eigenvalue of N has modulus |D|) remains
  documented rather than formalized there: it needs "the eigenvalues of a
  real matrix, listed with multiplicity" machinery this project does not
  yet build.
-/

namespace GppGrassmannian

/-- Plücker coordinate p_{23} as the mass parameter m = |det(A)| for the
    2-plane represented by A = [[a,b],[c,d]] in the big cell of Gr(2,4). -/
def massParameter (a b c d : ℝ) : ℝ := |a * d - b * c|

/-- Chart transition map U_{01} → U_{23} on Gr(2,4), in coordinates:
    τ(a,b,c,d) = (-b,a,-d,c)/(ad-bc). This is exactly the orientation map
    τ(A) = A ε / det(A), ε = [[0,1],[-1,0]], of the companion paper. -/
noncomputable def transition (a b c d : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-b / (a * d - b * c), a / (a * d - b * c),
    -d / (a * d - b * c), c / (a * d - b * c))

/-- The determinant of the transitioned coordinates is the reciprocal of the
    original determinant: D ↦ 1/D. -/
theorem transition_det_eq (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    (-b / (a * d - b * c)) * (c / (a * d - b * c))
      - (a / (a * d - b * c)) * (-d / (a * d - b * c))
      = 1 / (a * d - b * c) := by
  field_simp
  ring

/-- The chart transition, applied twice, negates every coordinate:
    τ∘τ = -id. Equivalently (Zitterbewegung as chart oscillation), the
    transition map has order 4, since (-id)² = id. -/
theorem transition_transition_eq_neg (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    transition (-b / (a * d - b * c)) (a / (a * d - b * c))
        (-d / (a * d - b * c)) (c / (a * d - b * c))
      = (-a, -b, -c, -d) := by
  have hne : (-b / (a * d - b * c)) * (c / (a * d - b * c))
      - (a / (a * d - b * c)) * (-d / (a * d - b * c)) ≠ 0 := by
    rw [transition_det_eq a b c d hD]
    exact one_div_ne_zero hD
  simp only [transition, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [transition_det_eq a b c d hD] at hne ⊢
      field_simp
      try ring

end GppGrassmannian
