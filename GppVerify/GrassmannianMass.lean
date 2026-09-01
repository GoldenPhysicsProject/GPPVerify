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
  -- Mathlib 4.33: `field_simp` leaves the determinant in whichever commuted form its
  -- normal form produces (`-(c*b) + a*d` in one branch, `d*a - b*c` in another). It can
  -- only clear a denominator it can see is nonzero, and `hD` is stated as `a*d - b*c`, so
  -- two of the four branches kept an uncleared `⁻¹` and `ring` could not finish. Supply
  -- the same fact in both commuted shapes — in the context, where `field_simp` picks them up
  -- as side conditions (passing them as simp args instead makes it treat them as rewrite
  -- rules and it still fails).
  have hD1 : -(c * b) + a * d ≠ 0 := fun h => hD (by linear_combination h)
  have hD2 : d * a - b * c ≠ 0 := fun h => hD (by linear_combination h)
  simp only [transition, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [transition_det_eq a b c d hD] at hne ⊢
      -- Mathlib 4.33: applied directly to `X = Y`, `field_simp` leaves two of the four
      -- branches carrying an uncleared `(…)⁻¹` that `ring` cannot finish. Moving
      -- everything to one side first gives it a shape it does clear, uniformly.
      rw [← sub_eq_zero]
      field_simp
      try ring
      -- A second pass: the first `field_simp` leaves two of the four branches with an
      -- uncleared `(…)⁻¹`, which it does clear when re-applied to that residual shape.
      try field_simp
      try ring

/-- The chart transition as a self-map of the coordinate 4-tuple, so that "applied four
    times" is literally `tauMap^[4]` rather than a chain of hand-substituted arguments. -/
noncomputable def tauMap (p : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  transition p.1 p.2.1 p.2.2.1 p.2.2.2

/-- `τ² = -id` in tuple form — `transition_transition_eq_neg` with the intermediate
    coordinates folded into the map rather than written out. -/
theorem tauMap_tauMap (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tauMap (tauMap (a, b, c, d)) = (-a, -b, -c, -d) :=
  transition_transition_eq_neg a b c d hD

/-- Negating all four coordinates leaves the determinant unchanged:
    `(-a)(-d) - (-b)(-c) = ad - bc`. This is what lets `τ²` be applied a second time. -/
theorem det_neg (a b c d : ℝ) : -a * -d - -b * -c = a * d - b * c := by ring

/-- **`τ⁴ = id`** (Theorem 3.3(i), second clause). The file docstring above has asserted
    since this file was written that "applying it four times returns to the start"; here
    that is actually proved, rather than left to the reader as a consequence of
    `transition_transition_eq_neg`.

    The one step that needs an argument is that `τ²` may be applied a *second* time at all:
    it is conditional on a nonvanishing determinant, and the point it is applied to is the
    negated tuple. `det_neg` supplies exactly that — negation preserves `ad - bc`, so the
    same hypothesis `hD` discharges both applications. -/
theorem tauMap_iterate_four (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tauMap^[4] (a, b, c, d) = (a, b, c, d) := by
  have hDneg : -a * -d - -b * -c ≠ 0 := by rw [det_neg]; exact hD
  have h2 : tauMap (tauMap (a, b, c, d)) = (-a, -b, -c, -d) := tauMap_tauMap a b c d hD
  have h4 : tauMap (tauMap (-a, -b, -c, -d)) = (- -a, - -b, - -c, - -d) :=
    tauMap_tauMap (-a) (-b) (-c) (-d) hDneg
  show tauMap (tauMap (tauMap (tauMap (a, b, c, d)))) = (a, b, c, d)
  rw [h2, h4, neg_neg, neg_neg, neg_neg, neg_neg]

/-- The period is exactly 4, not 2: `τ² = -id` is not the identity unless the coordinates
    all vanish — which the chart excludes, since `ad - bc ≠ 0` forces some coordinate
    nonzero. Stated because "order 4" is the claim the Zitterbewegung reading rests on, and
    an order-2 map would satisfy `τ⁴ = id` just as well. -/
theorem tauMap_tauMap_ne_self (a b c d : ℝ) (hD : a * d - b * c ≠ 0) :
    tauMap (tauMap (a, b, c, d)) ≠ (a, b, c, d) := by
  rw [tauMap_tauMap a b c d hD]
  intro h
  have ha : -a = a := congrArg Prod.fst h
  have hb : -b = b := congrArg (fun p => p.2.1) h
  have hc : -c = c := congrArg (fun p => p.2.2.1) h
  have hd : -d = d := congrArg (fun p => p.2.2.2) h
  exact hD (by
    have : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [this, hb0])

end GppGrassmannian
