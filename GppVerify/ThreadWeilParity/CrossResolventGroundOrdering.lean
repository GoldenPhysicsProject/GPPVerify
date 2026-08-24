import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cross-resolvent positivity below the even ground forces the odd ground above it

`formalization_queue` item `5e10a4f0` ("Cross-resolvent positivity below even ground implies
parity ground ordering"), Weil-Parity thread. The item's own framing:

  "Assume Hermitian parity blocks A (even, size n+1) and B (odd, size n) satisfy
  det(B-zI)/det(A-zI)=f(z) for real z below spec(A). If f(z)>0 for every real z<lambda_min(A),
  then B has no eigenvalue below lambda_min(A); hence lambda_min(A)<lambda_min(B) provided
  ... no common eigenvalue occurs at lambda_min(A). ... This is pure linear algebra and
  should be sorry-free."

## What this file proves, and what it deliberately does NOT

The genuinely substantive mathematical content, once "`z` is an eigenvalue of `B`" is
unfolded to "`det(B - zI) = 0`" (the standard, purely definitional characterization), is a
one-line algebraic fact: `B_det z = f z * A_det z` with both factors positive forces
`B_det z` positive, hence nonzero. This file formalizes exactly that core, abstractly in
terms of real-valued functions `A_det`, `B_det`, `f` tied together by the ratio identity —
plus the boundary/limiting refinement that turns "no eigenvalue strictly below
`lambda_min(A)`" into the item's stronger "`lambda_min(A) < lambda_min(B)`" claim, given
continuity of `B_det` and a no-common-eigenvalue hypothesis at `lambda_min(A)` itself.

It does **not** define Hermitian matrices `A`, `B`, their characteristic polynomials, or
their eigenvalues, and does not connect `A_det`/`B_det` to actual `Matrix.det (A - z•1)` /
`Matrix.det (B - z•1)` — that identification (`z` an eigenvalue of a Hermitian matrix `M`
iff `Matrix.det (M - z • 1) = 0`) is standard linear algebra, not itself formalized in this
file. No axiom, no sorry.
-/

namespace GppWeilParity

open Filter Topology

/-- **Core algebraic content.** If `B_det z = f z * A_det z` for every `z < lamMinA`
(the determinant-ratio identity), with `f z > 0` and `A_det z > 0` there, then
`B_det z > 0` for every `z < lamMinA` — in particular `B_det` has no zero below `lamMinA`,
i.e. (once `B_det` is identified with `z ↦ det(B - zI)`) `B` has no eigenvalue there. -/
theorem Bdet_pos_of_ratio_pos {lamMinA : ℝ} {A_det B_det f : ℝ → ℝ}
    (hratio : ∀ z < lamMinA, B_det z = f z * A_det z) (hfpos : ∀ z < lamMinA, 0 < f z)
    (hApos : ∀ z < lamMinA, 0 < A_det z) : ∀ z < lamMinA, 0 < B_det z := by
  intro z hz
  rw [hratio z hz]
  exact mul_pos (hfpos z hz) (hApos z hz)

/-- Immediate corollary in the "no eigenvalue" phrasing the queue item leads with. -/
theorem Bdet_ne_zero_of_ratio_pos {lamMinA : ℝ} {A_det B_det f : ℝ → ℝ}
    (hratio : ∀ z < lamMinA, B_det z = f z * A_det z) (hfpos : ∀ z < lamMinA, 0 < f z)
    (hApos : ∀ z < lamMinA, 0 < A_det z) : ∀ z < lamMinA, B_det z ≠ 0 :=
  fun z hz => (Bdet_pos_of_ratio_pos hratio hfpos hApos z hz).ne'

/-- **Boundary refinement.** If in addition `B_det` is continuous at `lamMinA` and does not
vanish there (the "no common eigenvalue at `lambda_min(A)`" hypothesis), positivity on the
open ray `z < lamMinA` propagates to `lamMinA` itself: `B_det lamMinA > 0` too. This is
exactly the queue item's strengthening from "no eigenvalue strictly below `lambda_min(A)`"
to "`lambda_min(A) < lambda_min(B)`" (once eigenvalues are the zero set of `B_det`, a value
of `B_det` that is everywhere positive on `(-∞, lambda_min(A)]` certifies no eigenvalue of
`B` lies at or below `lambda_min(A)`). -/
theorem Bdet_pos_at_lamMinA_of_continuousAt {lamMinA : ℝ} {B_det : ℝ → ℝ}
    (hcont : ContinuousAt B_det lamMinA) (hpos : ∀ z < lamMinA, 0 < B_det z)
    (hne : B_det lamMinA ≠ 0) : 0 < B_det lamMinA := by
  have htendsto : Tendsto B_det (𝓝[<] lamMinA) (𝓝 (B_det lamMinA)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hge : 0 ≤ B_det lamMinA :=
    ge_of_tendsto htendsto (eventually_nhdsWithin_of_forall (fun z hz => (hpos z hz).le))
  exact hge.lt_of_ne (Ne.symm hne)

end GppWeilParity
