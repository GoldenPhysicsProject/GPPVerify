import Mathlib.Tactic

/-!
# Record-oriented entropy with two microscopic time arrows

Finite sign algebra accompanying Daniel Toupin,
"Which Way Is Forward?", October 2026 correction.

This module records the convention used by the current orientation picture.

There is one coarse-grained record direction in the shared history.  Let
`r = dS/dlambda` be the entropy rate in that record coordinate, with `r >= 0`.
The microscopic time arrow `t in {+1,-1}` does **not** flip that shared
coarse-grained history.  Instead it says whether a constituent's intrinsic
clock is aligned or anti-aligned with the record coordinate.

Thus

  dS/dtau_t = t * r.

For `t=+1`, entropy rises toward the constituent's microscopic future.
For `t=-1`, entropy falls when followed toward that constituent's microscopic
future, equivalently entropy rises toward its microscopic past.  Both lifts
occupy the same record history and therefore have the same coordinate entropy
rate `r`.

The signed/oriented entropy variable `t*S` cancels between an equally weighted
pair.  This is the precise finite statement behind the notation
`S_oriented,total = 0`; it does not say that ordinary thermodynamic or
von Neumann entropy is negative.

This file formalizes only this sign algebra.  It does not derive the second law,
the low-entropy boundary condition, decoherence, record formation, or an equal
population law.
-/

namespace GppOrientationCovariantSecondLaw

/-- Relational particle/antiparticle grading. -/
def relationalChi (q t : ℝ) : ℝ := q * t

/-- Coarse-grained entropy rate in the observer's shared record coordinate. -/
def recordEntropyRate (r : ℝ) : ℝ := r

/-- Entropy derivative with respect to a constituent clock whose microscopic
orientation relative to the record coordinate is `t`. -/
def intrinsicEntropyRate (t r : ℝ) : ℝ := t * r

/-- Signed/oriented entropy used only to compare the two microscopic lifts. -/
def orientedEntropy (t S : ℝ) : ℝ := t * S

/-- Complete q,t reversal preserves the relational grading. -/
theorem diagonal_reversal_preserves_chi (q t : ℝ) :
    relationalChi (-q) (-t) = relationalChi q t := by
  simp [relationalChi]

/-- A single q or t half flip reverses the relational grading. -/
theorem either_half_flip_reverses_chi (q t : ℝ) :
    relationalChi (-q) t = - relationalChi q t ∧
    relationalChi q (-t) = - relationalChi q t := by
  constructor <;> simp [relationalChi]

/-- The shared record-coordinate entropy rate is independent of microscopic
orientation.  Both lifts inhabit the same coarse-grained history. -/
theorem shared_record_rate (r : ℝ) :
    recordEntropyRate r = r := rfl

/-- The backward microscopic lift has the opposite entropy derivative with
respect to its own intrinsic clock. -/
theorem backward_intrinsic_rate_is_negative_of_forward (r : ℝ) :
    intrinsicEntropyRate (-1 : ℝ) r = - intrinsicEntropyRate (1 : ℝ) r := by
  simp [intrinsicEntropyRate]

/-- The two intrinsic-clock entropy derivatives cancel as an oriented pair. -/
theorem paired_intrinsic_rates_cancel (r : ℝ) :
    intrinsicEntropyRate (1 : ℝ) r +
      intrinsicEntropyRate (-1 : ℝ) r = 0 := by
  simp [intrinsicEntropyRate]

/-- Equal-magnitude opposite microscopic orientations give zero total signed
entropy, while leaving the ordinary entropy magnitude `S` untouched. -/
theorem paired_oriented_entropy_cancel (S : ℝ) :
    orientedEntropy (1 : ℝ) S + orientedEntropy (-1 : ℝ) S = 0 := by
  simp [orientedEntropy]

/-- If entropy increases in the shared record direction, the forward microscopic
lift sees nonnegative entropy change toward its own future. -/
theorem forward_entropy_increases_toward_intrinsic_future {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ intrinsicEntropyRate (1 : ℝ) r := by
  simpa [intrinsicEntropyRate] using hr

/-- If entropy increases in the shared record direction, the backward microscopic
lift sees nonpositive entropy change toward its own future.  Equivalently, its
entropy increases toward its microscopic past. -/
theorem backward_entropy_increases_toward_intrinsic_past {r : ℝ} (hr : 0 ≤ r) :
    intrinsicEntropyRate (-1 : ℝ) r ≤ 0 := by
  simp [intrinsicEntropyRate]
  exact hr

/-- Both microscopic lifts share the same nonnegative record-coordinate entropy
rate even though their intrinsic-clock derivatives have opposite signs. -/
theorem shared_record_arrow_capstone {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ recordEntropyRate r ∧
    0 ≤ recordEntropyRate r ∧
    intrinsicEntropyRate (1 : ℝ) r =
      - intrinsicEntropyRate (-1 : ℝ) r := by
  constructor
  · simpa [recordEntropyRate] using hr
  constructor
  · simpa [recordEntropyRate] using hr
  · simp [intrinsicEntropyRate]

/-- Package the corrected finite sign content: common record arrow, opposite
microscopic clock derivatives, and cancellation only of the signed entropy. -/
theorem record_oriented_entropy_capstone {r S : ℝ} (hr : 0 ≤ r) :
    0 ≤ recordEntropyRate r ∧
    0 ≤ intrinsicEntropyRate (1 : ℝ) r ∧
    intrinsicEntropyRate (-1 : ℝ) r ≤ 0 ∧
    orientedEntropy (1 : ℝ) S + orientedEntropy (-1 : ℝ) S = 0 := by
  constructor
  · simpa [recordEntropyRate] using hr
  constructor
  · exact forward_entropy_increases_toward_intrinsic_future hr
  constructor
  · exact backward_entropy_increases_toward_intrinsic_past hr
  · exact paired_oriented_entropy_cancel S

end GppOrientationCovariantSecondLaw
