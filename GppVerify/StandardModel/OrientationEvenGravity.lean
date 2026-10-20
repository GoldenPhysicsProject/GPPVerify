import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# Gravity reads the even part of the orientation grading

Source: Daniel Toupin, *Which Way Is Forward?* (v27, section "Gravity reads the even part"),
with AI assistance from Claude Code.

Reversing a worldline's orientation sends its tangent `u ↦ -u`.  Quantities are graded by how
many times that orientation enters:

* the oriented current `j = q • u` is **odd** in `u` alone (`current_odd`), so a single arrow
  flip changes the measured charge, while the simultaneous flip `(q, u) ↦ (-q, -u)` leaves it
  fixed (`current_diagonal`);
* the dust stress tensor `T i j = m * u i * u j` is **even** (`stress_even`): no arrow flip
  changes the gravitational source;
* acceleration is **even** under reversal of the curve parameter (`reversed_velocity`,
  `reversed_acceleration`): if `x' = v` and `v' = a`, the reversed path `s ↦ x (-s)` has
  velocity `-v (-s)` and acceleration `a (-s)`.

Consequently (`gravitational_source_sign`) the sign of the source is the sign of `m` for either
orientation: turning attraction into repulsion requires `m < 0`, never an arrow flip.

Scope: classical point-particle/dust kinematics.  The field-theory statements (the Dirac stress
tensor and its charge-conjugation evenness) and the experimental input (ALPHA-g) are cited in
the paper, not formalized here.  Nothing here concerns RH.
-/

namespace GppOrientationEvenGravity

/-- Oriented current of a point charge with charge arrow `q` and tangent `u`. -/
def current {n : ℕ} (q : ℝ) (u : Fin n → ℝ) : Fin n → ℝ := fun i => q * u i

/-- Dust stress tensor `m uᵢ uⱼ`. -/
def stress {n : ℕ} (m : ℝ) (u : Fin n → ℝ) : Fin n → Fin n → ℝ := fun i j => m * u i * u j

/-- A single arrow flip reverses the current. -/
theorem current_odd {n : ℕ} (q : ℝ) (u : Fin n → ℝ) :
    current q (-u) = -current q u := by
  funext i; simp [current]

/-- The simultaneous flip `(q, u) ↦ (-q, -u)` leaves the current unchanged. -/
theorem current_diagonal {n : ℕ} (q : ℝ) (u : Fin n → ℝ) :
    current (-q) (-u) = current q u := by
  funext i; simp [current]

/-- The gravitational source is even under the arrow flip. -/
theorem stress_even {n : ℕ} (m : ℝ) (u : Fin n → ℝ) : stress m (-u) = stress m u := by
  funext i j; simp [stress]

/-- The energy density `T₀₀ = m u₀²` has the sign of `m` for either orientation of `u`. -/
theorem gravitational_source_sign {n : ℕ} (m : ℝ) (u : Fin (n + 1) → ℝ) (hu : u 0 ≠ 0) :
    (0 < stress m u 0 0 ↔ 0 < m) ∧ (0 < stress m (-u) 0 0 ↔ 0 < m) := by
  have key : ∀ w : Fin (n + 1) → ℝ, w 0 ≠ 0 → (0 < stress m w 0 0 ↔ 0 < m) := by
    intro w hw
    have hw2 : 0 < w 0 * w 0 := mul_self_pos.mpr hw
    simp only [stress, mul_assoc]
    exact ⟨fun h => pos_of_mul_pos_left_iff_aux h hw2, fun h => mul_pos h hw2⟩
  exact ⟨key u hu, key (-u) (by simpa using hu)⟩
where
  pos_of_mul_pos_left_iff_aux {a b : ℝ} (h : 0 < a * b) (hb : 0 < b) : 0 < a :=
    (pos_iff_pos_of_mul_pos h).mpr hb

/-- Reversing the curve parameter reverses velocity. -/
theorem reversed_velocity {x v : ℝ → ℝ} (hx : ∀ s, HasDerivAt x (v s) s) (s : ℝ) :
    HasDerivAt (fun r => x (-r)) (-v (-s)) s := by
  have h := (hx (-s)).comp s (hasDerivAt_neg s)
  rw [mul_neg_one] at h
  exact h

/-- Reversing the curve parameter leaves acceleration unchanged: the double flip. -/
theorem reversed_acceleration {v a : ℝ → ℝ} (hv : ∀ s, HasDerivAt v (a s) s) (s : ℝ) :
    HasDerivAt (fun r => -v (-r)) (a (-s)) s := by
  have h := ((hv (-s)).comp s (hasDerivAt_neg s)).neg
  rw [mul_neg_one, neg_neg] at h
  exact h

end GppOrientationEvenGravity
