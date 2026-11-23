import GppVerify.RiemannHypothesis.CayleyDicksonOctonion

/-!
# Rung 16 of the Cayley-Dickson ladder: the sedenions

`S16 := CD O8 (-1)` over the octonion rung of `GppVerify.RiemannHypothesis.CayleyDicksonOctonion`
(possible because `CD` is defined over any `NonAssocRing`). The norm is `n16 x = n8 x.fst + n8 x.snd`.

* `zero_divisor`: `(e₁ + e₁₀) * (e₄ - e₁₅) = 0`, with both factors nonzero (`a16_ne_zero`,
  `b16_ne_zero`); here `e_i` for `i < 8` is `⟨eᵢ, 0⟩` and `e_{8+i}` is `⟨0, eᵢ⟩`.
* `n16_a16`, `n16_b16`, `n16_mul_a16_b16`: the norms are `2`, `2` and `0`, so
  `n16_not_mul : ¬ ∀ x y, n16 (x * y) = n16 x * n16 y`: the norm is not multiplicative at rung 16.
-/

namespace GppSedenion

open GppOctonion

/-- The sedenion rung. -/
abbrev S16 : Type := CD O8 (-1)

/-- The norm: the sum of the sixteen squared coordinates. -/
def n16 (x : S16) : ℝ := n8 x.fst + n8 x.snd

/-- `e_i` for `i < 8`. -/
def lo (x : O8) : S16 := ⟨x, 0⟩

/-- `e_{8+i}` for `e_i : O8`. -/
def hi (x : O8) : S16 := ⟨0, x⟩

/-- `e₁ + e₁₀`. -/
def a16 : S16 := lo e1 + hi e2

/-- `e₄ - e₁₅`. -/
def b16 : S16 := lo e4 - hi e7

set_option maxHeartbeats 8000000 in
/-- The product of the two nonzero sedenions `e₁ + e₁₀` and `e₄ - e₁₅` is zero. -/
theorem zero_divisor : a16 * b16 = 0 := by
  ext <;> simp [a16, b16, lo, hi, e1, e2, e4, e7, mk8, star_trivial]

theorem a16_ne_zero : a16 ≠ 0 := by
  intro h
  have := congrArg (fun x : S16 => x.fst.fst.fst.snd) h
  simp [a16, lo, hi, e1, mk8] at this

theorem b16_ne_zero : b16 ≠ 0 := by
  intro h
  have := congrArg (fun x : S16 => x.fst.snd.fst.fst) h
  simp [b16, lo, hi, e4, mk8] at this

theorem n16_a16 : n16 a16 = 2 := by
  simp [n16, n8, a16, lo, hi, e1, e2, mk8]
  norm_num

theorem n16_b16 : n16 b16 = 2 := by
  simp [n16, n8, b16, lo, hi, e4, e7, mk8]
  norm_num

theorem n16_mul_a16_b16 : n16 (a16 * b16) = 0 := by
  rw [zero_divisor]
  simp [n16, n8]

/-- The sedenion norm is not multiplicative. -/
theorem n16_not_mul : ¬ ∀ x y : S16, n16 (x * y) = n16 x * n16 y := by
  intro h
  have := h a16 b16
  rw [n16_mul_a16_b16, n16_a16, n16_b16] at this
  norm_num at this

#print axioms zero_divisor
#print axioms a16_ne_zero
#print axioms b16_ne_zero
#print axioms n16_a16
#print axioms n16_b16
#print axioms n16_not_mul

end GppSedenion
