import GppVerify.RiemannHypothesis.CayleyDickson

/-!
# Rung 8 of the Cayley-Dickson ladder: the octonions

`O8 := CD Q8 (-1)` with `Q8 := CD (CD ℝ (-1)) (-1)` the quaternion rung of `GppVerify.RiemannHypothesis.CayleyDickson`.
Coordinates `x₀, …, x₇` of `x : O8` are, in this order, `x.fst.fst.fst`, `x.fst.fst.snd`, `x.fst.snd.fst`,
`x.fst.snd.snd`, `x.snd.fst.fst`, `x.snd.fst.snd`, `x.snd.snd.fst`, `x.snd.snd.snd`, and `eᵢ` is the element with
coordinate `i` equal to `1` and the others `0` (index bits: low bit is the innermost doubling, high bit the
outermost).

* `n8_mul`: the norm `n8 x = Σ xᵢ²` is multiplicative, `n8 (x * y) = n8 x * n8 y` (Degen's eight-squares
  identity in coordinates, `sum_eight_sq_mul_sum_eight_sq` in Mathlib).
* `mul_star_self`: `x * star x = ofReal8 (n8 x)`.
* `alt_left`, `alt_right`: the alternative laws `x * (x * y) = (x * x) * y` and `(y * x) * x = y * (x * x)`.
* `assoc_e1_e2_e4`, `assoc_e1_e2_e4'`, `not_assoc`: `(e₁ e₂) e₄ = e₇` while `e₁ (e₂ e₄) = - e₇`, so the
  product is not associative.
-/

namespace GppOctonion

/-- The quaternion rung. -/
abbrev Q8 : Type := CD (CD ℝ (-1)) (-1)

/-- The octonion rung. -/
abbrev O8 : Type := CD Q8 (-1)

/-- The element with coordinates `a, …, h`. -/
def mk8 (a b c d e f g h : ℝ) : O8 := ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨⟨e, f⟩, ⟨g, h⟩⟩⟩

/-- The real element `r`. -/
def ofReal8 (r : ℝ) : O8 := mk8 r 0 0 0 0 0 0 0

/-- The norm: the sum of the eight squared coordinates. -/
def n8 (x : O8) : ℝ :=
  x.fst.fst.fst ^ 2 + x.fst.fst.snd ^ 2 + x.fst.snd.fst ^ 2 + x.fst.snd.snd ^ 2 +
    x.snd.fst.fst ^ 2 + x.snd.fst.snd ^ 2 + x.snd.snd.fst ^ 2 + x.snd.snd.snd ^ 2

/-- The norm is multiplicative. -/
theorem n8_mul (x y : O8) : n8 (x * y) = n8 x * n8 y := by
  simp [n8, star_trivial]
  ring

/-- `x * star x` is the real number `n8 x`. -/
theorem mul_star_self (x : O8) : x * star x = ofReal8 (n8 x) := by
  ext <;> simp [n8, ofReal8, mk8, star_trivial]
  all_goals ring

set_option maxHeartbeats 4000000 in
/-- Left alternative law. -/
theorem alt_left (x y : O8) : x * (x * y) = (x * x) * y := by
  ext <;> simp [star_trivial] <;> ring

set_option maxHeartbeats 4000000 in
/-- Right alternative law. -/
theorem alt_right (x y : O8) : (y * x) * x = y * (x * x) := by
  ext <;> simp [star_trivial] <;> ring

/-- The basis elements used in the non-associativity witness. -/
def e1 : O8 := mk8 0 1 0 0 0 0 0 0
def e2 : O8 := mk8 0 0 1 0 0 0 0 0
def e4 : O8 := mk8 0 0 0 0 1 0 0 0
def e7 : O8 := mk8 0 0 0 0 0 0 0 1

set_option maxHeartbeats 4000000 in
theorem assoc_e1_e2_e4 : (e1 * e2) * e4 = e7 := by
  ext <;> simp [e1, e2, e4, e7, mk8, star_trivial]

set_option maxHeartbeats 4000000 in
theorem assoc_e1_e2_e4' : e1 * (e2 * e4) = -e7 := by
  ext <;> simp [e1, e2, e4, e7, mk8, star_trivial]

/-- The octonion product is not associative. -/
theorem not_assoc : ¬ ∀ x y z : O8, (x * y) * z = x * (y * z) := by
  intro h
  have h1 := h e1 e2 e4
  rw [assoc_e1_e2_e4, assoc_e1_e2_e4'] at h1
  have h2 := congrArg (fun x : O8 => x.snd.snd.snd) h1
  simp [e7, mk8] at h2
  norm_num at h2

#print axioms n8_mul
#print axioms mul_star_self
#print axioms alt_left
#print axioms alt_right
#print axioms assoc_e1_e2_e4
#print axioms assoc_e1_e2_e4'
#print axioms not_assoc

end GppOctonion
