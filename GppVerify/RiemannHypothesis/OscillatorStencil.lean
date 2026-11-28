import Init

/-! # Rigidity of the dyadic oscillator stencil

Use five consecutive nodes on the log₂ scale. Clearing the common factor
and shifting the indices turns the reciprocal stencil into (2,-9,14,-9,2).
The Laurent modes of exponent ±1 become the integer vectors (1,2,4,8,16)
and its reversal. Multiplication by the node index is logarithmic tilting.
All results are finite identities about the dilation operator.
-/

namespace GppVerify.OscillatorStencil

/-- Four cancellations on the constant, log, growing and decaying modes. -/
structure CuspCancellation (a b c d e : Int) : Prop where
  constant : a + b + c + d + e = 0
  linear : b + 2*c + 3*d + 4*e = 0
  growing : a + 2*b + 4*c + 8*d + 16*e = 0
  decaying : 16*a + 8*b + 4*c + 2*d + e = 0

theorem oscillator_cancels : CuspCancellation 2 (-9) 14 (-9) 2 := by
  constructor <;> decide

/-- No symmetry assumption is needed. The four cancellations force symmetry
and determine all five weights up to an integer factor. -/
theorem rigid {a b c d e : Int} (h : CuspCancellation a b c d e) :
    ∃ k : Int, a = 2*k ∧ b = -9*k ∧ c = 14*k ∧ d = -9*k ∧ e = 2*k := by
  obtain ⟨_, _, _, _⟩ := h
  exact ⟨-(b + 4*a), by omega⟩

/-- The forward growing mode, its reciprocal (scaled by 16), and the
constant mode's second tilt produce linked responses. -/
theorem tilt_responses {a b c d e : Int} (h : CuspCancellation a b c d e) :
    2*b + 8*c + 24*d + 64*e = 3*a ∧
    8*b + 8*c + 6*d + 4*e = -3*a ∧
    b + 4*c + 9*d + 16*e = -a := by
  obtain ⟨_, _, _, _⟩ := h
  omega

theorem no_extra_growing_cancellation {a b c d e : Int}
    (h : CuspCancellation a b c d e) (ht : 2*b + 8*c + 24*d + 64*e = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  obtain ⟨_, _, _, _⟩ := h
  omega


/-- Pair weights with integer samples on consecutive log-scale nodes. -/
def pair : List Int → List Int → Int
  | x :: xs, y :: ys => x*y + pair xs ys
  | _, _ => 0

/-- Cancel the constant and its first tilt, and both geometric modes and
their first tilts. The two reciprocal vectors have been scaled by 2^6. -/
def cancelsSixModes (w : List Int) : Prop :=
  pair w [1,1,1,1,1,1,1] = 0 ∧
  pair w [0,1,2,3,4,5,6] = 0 ∧
  pair w [1,2,4,8,16,32,64] = 0 ∧
  pair w [0,2,8,24,64,160,384] = 0 ∧
  pair w [64,32,16,8,4,2,1] = 0 ∧
  pair w [0,32,32,24,16,10,6] = 0

/-- Six consecutive weights cannot achieve all six cancellations. A shorter
stencil is included by padding its unused weights with zeros. -/
theorem six_nodes_trivial {a b c d e f : Int}
    (h : cancelsSixModes [a,b,c,d,e,f]) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  simp [cancelsSixModes, pair] at h
  omega

/-- Coefficients of (x-1)^2 (x-2)^2 (2x-1)^2 in increasing order. -/
def doubledRoots : List Int := [4,-28,77,-106,77,-28,4]

theorem seven_nodes_work : cancelsSixModes doubledRoots := by
  unfold cancelsSixModes doubledRoots
  decide

/-- The new window still detects second logarithmic tilts at all three
modes. The reciprocal mode uses the same factor of 64 as above. -/
theorem surviving_second_tilts :
    pair doubledRoots [0,1,4,9,16,25,36] = 2 ∧
    pair doubledRoots [0,2,16,72,256,800,2304] = 72 ∧
    pair doubledRoots [0,32,64,72,64,50,36] = 72 := by
  decide


/-- One step X ↦ 4X doubles a square-root term. This difference therefore
removes any constant multiple of that mode on each dilation orbit. -/
def squareDifference {R : Type} [Lean.Grind.CommRing R] (v : Nat → R) (j : Nat) : R :=
  v (j+1) - 2*v j

theorem square_mode_killed {R : Type} [Lean.Grind.CommRing R] (v : Nat → R)
    (hv : ∀ j, v (j+1) = 2*v j) (j : Nat) : squareDifference v j = 0 := by
  unfold squareDifference
  rw [hv]
  grind

/-- Exact reconstruction of a scale sequence from its initial value and
successive differences, over any commutative ring. -/
def accumulate {R : Type} [Lean.Grind.CommRing R] (d : Nat → R) : Nat → R
  | 0 => 0
  | j+1 => 2*accumulate d j + d j

theorem reconstruct {R : Type} [Lean.Grind.CommRing R] (v : Nat → R) (j : Nat) :
    v j = 2^j * v 0 + accumulate (squareDifference v) j := by
  induction j with
  | zero => simp [accumulate] <;> grind
  | succ j ih =>
    simp only [accumulate, squareDifference]
    grind [Lean.Grind.Semiring.pow_succ]


/-- A bound on the residual recovers the target envelope on the full orbit.
For a power envelope A(j)=C q^j the residual budget is C(q-2)q^j,
positive at every exponent strictly above the square-root scale. -/
theorem orbit_bound {R : Type} [Lean.Grind.CommRing R] [LE R] [LT R]
    [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R]
    (v A : Nat → R) (h0 : -A 0 ≤ v 0 ∧ v 0 ≤ A 0)
    (hd : ∀ j, -(A (j+1) - 2*A j) ≤ squareDifference v j ∧
      squareDifference v j ≤ A (j+1) - 2*A j) (j : Nat) :
    -A j ≤ v j ∧ v j ≤ A j := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    have step := hd j
    unfold squareDifference at step
    grind

end GppVerify.OscillatorStencil
