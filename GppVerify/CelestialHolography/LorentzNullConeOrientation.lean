import Mathlib.Tactic
import GppVerify.CelestialHolography.LorentzHermitianDiscreteGeometry

/-!
# Lorentzian reality and the missing future/past sign

The complexified/split null factorization uses two independent spinors

  p_{AA'} = lambda_A lambdatilde_{A'}.

On a real Lorentzian null ray, however, the primed spinor is the complex conjugate of the
unprimed one.  A real null vector therefore has the form, up to normalization,

  p = lambda lambda^dagger

for the future cone, or

  p = - lambda lambda^dagger

for the past cone.

This matters for the project's proposed time-orientation sign.  Once Lorentzian reality is
imposed, one cannot flip the left spinor sign independently of the right/conjugate sign:
`lambda -> -lambda` also sends `bar lambda -> -bar lambda`, and the vector is unchanged.
The connected spin group therefore does NOT contain the future/past sign.

The sign distinguishing the two components of the real null cone is an extra discrete
orientation label

  t in {+1,-1},    p = t lambda lambda^dagger.

This is exactly the kind of hidden `t` needed by the charge-orientation quotient: it is
forgotten by projectivizing a null LINE, but is required to distinguish the two oriented
cones.  The earlier independent `Z2_L x Z2_R` center algebra should therefore be read as a
complexified/split precursor; on the Lorentzian real slice its one-sided center is not an
allowed reality-preserving transformation.

The module proves this with an explicit real-coordinate spinor square.
-/

namespace GppLorentzNullConeOrientation

open GppLorentzHermitianDiscreteGeometry

/-- One complex two-spinor written as four real coordinates
`lambda=(a+i b, c+i d)`. -/
abbrev RealSpinor4 := ℝ × ℝ × ℝ × ℝ

/-- Future-directed null vector associated with `lambda lambda^dagger`, with an irrelevant
factor-of-two normalization chosen to avoid fractions. -/
def spinorNullVector (s : RealSpinor4) : R4 :=
  let a := s.1
  let b := s.2.1
  let c := s.2.2.1
  let d := s.2.2.2
  (a^2+b^2+c^2+d^2,
   2*(a*c+b*d),
   2*(a*d-b*c),
   a^2+b^2-c^2-d^2)

/-- The spinor square is exactly null. -/
theorem spinorNullVector_is_null (s : RealSpinor4) :
    minkowskiQ (spinorNullVector s) = 0 := by
  rcases s with ⟨a,b,c,d⟩
  simp [spinorNullVector, minkowskiQ]
  ring

/-- Its time component is a sum of squares and therefore nonnegative. -/
theorem spinorNullVector_time_nonneg (s : RealSpinor4) :
    0 ≤ (spinorNullVector s).1 := by
  rcases s with ⟨a,b,c,d⟩
  simp [spinorNullVector]
  positivity

/-- The central spinor deck sign `lambda -> -lambda` is invisible on the Lorentz vector. -/
def negRealSpinor (s : RealSpinor4) : RealSpinor4 :=
  (-s.1,-s.2.1,-s.2.2.1,-s.2.2.2)

theorem spinor_deck_sign_invisible (s : RealSpinor4) :
    spinorNullVector (negRealSpinor s) = spinorNullVector s := by
  rcases s with ⟨a,b,c,d⟩
  simp [spinorNullVector, negRealSpinor]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- Add the genuinely independent orientation sign of the real null cone. -/
def orientedNullVector (t : ℝ) (s : RealSpinor4) : R4 :=
  let p := spinorNullVector s
  (t*p.1,t*p.2.1,t*p.2.2.1,t*p.2.2.2)

/-- Reversing the cone-orientation sign reverses the whole null vector. -/
theorem orientedNullVector_flip (t : ℝ) (s : RealSpinor4) :
    orientedNullVector (-t) s =
      let p := orientedNullVector t s
      (-p.1,-p.2.1,-p.2.2.1,-p.2.2.2) := by
  rcases s with ⟨a,b,c,d⟩
  simp [orientedNullVector, spinorNullVector]
  constructor
  · ring
  · constructor
    · ring
    · constructor <;> ring

/-- The signed lift remains null for every orientation scalar. -/
theorem orientedNullVector_is_null (t : ℝ) (s : RealSpinor4) :
    minkowskiQ (orientedNullVector t s) = 0 := by
  rcases s with ⟨a,b,c,d⟩
  simp [orientedNullVector, spinorNullVector, minkowskiQ]
  ring

/-- For the canonical signs +/-1, the time component has the corresponding sign. -/
theorem future_past_time_components (s : RealSpinor4) :
    (orientedNullVector 1 s).1 = (spinorNullVector s).1 ∧
    (orientedNullVector (-1) s).1 = -(spinorNullVector s).1 := by
  simp [orientedNullVector]

/-- Spin deck sign and cone orientation are sharply different: the former is invisible,
whereas the latter negates the vector. -/
theorem deck_vs_cone_orientation (s : RealSpinor4) :
    spinorNullVector (negRealSpinor s) = spinorNullVector s ∧
    orientedNullVector (-1) s =
      let p := orientedNullVector 1 s
      (-p.1,-p.2.1,-p.2.2.1,-p.2.2.2) := by
  exact ⟨spinor_deck_sign_invisible s, orientedNullVector_flip 1 s⟩

end GppLorentzNullConeOrientation
