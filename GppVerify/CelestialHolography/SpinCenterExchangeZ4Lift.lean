import Mathlib.Tactic
import GppVerify.CelestialHolography.SpinProductCenterTimeOrientation

/-!
# Factor exchange plus relative-center reversal has an order-four spin lift

On the doubled spinor carrier `(lambda,lambdatilde)` there are two elementary involutions:

* `E(lambda,lambdatilde) = (lambdatilde,lambda)` exchanges the two chiral factors;
* `L(lambda,lambdatilde) = (-lambda,lambdatilde)` flips one spin-product center and hence
  reverses the oriented vector sign `t`.

They do not commute: exchange conjugates the left flip into the right flip.  Their product

  Q = E L,

acts by

  Q(lambda,lambdatilde) = (lambdatilde,-lambda).

Applying it twice gives the diagonal center

  Q^2(lambda,lambdatilde) = (-lambda,-lambdatilde),

which is invisible on the vector representation.  Four applications return the spinor
pair exactly.  Thus `Q` has vector/projective order two but spinor-level order four.

This is a clean finite Pin/Spin-type lifting pattern generated entirely by the two pieces
already present in the geometry: chiral-factor exchange and the relative center that carries
oriented-vector/worldline sign.  No identification with a particular physical P, T, or CPT
operator is made here.
-/

namespace GppSpinCenterExchangeZ4Lift

open GppFlatInfinityCelestialFactorization
open GppSpinProductCenterTimeOrientation

abbrev SpinPair := Spinor2 × Spinor2

/-- Exchange the two chiral spinor factors. -/
def exchangeSpinFactors (u : SpinPair) : SpinPair := (u.2,u.1)

/-- Flip only the left central sign. -/
def flipLeftCenter (u : SpinPair) : SpinPair := (centerScale (-1) u.1,u.2)

/-- Flip only the right central sign. -/
def flipRightCenter (u : SpinPair) : SpinPair := (u.1,centerScale (-1) u.2)

/-- Primitive quarter-lift: factor exchange after one relative-center reversal. -/
def quarterLift (u : SpinPair) : SpinPair := exchangeSpinFactors (flipLeftCenter u)

/-- Factor exchange is involutive. -/
theorem exchangeSpinFactors_sq (u : SpinPair) :
    exchangeSpinFactors (exchangeSpinFactors u) = u := by
  rcases u with ⟨l,r⟩
  rfl

/-- Each one-sided center flip is involutive. -/
theorem flipLeftCenter_sq (u : SpinPair) : flipLeftCenter (flipLeftCenter u) = u := by
  rcases u with ⟨⟨a,b⟩,r⟩
  simp [flipLeftCenter, centerScale, scale2]

theorem flipRightCenter_sq (u : SpinPair) : flipRightCenter (flipRightCenter u) = u := by
  rcases u with ⟨l,⟨a,b⟩⟩
  simp [flipRightCenter, centerScale, scale2]

/-- Exchange conjugates left-center reversal into right-center reversal. -/
theorem exchange_conjugates_left_to_right (u : SpinPair) :
    exchangeSpinFactors (flipLeftCenter (exchangeSpinFactors u)) = flipRightCenter u := by
  rcases u with ⟨l,r⟩
  rfl

/-- Explicit quarter-lift action. -/
theorem quarterLift_apply (lambda lambdatilde : Spinor2) :
    quarterLift (lambda,lambdatilde) = (lambdatilde,centerScale (-1) lambda) := by
  rfl

/-- Two quarter-lifts give the diagonal central sign. -/
theorem quarterLift_sq_diagonal_center (u : SpinPair) :
    quarterLift (quarterLift u) =
      (centerScale (-1) u.1, centerScale (-1) u.2) := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [quarterLift, exchangeSpinFactors, flipLeftCenter, centerScale, scale2]

/-- Hence four applications close exactly upstairs. -/
theorem quarterLift_four (u : SpinPair) :
    quarterLift (quarterLift (quarterLift (quarterLift u))) = u := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [quarterLift, exchangeSpinFactors, flipLeftCenter, centerScale, scale2]

/-- Momentum represented by a spin pair. -/
def pairMomentum (u : SpinPair) : M2 := nullMomentum u.1 u.2

/-- Factor exchange transposes the rank-one momentum matrix. -/
def transposeM2 (P : M2) : M2 := (P.1,P.2.2.1,P.2.1,P.2.2.2)

theorem pairMomentum_exchange_is_transpose (u : SpinPair) :
    pairMomentum (exchangeSpinFactors u) = transposeM2 (pairMomentum u) := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

/-- The quarter lift acts downstairs as minus transpose: exchange plus vector-orientation
reversal. -/
theorem pairMomentum_quarterLift_is_neg_transpose (u : SpinPair) :
    pairMomentum (quarterLift u) = scaleM2 (-1) (transposeM2 (pairMomentum u)) := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  apply Prod.ext
  · simp [pairMomentum, quarterLift, exchangeSpinFactors, flipLeftCenter,
      centerScale, scale2, nullMomentum, transposeM2, scaleM2]; ring
  · apply Prod.ext
    · simp [pairMomentum, quarterLift, exchangeSpinFactors, flipLeftCenter,
        centerScale, scale2, nullMomentum, transposeM2, scaleM2]; ring
    · apply Prod.ext
      · simp [pairMomentum, quarterLift, exchangeSpinFactors, flipLeftCenter,
          centerScale, scale2, nullMomentum, transposeM2, scaleM2]; ring
      · simp [pairMomentum, quarterLift, exchangeSpinFactors, flipLeftCenter,
          centerScale, scale2, nullMomentum, transposeM2, scaleM2]; ring

/-- Although the spin lift has order four, its action on the vector momentum has order two. -/
theorem pairMomentum_quarterLift_sq_invisible (u : SpinPair) :
    pairMomentum (quarterLift (quarterLift u)) = pairMomentum u := by
  rw [quarterLift_sq_diagonal_center]
  exact diagonal_center_is_vector_invisible u.1 u.2

end GppSpinCenterExchangeZ4Lift
