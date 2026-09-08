import Mathlib.Tactic
import GppVerify.CelestialHolography.SpinCenterExchangeZ4Lift
import GppVerify.CelestialHolography.WeylQuarticNullReconstruction
import GppVerify.StandardModel.GaugeCurrentSpinOrientation

/-!
# Discrete Pin-style geometry: factor exchange, central inversion, and googly chirality

The doubled spinor algebra now distinguishes three spacetime operations at the finite level.
For a rank-one mixed spinor/vector `P=lambda*lambdatilde^T`:

  E : (lambda,lambdatilde) -> (lambdatilde,lambda)
      gives P -> P^T;

  O : (lambda,lambdatilde) -> (-lambda,lambdatilde)
      gives P -> -P;

  Q = E O
      gives P -> -P^T and has Q^2 equal to the diagonal spin center upstairs.

On a Lorentzian Hermitian real slice these are the algebraic patterns expected, up to
basis conventions, for a parity-like reflection, central spacetime inversion `PT`, and a
time-reflection-like Pin lift respectively:

  P-like :  X ->  adjugate/transpose-type X,
  PT-like:  X -> -X,
  T-like :  X -> minus transpose/adjugate-type X.

The naming remains a DICTIONARY CANDIDATE until the Lorentzian soldering/Pin map is built.
The important invariant distinction is already exact:

* factor exchange swaps left/right spin representations and hence W+ <-> W-;
* central vector inversion does NOT swap the rank-four Weyl chiralities (center-even);
* their product swaps W+ <-> W- and reverses vector/worldline orientation;
* its spin lift has order four although its vector action has order two.

This prevents a major conflation: googly exchange is associated with an orientation-reversing
factor swap (P-like or T-like), whereas the pure `X->-X` worldline orientation reversal is
PT-like and is invisible to the Weyl chirality labels.
-/

namespace GppDiscretePinGooglyDictionary

open GppSpinCenterExchangeZ4Lift
open GppWeylQuarticNullReconstruction
open GppFlatInfinityCelestialFactorization
open GppGaugeCurrentSpinOrientation

/-- P-like factor exchange. -/
def Pspin (u : SpinPair) : SpinPair := exchangeSpinFactors u

/-- PT-like central vector/worldline inversion, using the left lift. -/
def PTspin (u : SpinPair) : SpinPair := flipLeftCenter u

/-- T-like composition: factor exchange after central vector inversion. -/
def Tspin (u : SpinPair) : SpinPair := quarterLift u

/-- P-like action on momentum is transpose. -/
theorem Pspin_momentum (u : SpinPair) :
    pairMomentum (Pspin u) = transposeM2 (pairMomentum u) := by
  exact pairMomentum_exchange_is_transpose u

/-- PT-like action is pure vector sign reversal. -/
theorem PTspin_momentum (u : SpinPair) :
    pairMomentum (PTspin u) = scaleM2 (-1) (pairMomentum u) := by
  rcases u with ⟨lambda,lambdatilde⟩
  exact GppSpinProductCenterTimeOrientation.left_center_flip_reverses_vector lambda lambdatilde

/-- T-like composition is minus transpose. -/
theorem Tspin_momentum (u : SpinPair) :
    pairMomentum (Tspin u) = scaleM2 (-1) (transposeM2 (pairMomentum u)) := by
  exact pairMomentum_quarterLift_is_neg_transpose u

/-- P-like and PT-like are involutions upstairs. -/
theorem Pspin_sq (u : SpinPair) : Pspin (Pspin u) = u := exchangeSpinFactors_sq u

theorem PTspin_sq (u : SpinPair) : PTspin (PTspin u) = u := flipLeftCenter_sq u

/-- The T-like lift squares to the diagonal spin center and closes only after four turns. -/
theorem Tspin_sq_diagonal_center (u : SpinPair) :
    Tspin (Tspin u) =
      (GppSpinProductCenterTimeOrientation.centerScale (-1) u.1,
       GppSpinProductCenterTimeOrientation.centerScale (-1) u.2) :=
  quarterLift_sq_diagonal_center u

theorem Tspin_four (u : SpinPair) :
    Tspin (Tspin (Tspin (Tspin u))) = u := quarterLift_four u

/-- Gravitational chirality action: factor exchange is the googly swap. -/
def Pweyl (W : WeylPair) : WeylPair := exchangeWeyl W

/-- Pure central vector inversion is center-even on rank-four Weyl spinors, so its induced
finite chiral-label action is the identity. -/
def PTweyl (W : WeylPair) : WeylPair := W

/-- The T-like composition therefore has the same chiral exchange as the P-like factor swap. -/
def Tweyl (W : WeylPair) : WeylPair := exchangeWeyl W

/-- P-like and T-like operations exchange the two Weyl quartics; PT-like does not. -/
theorem discrete_weyl_action_package (W : WeylPair) :
    (Pweyl W).left = W.right ∧ (Pweyl W).right = W.left ∧
    (PTweyl W).left = W.left ∧ (PTweyl W).right = W.right ∧
    (Tweyl W).left = W.right ∧ (Tweyl W).right = W.left := by
  rfl

/-- Adding gauge conjugation to pure vector/worldline inversion leaves a charge-weighted
source current unchanged: the finite `(-q)(-P)=qP` core of the proposed CPT-like diagonal
relation. -/
theorem gauge_plus_PT_source_invariant (q : ℝ) (u : SpinPair) :
    sourceCurrent (-q) (pairMomentum (PTspin u)) =
      sourceCurrent q (pairMomentum u) := by
  rw [PTspin_momentum]
  exact diagonal_charge_momentum_flip_invariant q _

end GppDiscretePinGooglyDictionary
