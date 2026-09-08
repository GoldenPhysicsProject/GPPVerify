import Mathlib.Tactic

/-!
# Local Weyl-spinor reconstruction from null-direction quartic data

A totally symmetric rank-four two-spinor has five independent components.  On an affine
spinor chart `lambda=(1,z)`, its principal-spinor contraction is a binary quartic

  Q(z) = a0 + a1 z + a2 z^2 + a3 z^3 + a4 z^4

(up to the conventional binomial factors, which are an invertible change of coefficients).
Therefore the chiral Weyl spinor is determined by its contractions along sufficiently many
null directions.

This module proves an explicit finite injectivity statement: values at

  z = 0, 1, -1, 2, -2

determine all five coefficients.  Applying the theorem independently to the left and right
quartics shows that paired null-direction data determines BOTH chiral Weyl carriers locally.

This is exactly the algebra needed by the nonchiral null-ray route to the googly problem:
one need not manufacture one Weyl chirality from the other if the parent null/contact
geometry supplies both quartic contractions.  What remains hard is the differential-
geometric theorem identifying the actual curved contact/Jacobi obstruction with these
quartics and gluing the reconstruction globally.
-/

namespace GppWeylQuarticNullReconstruction

/-- Five coefficients of a binary quartic on an affine spinor chart. -/
structure Quartic5 where
  a0 : ℝ
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  deriving DecidableEq

/-- Affine evaluation of the quartic. -/
def qeval (Q : Quartic5) (z : ℝ) : ℝ :=
  Q.a0 + Q.a1*z + Q.a2*z^2 + Q.a3*z^3 + Q.a4*z^4

/-- If a quartic vanishes on the five explicit null directions, all coefficients vanish. -/
theorem quartic_zero_of_five_samples
    (Q : Quartic5)
    (h0 : qeval Q 0 = 0)
    (h1 : qeval Q 1 = 0)
    (hm1 : qeval Q (-1) = 0)
    (h2 : qeval Q 2 = 0)
    (hm2 : qeval Q (-2) = 0) :
    Q = ⟨0,0,0,0,0⟩ := by
  rcases Q with ⟨a,b,c,d,e⟩
  simp [qeval] at h0 h1 hm1 h2 hm2 ⊢
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor <;> linarith

/-- Equality of five samples implies equality of quartics. -/
theorem quartic_ext_five_samples
    (Q R : Quartic5)
    (h0 : qeval Q 0 = qeval R 0)
    (h1 : qeval Q 1 = qeval R 1)
    (hm1 : qeval Q (-1) = qeval R (-1))
    (h2 : qeval Q 2 = qeval R 2)
    (hm2 : qeval Q (-2) = qeval R (-2)) :
    Q = R := by
  rcases Q with ⟨a0,a1,a2,a3,a4⟩
  rcases R with ⟨b0,b1,b2,b3,b4⟩
  simp [qeval] at h0 h1 hm1 h2 hm2 ⊢
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor <;> linarith

/-- Paired chiral Weyl carrier. -/
structure WeylPair where
  left : Quartic5
  right : Quartic5
  deriving DecidableEq

/-- Googly/factor exchange of the two chiral quartics. -/
def exchangeWeyl (W : WeylPair) : WeylPair := ⟨W.right,W.left⟩

/-- The exchange is involutive. -/
theorem exchangeWeyl_involution (W : WeylPair) :
    exchangeWeyl (exchangeWeyl W) = W := by
  cases W
  rfl

/-- Ten explicit null-direction samples (five per chirality) determine the full paired
Weyl carrier. -/
theorem weylPair_ext_ten_samples
    (W V : WeylPair)
    (l0 : qeval W.left 0 = qeval V.left 0)
    (l1 : qeval W.left 1 = qeval V.left 1)
    (lm1 : qeval W.left (-1) = qeval V.left (-1))
    (l2 : qeval W.left 2 = qeval V.left 2)
    (lm2 : qeval W.left (-2) = qeval V.left (-2))
    (r0 : qeval W.right 0 = qeval V.right 0)
    (r1 : qeval W.right 1 = qeval V.right 1)
    (rm1 : qeval W.right (-1) = qeval V.right (-1))
    (r2 : qeval W.right 2 = qeval V.right 2)
    (rm2 : qeval W.right (-2) = qeval V.right (-2)) :
    W = V := by
  cases W with
  | mk WL WR =>
    cases V with
    | mk VL VR =>
      have hL : WL = VL := quartic_ext_five_samples WL VL l0 l1 lm1 l2 lm2
      have hR : WR = VR := quartic_ext_five_samples WR VR r0 r1 rm1 r2 rm2
      subst VL
      subst VR
      rfl

/-- Factor exchange simply exchanges the corresponding null-direction quartic data. -/
theorem qeval_exchange_left (W : WeylPair) (z : ℝ) :
    qeval (exchangeWeyl W).left z = qeval W.right z := by rfl

theorem qeval_exchange_right (W : WeylPair) (z : ℝ) :
    qeval (exchangeWeyl W).right z = qeval W.left z := by rfl

end GppWeylQuarticNullReconstruction
