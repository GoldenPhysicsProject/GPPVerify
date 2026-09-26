import GppVerify.RiemannHypothesis.PadicConformalScaling
import Mathlib.Tactic

/-!
# p-adic Möbius conformal kinematics

A decisive step beyond a mere analogy with one-dimensional CFT is that the local
p-adic field carries the same exact fractional-linear geometry as an ordinary
one-dimensional conformal boundary.  For

  g(x) = (a x + b) / (c x + d),

one has the field identity

  g(x)-g(y) = det(g) (x-y) / ((c x+d)(c y+d)),

and therefore, using the multiplicative p-adic norm,

  |g(x)-g(y)|_p
    = |det(g)|_p |x-y|_p / (|c x+d|_p |c y+d|_p).

This is precisely the local conformal covariance law underlying `PGL(2,Q_p)`
actions on the p-adic projective line.  The theorem is proved directly on
Mathlib's `Padic p` field; no CFT or holography axiom is introduced.
-/

namespace GppPadicMobiusConformal

variable (p : ℕ) [Fact p.Prime]

/-- Fractional-linear action in an affine chart of the p-adic projective line. -/
noncomputable def mobius (a b c d x : Padic p) : Padic p :=
  (a * x + b) / (c * x + d)

/-- The determinant controlling a fractional-linear transformation. -/
def mobiusDet (a b c d : Padic p) : Padic p := a * d - b * c

/-- Exact difference law for two points under the same Möbius transformation. -/
theorem mobius_sub
    {a b c d x y : Padic p}
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) :
    mobius p a b c d x - mobius p a b c d y =
      mobiusDet p a b c d * (x - y) /
        ((c * x + d) * (c * y + d)) := by
  unfold mobius mobiusDet
  field_simp [hx, hy]
  ring

/-- **p-adic conformal distance covariance.**  The p-adic norm transforms with
the exact two endpoint Jacobian factors of a one-dimensional primary geometry. -/
theorem norm_mobius_sub
    {a b c d x y : Padic p}
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) :
    ‖mobius p a b c d x - mobius p a b c d y‖ =
      ‖mobiusDet p a b c d‖ * ‖x - y‖ /
        (‖c * x + d‖ * ‖c * y + d‖) := by
  rw [mobius_sub p hx hy, norm_div, norm_mul, norm_mul]

/-- Affine dilations are the `c=0,b=0,d=1` Möbius subgroup and scale p-adic
distance exactly by the field norm. -/
theorem norm_dilation_sub (a x y : Padic p) :
    ‖a * x - a * y‖ = ‖a‖ * ‖x - y‖ := by
  rw [← mul_sub, norm_mul]

/-- Translation is an exact p-adic isometry. -/
theorem norm_translation_sub (b x y : Padic p) :
    ‖(x + b) - (y + b)‖ = ‖x - y‖ := by
  congr 1
  ring

/-- Inversion, the Weyl generator of the one-dimensional Möbius group, obeys
the corresponding reciprocal distance law. -/
theorem norm_inv_sub_inv
    {x y : Padic p} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x⁻¹ - y⁻¹‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
  have h := norm_mobius_sub (p := p)
    (a := 0) (b := 1) (c := 1) (d := 0) (x := x) (y := y)
    (by simpa using hx) (by simpa using hy)
  simpa [mobius, mobiusDet, mul_comm] using h

end GppPadicMobiusConformal

#print axioms GppPadicMobiusConformal.mobius_sub
#print axioms GppPadicMobiusConformal.norm_mobius_sub
#print axioms GppPadicMobiusConformal.norm_dilation_sub
#print axioms GppPadicMobiusConformal.norm_inv_sub_inv
