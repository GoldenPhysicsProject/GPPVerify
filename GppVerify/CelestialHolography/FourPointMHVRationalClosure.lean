import Mathlib.Tactic

/-!
# Four-point adjacent-MHV rational coefficient cancellation

This file formalizes the final algebraic cancellation in the D-dimensional
unitarity reconstruction of the four-point adjacent-MHV rational remainder.

The amplitude-specific generalized-unitarity coefficient is deliberately supplied
as a hypothesis: this theorem does not claim to derive Badger's bubble coefficient
or the vanishing of the triangle coefficients.  It proves that, once the exact
box coefficient and reduced bubble relation are available, the box-plus-bubble
combination collapses to the stated compact rational expression.
-/

namespace GppFourPointMHVRationalClosure

open Complex

/-- Algebraic closure of the adjacent-MHV FDH rational remainder.

`Q` is the convention-fixed spinor phase, `s=s12`, `t=s23`, and `C2` is the
single independent `mu^2` bubble coefficient after four-point spinor reduction.
The hypothesis is exactly the reduced relation

  t C2 = i Q * 2(2s-3t)/(3t).

Together with `C4 = 2 i Q`, `I4[mu^4] -> -1/6`, and
`I2[mu^2] -> -t/6`, the rational combination is

  R = -(1/6) C4 -(t/6) C2 = -(2i/9)(s/t)Q.
-/
theorem adjacentMHV_rational_closure
    (s t : ℝ) (Q C2 : ℂ) (ht : t ≠ 0)
    (hC2 :
      (t : ℂ) * C2 =
        I * Q *
          (2 * (2 * (s : ℂ) - 3 * (t : ℂ)) / (3 * (t : ℂ)))) :
    (-(1 : ℂ) / 6) * (2 * I * Q) - ((t : ℂ) / 6) * C2 =
      (-(2 : ℂ) * I / 9) * ((s : ℂ) / (t : ℂ)) * Q := by
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  calc
    (-(1 : ℂ) / 6) * (2 * I * Q) - ((t : ℂ) / 6) * C2 =
        (-(1 : ℂ) / 6) * (2 * I * Q) -
          ((1 : ℂ) / 6) * ((t : ℂ) * C2) := by ring
    _ = (-(1 : ℂ) / 6) * (2 * I * Q) -
          ((1 : ℂ) / 6) *
            (I * Q * (2 * (2 * (s : ℂ) - 3 * (t : ℂ)) / (3 * (t : ℂ)))) := by
          rw [hC2]
    _ = (-(2 : ℂ) * I / 9) * ((s : ℂ) / (t : ℂ)) * Q := by
          field_simp [htC]
          ring

end GppFourPointMHVRationalClosure

#print axioms GppFourPointMHVRationalClosure.adjacentMHV_rational_closure
