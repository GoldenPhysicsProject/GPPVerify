import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Two- and three-layer causal translation overlap bounds

The primitive finite-chain inequalities behind a zero-independent
positive-completed-Weil short-support theorem. They are exact for real
layer norms; transferring them to L² translated intervals and the full
prime-free gamma/pole integrals remains a separate analytical task.
No statement of global Weil positivity or RH is made here.
-/

namespace GppCausalShortWindow

/-- On two causally disjoint translated layers, the crossing term
is at most the sum of the layer energies. -/
theorem two_layer_overlap (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith only [sq_nonneg (a - b)]

/-- The sharp spectral radius of the three-vertex path is sqrt(2).
This is the exact bound on 2 Re⟨f,T_y f⟩ for a three-layer
translation after Cauchy-Schwarz on each adjacent pair. -/
theorem three_layer_overlap (a b c : ℝ) :
    2 * (a*b + b*c) ≤ Real.sqrt 2 * (a^2 + b^2 + c^2) := by
  let t : ℝ := Real.sqrt 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ^ 2 = 2 := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have hsq : 0 ≤ (t*a-b)^2 + (t*c-b)^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hident :
      (t*a-b)^2 + (t*c-b)^2 =
        t * (t*(a^2+b^2+c^2)-2*(a*b+b*c)) := by
    calc
      _ = t * (t*(a^2+b^2+c^2)-2*(a*b+b*c)) +
            (2-t^2)*b^2 := by ring
      _ = _ := by rw [ht2]; ring
  rw [hident] at hsq
  by_contra h
  have hneg : t*(a^2+b^2+c^2)-2*(a*b+b*c) < 0 := by
    have hh : t * (a^2 + b^2 + c^2) < 2*(a*b+b*c) :=
      lt_of_not_ge h
    linarith
  have hprod : t*(t*(a^2+b^2+c^2)-2*(a*b+b*c)) < 0 :=
    mul_neg_of_pos_of_neg ht hneg
  linarith

end GppCausalShortWindow

#print axioms GppCausalShortWindow.two_layer_overlap
#print axioms GppCausalShortWindow.three_layer_overlap
