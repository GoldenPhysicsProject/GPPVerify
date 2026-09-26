import GppVerify.RiemannHypothesis.ZetaFisherArithmeticBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Strict positivity of the reflected KL orientation kernel

For midpoint `m` and half-gap `L>0`, the antisymmetric KL kernel is

  2 y (g(m-y) - g(m+y)).

This file proves the exact strict-integral step under the local hypotheses needed in
applications: continuity of `g` and strict decrease across each reflected pair in
`0<y<L`.  The separate Bregman-to-triangular-kernel identity can then feed this lemma.
-/

namespace GppKLOrientationKernel

open Set MeasureTheory intervalIntegral

/-- Reflected antisymmetric Fisher kernel. -/
def reflectedKernel (g : ℝ → ℝ) (m y : ℝ) : ℝ :=
  2 * y * (g (m - y) - g (m + y))

/-- A strictly decreasing reflected pair makes the kernel strictly positive for `y>0`. -/
theorem reflectedKernel_pos
    {g : ℝ → ℝ} {m y : ℝ}
    (hy : 0 < y) (hg : g (m + y) < g (m - y)) :
    0 < reflectedKernel g m y := by
  unfold reflectedKernel
  have hdiff : 0 < g (m - y) - g (m + y) := sub_pos.mpr hg
  positivity

/-- **Strict reflected-kernel integral positivity.**
If `g` is continuous and strictly decreases across every reflected pair in the
interior of a nontrivial half-interval, then the antisymmetric kernel has positive
integral. -/
theorem reflectedKernel_integral_pos
    {g : ℝ → ℝ} {m L : ℝ}
    (hL : 0 < L)
    (hgcont : Continuous g)
    (hg : ∀ y ∈ Ioo (0 : ℝ) L, g (m + y) < g (m - y)) :
    0 < ∫ y in (0 : ℝ)..L, reflectedKernel g m y := by
  have hcont : Continuous (fun y : ℝ => reflectedKernel g m y) := by
    unfold reflectedKernel
    fun_prop
  apply intervalIntegral_pos_of_pos_on hcont.intervalIntegrable
  · intro y hy
    exact reflectedKernel_pos hy.1 (hg y hy)
  · exact hL

end GppKLOrientationKernel

#print axioms GppKLOrientationKernel.reflectedKernel_pos
#print axioms GppKLOrientationKernel.reflectedKernel_integral_pos
