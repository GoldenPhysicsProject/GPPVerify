import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.RiemannHypothesis.CayleyShadowDirac

/-!
# Haar-fixed shadow-pair metric rigidity

This file strengthens the Cayley shadow-adjoint bridge by allowing an arbitrary
two-state metric, including off-diagonal coherence.

Let D swap the two shadow orientations and let

  Q_a = [[0,-a^{-1}],[a,0]].

If a nondegenerate metric G is invariant under the swap D and Q_a is skew-adjoint
with respect to that SAME metric, then a^{-1}=conj(a). Thus |a|=1.

The proof uses only the (0,0) entry of swap invariance and the (0,1) entry of
metric skew-adjointness. No diagonal-metric assumption is made.

Specializing a=beta(s)=(s-1)/s therefore forces Re(s)=1/2.
-/

namespace GppCayleyHaarMetricRigidity

open Complex
open GppCayleyShadowAdjointBridge

/-- Swap of the two shadow orientations. -/
def shadowSwap : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Generic reciprocal first-order shadow block. -/
noncomputable def reciprocalDirac (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -(a⁻¹); a, 0]

/-- Swap invariance equalizes the two diagonal metric weights, even with coherence. -/
lemma diag_eq_of_swap_invariant
    (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hswap : Matrix.conjTranspose shadowSwap * G * shadowSwap = G) :
    G 1 1 = G 0 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hswap
  simpa [shadowSwap, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply] using h

/--
Metric skew-adjointness plus swap invariance forces reciprocal shadow to equal Hilbert
conjugation. Positivity is stronger than needed here; nondegeneracy of one diagonal
weight already suffices.
-/
theorem inv_eq_conj_of_swap_metric_skew
    (a : ℂ) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hswap : Matrix.conjTranspose shadowSwap * G * shadowSwap = G)
    (hG00 : G 0 0 ≠ 0)
    (hskew :
      Matrix.conjTranspose (reciprocalDirac a) * G +
        G * reciprocalDirac a = 0) :
    a⁻¹ = (starRingEnd ℂ) a := by
  have hdiag : G 1 1 = G 0 0 :=
    diag_eq_of_swap_invariant G hswap
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hskew
  simp [reciprocalDirac, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, hdiag] at h01
  have hfac : G 0 0 * ((starRingEnd ℂ) a - a⁻¹) = 0 := by
    linear_combination h01
  have hdiff : (starRingEnd ℂ) a - a⁻¹ = 0 :=
    (mul_eq_zero.mp hfac).resolve_left hG00
  exact (sub_eq_zero.mp hdiff).symm

/-- The generic reciprocal shadow block therefore has unit scalar modulus. -/
theorem norm_one_of_swap_metric_skew
    (a : ℂ) (ha : a ≠ 0) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hswap : Matrix.conjTranspose shadowSwap * G * shadowSwap = G)
    (hG00 : G 0 0 ≠ 0)
    (hskew :
      Matrix.conjTranspose (reciprocalDirac a) * G +
        G * reciprocalDirac a = 0) :
    ‖a‖ = 1 := by
  exact norm_one_of_inv_eq_conj a ha
    (inv_eq_conj_of_swap_metric_skew a G hswap hG00 hskew)

/--
Specialization to the RH Cayley coordinate: a fixed shadow-symmetric metric cannot make
the first-order reciprocal block skew-adjoint off the critical line.
-/
theorem critical_of_cayley_swap_metric_skew
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hswap : Matrix.conjTranspose shadowSwap * G * shadowSwap = G)
    (hG00 : G 0 0 ≠ 0)
    (hskew :
      Matrix.conjTranspose (reciprocalDirac (beta s)) * G +
        G * reciprocalDirac (beta s) = 0) :
    s.re = (1 / 2 : ℝ) := by
  have hinv : (beta s)⁻¹ = (starRingEnd ℂ) (beta s) :=
    inv_eq_conj_of_swap_metric_skew (beta s) G hswap hG00 hskew
  have hshadow : beta (1 - s) = (starRingEnd ℂ) (beta s) := by
    rw [beta_shadow_eq_inv s hs0 hs1]
    exact hinv
  exact (beta_shadow_eq_adjoint_iff_critical s hs0 hs1).mp hshadow

end GppCayleyHaarMetricRigidity

#print axioms GppCayleyHaarMetricRigidity.diag_eq_of_swap_invariant
#print axioms GppCayleyHaarMetricRigidity.inv_eq_conj_of_swap_metric_skew
#print axioms GppCayleyHaarMetricRigidity.norm_one_of_swap_metric_skew
#print axioms GppCayleyHaarMetricRigidity.critical_of_cayley_swap_metric_skew
