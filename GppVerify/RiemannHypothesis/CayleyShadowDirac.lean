import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import GppVerify.RiemannHypothesis.CayleyShadowAdjointBridge

/-!
# Cayley shadow Dirac: order four is not enough

The Cayley coordinate beta(s) = (s - 1) / s turns functional-equation shadow s -> 1-s
into reciprocal inversion. This file keeps that first-order shadow operation distinct
from Hilbert adjoint.

Define Q(s) = [[0, -beta(1-s)], [beta(s), 0]].

Away from s=0,1, shadow reciprocity alone forces Q(s)^2 = -I and Q(s)^4 = I
for every s. Thus the abstract order-four algebra does not detect the critical line.

The critical line is detected by metric compatibility:
Q(s)^* = -Q(s) iff Re(s)=1/2.

No zeta-zero statement is used here.
-/

namespace GppCayleyShadowDirac

open Complex
open GppCayleyShadowAdjointBridge

/-- First-order shadow Dirac with the orientation sign chosen so its square is -I. -/
noncomputable def quarterTurnDirac (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -(beta (1 - s));
     beta s, 0]

/-- Away from s=0,1, the Cayley weight itself is nonzero. -/
lemma beta_ne_zero {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) : beta s ≠ 0 := by
  unfold beta
  exact div_ne_zero (sub_ne_zero.mpr hs1) hs0

/-- Shadow reciprocity alone makes the first-order block a quarter-turn for every s. -/
theorem quarterTurnDirac_sq_neg_one
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    quarterTurnDirac s * quarterTurnDirac s =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hshadow := beta_shadow_eq_inv s hs0 hs1
  have hb0 : beta s ≠ 0 := beta_ne_zero hs0 hs1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnDirac, Matrix.mul_apply, Fin.sum_univ_two, hshadow, hb0]

/-- Consequently the shadow block closes after four applications for every s. -/
theorem quarterTurnDirac_four_one
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    quarterTurnDirac s * quarterTurnDirac s *
      quarterTurnDirac s * quarterTurnDirac s =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  calc
    _ = (quarterTurnDirac s * quarterTurnDirac s) *
        (quarterTurnDirac s * quarterTurnDirac s) := by
          simp only [mul_assoc]
    _ = 1 := by
      rw [quarterTurnDirac_sq_neg_one s hs0 hs1]
      simp

/-- Metric compatibility is exactly the critical line. -/
theorem quarterTurnDirac_skewAdjoint_iff_critical
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Matrix.conjTranspose (quarterTurnDirac s) = -quarterTurnDirac s
      ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have hshadow :
        beta (1 - s) = (starRingEnd ℂ) (beta s) := by
      simpa [quarterTurnDirac, Matrix.conjTranspose_apply] using h01.symm
    exact (beta_shadow_eq_adjoint_iff_critical s hs0 hs1).mp hshadow
  · intro hcrit
    have hshadow :
        beta (1 - s) = (starRingEnd ℂ) (beta s) :=
      (beta_shadow_eq_adjoint_iff_critical s hs0 hs1).mpr hcrit
    have hshadow' :
        (starRingEnd ℂ) (beta (1 - s)) = beta s := by
      have hc := congrArg (starRingEnd ℂ) hshadow
      simpa using hc
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quarterTurnDirac, Matrix.conjTranspose_apply, hshadow, hshadow']

/-- On the critical line the positive square is the Hilbert square of the skew-adjoint
    first-order generator. -/
theorem neg_square_eq_adjoint_mul_of_critical
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcrit : s.re = (1 / 2 : ℝ)) :
    -(quarterTurnDirac s * quarterTurnDirac s) =
      Matrix.conjTranspose (quarterTurnDirac s) * quarterTurnDirac s := by
  have hskew :
      Matrix.conjTranspose (quarterTurnDirac s) = -quarterTurnDirac s :=
    (quarterTurnDirac_skewAdjoint_iff_critical s hs0 hs1).mpr hcrit
  rw [hskew]
  ring

end GppCayleyShadowDirac

#print axioms GppCayleyShadowDirac.quarterTurnDirac_sq_neg_one
#print axioms GppCayleyShadowDirac.quarterTurnDirac_four_one
#print axioms GppCayleyShadowDirac.quarterTurnDirac_skewAdjoint_iff_critical
#print axioms GppCayleyShadowDirac.neg_square_eq_adjoint_mul_of_critical
