import Mathlib.Tactic
import GppVerify.RiemannHypothesis.L2Constraint

/-!
# Cayley shadow--adjoint bridge

Put

  beta(s) = (s - 1) / s.

This is the Cayley coordinate already present in the Nyman--Burnol Hardy picture.  The two
involutions relevant to the RH program become completely different operations on `beta`:

* functional-equation shadow `s -> 1-s` becomes inversion `beta -> beta⁻¹`;
* Hilbert/real adjoint `s -> conj(s)` becomes complex conjugation
  `beta -> conj(beta)`.

Consequently identifying shadow with the positive Hilbert adjoint is exactly the unitary
condition

  beta⁻¹ = conj(beta),

and this happens exactly on `Re(s)=1/2` (away from the two trivial Cayley singular points
`s=0,1`).  This is the finite algebraic core of the proposed Rosati/polarization route: the
functional equation supplies reciprocity; positivity must identify reciprocity with the
Hilbert adjoint.

No statement here says that zeta zeros satisfy the required positive-adjoint hypothesis.
That is the hard arithmetic theorem.
-/

namespace GppCayleyShadowAdjointBridge

open Complex

/-- Burnol/Nyman Cayley coordinate. -/
def beta (s : ℂ) : ℂ := (s - 1) / s

/-- The Cayley coordinate is injective away from its pole at `s=0`. -/
theorem beta_injective_of_ne_zero
    {s t : ℂ} (hs : s ≠ 0) (ht : t ≠ 0) (h : beta s = beta t) : s = t := by
  unfold beta at h
  field_simp [hs, ht] at h
  linear_combination h

/-- Complex conjugation of `s` becomes complex conjugation of the Cayley coordinate. -/
theorem beta_conj (s : ℂ) :
    beta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (beta s) := by
  simp [beta, map_sub, map_div]

/-- Functional-equation shadow becomes multiplicative inversion in the Cayley chart. -/
theorem beta_shadow_eq_inv
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    beta (1 - s) = (beta s)⁻¹ := by
  unfold beta
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1ms : 1 - s ≠ 0 := by
    intro h
    apply hs1
    linarith
  field_simp [hs0, hsm1, h1ms]
  ring

/-- If inverse and conjugate coincide for a nonzero scalar, its norm is one. -/
theorem norm_one_of_inv_eq_conj
    (z : ℂ) (hz : z ≠ 0)
    (h : z⁻¹ = (starRingEnd ℂ) z) :
    ‖z‖ = 1 := by
  apply GppL2.norm_one_of_mul_conj_eq_one z
  rw [← h]
  exact mul_inv_cancel₀ hz

/-- Critical-line points identify shadow and complex conjugation in the original `s` chart. -/
theorem conj_eq_shadow_of_critical
    (s : ℂ) (hs : s.re = (1 / 2 : ℝ)) :
    (starRingEnd ℂ) s = 1 - s := by
  apply Complex.ext
  · simp [hs]
    linarith
  · simp

/--
**Shadow = adjoint iff critical line, in Cayley coordinates.**

Away from `s=0,1`, the functional-equation image of the Cayley coordinate equals its
Hilbert adjoint exactly when `Re(s)=1/2`.
-/
theorem beta_shadow_eq_adjoint_iff_critical
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    beta (1 - s) = (starRingEnd ℂ) (beta s) ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hconj : beta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (beta s) := beta_conj s
    have hbeta : beta (1 - s) = beta ((starRingEnd ℂ) s) := by
      calc
        beta (1 - s) = (starRingEnd ℂ) (beta s) := h
        _ = beta ((starRingEnd ℂ) s) := hconj.symm
    have h1ms : 1 - s ≠ 0 := by
      intro hz
      apply hs1
      linarith
    have hcs : (starRingEnd ℂ) s ≠ 0 := by
      simpa using hs0
    have hsEq : 1 - s = (starRingEnd ℂ) s :=
      beta_injective_of_ne_zero h1ms hcs hbeta
    exact GppL2.conj_eq_shadow_iff_critical s hsEq.symm
  · intro hcrit
    have hcs : (starRingEnd ℂ) s = 1 - s := conj_eq_shadow_of_critical s hcrit
    calc
      beta (1 - s) = beta ((starRingEnd ℂ) s) := by rw [hcs]
      _ = (starRingEnd ℂ) (beta s) := beta_conj s

/--
The same theorem written as the unitary scalar condition: on the critical line, shadow
inversion and Hilbert conjugation agree.
-/
theorem beta_inv_eq_conj_of_critical
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcrit : s.re = (1 / 2 : ℝ)) :
    (beta s)⁻¹ = (starRingEnd ℂ) (beta s) := by
  rw [← beta_shadow_eq_inv s hs0 hs1]
  exact (beta_shadow_eq_adjoint_iff_critical s hs0 hs1).2 hcrit

/-- Critical-line Cayley weights have unit modulus. -/
theorem beta_norm_one_of_critical
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcrit : s.re = (1 / 2 : ℝ)) :
    ‖beta s‖ = 1 := by
  have hbeta0 : beta s ≠ 0 := by
    unfold beta
    exact div_ne_zero (sub_ne_zero.mpr hs1) hs0
  exact norm_one_of_inv_eq_conj (beta s) hbeta0
    (beta_inv_eq_conj_of_critical s hs0 hs1 hcrit)

end GppCayleyShadowAdjointBridge
