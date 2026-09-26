import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Gamma-pair recurrence for the spectral convolution family

The all-order Mehler--Fock/Wiener--Hopf family uses the conjugate Gamma product

  Gamma(a+i x) Gamma(a-i x).

The only special-function input needed for its polynomial recursion is Euler's
one-step Gamma recurrence.  This file proves, for every real `a>0`,

  Gamma(a+1+i x) Gamma(a+1-i x)
    = (a^2+x^2) Gamma(a+i x) Gamma(a-i x).

It also records the exact spectral reflection symmetry `x -> -x`: the two Gamma
factors simply exchange places, so the pair is an even function of the principal-series
spectral parameter.
-/

namespace GppSpectralGammaPair

open Complex

/-- Conjugate-principal-series Gamma pair at real height `x` and positive real shift `a`. -/
noncomputable def gammaPair (a x : ℝ) : ℂ :=
  Complex.Gamma ((a : ℂ) + (x : ℂ) * I) *
    Complex.Gamma ((a : ℂ) - (x : ℂ) * I)

/-- The conjugate Gamma pair is exactly even in the spectral height. -/
theorem gammaPair_neg (a x : ℝ) : gammaPair a (-x) = gammaPair a x := by
  unfold gammaPair
  have hp : ((a : ℂ) + ((-x : ℝ) : ℂ) * I) =
      ((a : ℂ) - (x : ℂ) * I) := by
    push_cast
    ring
  have hm : ((a : ℂ) - ((-x : ℝ) : ℂ) * I) =
      ((a : ℂ) + (x : ℂ) * I) := by
    push_cast
    ring
  rw [hp, hm]
  ring

/-- The conjugate Gamma pair gains exactly the quadratic factor `a^2+x^2` under `a -> a+1`. -/
theorem gammaPair_add_one {a : ℝ} (ha : 0 < a) (x : ℝ) :
    gammaPair (a + 1) x =
      (((a ^ 2 + x ^ 2 : ℝ) : ℂ) * gammaPair a x) := by
  let zp : ℂ := (a : ℂ) + (x : ℂ) * I
  let zm : ℂ := (a : ℂ) - (x : ℂ) * I
  have hzp : zp ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [zp] at hre
    linarith
  have hzm : zm ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [zm] at hre
    linarith
  have hp := Complex.Gamma_add_one zp hzp
  have hm := Complex.Gamma_add_one zm hzm
  have hplus :
      ((a + 1 : ℝ) : ℂ) + (x : ℂ) * I = zp + 1 := by
    simp [zp]
    ring
  have hminus :
      ((a + 1 : ℝ) : ℂ) - (x : ℂ) * I = zm + 1 := by
    simp [zm]
    ring
  unfold gammaPair
  rw [hplus, hminus, hp, hm]
  have hquadC : zp * zm = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
    dsimp [zp, zm]
    calc
      ((a : ℂ) + (x : ℂ) * I) * ((a : ℂ) - (x : ℂ) * I)
          = (a : ℂ) ^ 2 - ((x : ℂ) * I) ^ 2 := by ring
      _ = (a : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
        rw [mul_pow]
        norm_num
  have hcast : (a : ℂ) ^ 2 + (x : ℂ) ^ 2 = ((a ^ 2 + x ^ 2 : ℝ) : ℂ) := by
    norm_num
  have hquad : zp * zm = ((a ^ 2 + x ^ 2 : ℝ) : ℂ) := hquadC.trans hcast
  calc
    zp * Complex.Gamma zp * (zm * Complex.Gamma zm)
        = (zp * zm) * (Complex.Gamma zp * Complex.Gamma zm) := by ring
    _ = ((a ^ 2 + x ^ 2 : ℝ) : ℂ) *
          (Complex.Gamma ((a : ℂ) + (x : ℂ) * I) *
            Complex.Gamma ((a : ℂ) - (x : ℂ) * I)) := by
          rw [hquad]

/-- Integer-step specialization used by the `rho_m` hierarchy. -/
theorem gammaPair_nat_succ (m : ℕ) (x : ℝ) :
    gammaPair ((m : ℝ) + 2) x =
      (((((m : ℝ) + 1) ^ 2 + x ^ 2 : ℝ) : ℂ) *
        gammaPair ((m : ℝ) + 1) x) := by
  have h := gammaPair_add_one (a := (m : ℝ) + 1) (by positivity) x
  have hm : ((m : ℝ) + 2) = (((m : ℝ) + 1) + 1) := by ring
  calc
    gammaPair ((m : ℝ) + 2) x = gammaPair (((m : ℝ) + 1) + 1) x := by rw [hm]
    _ = (((((m : ℝ) + 1) ^ 2 + x ^ 2 : ℝ) : ℂ) *
        gammaPair ((m : ℝ) + 1) x) := h

end GppSpectralGammaPair

#print axioms GppSpectralGammaPair.gammaPair_neg
#print axioms GppSpectralGammaPair.gammaPair_add_one
#print axioms GppSpectralGammaPair.gammaPair_nat_succ
