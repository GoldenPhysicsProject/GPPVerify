import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The Euler product `∏ (1 - e^{-nt})` under `t ↦ 4π²/t`

For `t > 0` write `P(t) = ∏_{n ≥ 1} (1 - e^{-n t})` (`etaProd`).  The Dedekind eta function on
the imaginary axis is `η(i t/(2π)) = e^{-t/24} P(t)` (`eta_imag`), and Mathlib's modular
transformation `η(-1/z) = (√I)⁻¹ √z η(z)` at `z = i t/(2π)` becomes the real-variable
inversion formula

  `e^{-t'/24} P(t') = √(t/(2π)) · e^{-t/24} P(t)`,  `t' = 4π²/t`,

(`eta_inversion_real`).  The inversion is exact: the product at `4π²/t` and the product at `t` differ by the explicit
elementary factor `√(t/(2π)) · e^{(t' - t)/24}` (here `t' = 4π²/t`), which is the functional
equation of the archimedean place written on the Euler product.
-/

open Complex ModularForm

namespace GppEtaInversion

/-- The real-variable Euler product `P(t) = ∏_{n ≥ 1} (1 - e^{-n t})`, valued in `ℂ`. -/
noncomputable def etaProd (t : ℝ) : ℂ :=
  ∏' n : ℕ, (1 - ((Real.exp (-((n + 1 : ℝ) * t)) : ℝ) : ℂ))

/-- `η` on the imaginary axis is `e^{-t/24} P(t)`. -/
theorem eta_imag (t : ℝ) :
    η (I * ((t / (2 * Real.pi) : ℝ) : ℂ)) = ((Real.exp (-t / 24) : ℝ) : ℂ) * etaProd t := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold ModularForm.eta etaProd
  congr 1
  · simp only [Function.Periodic.qParam]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · refine tprod_congr (fun n => ?_)
    rw [ModularForm.eta_q_eq_cexp, Complex.ofReal_exp]
    congr 2
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]

/-- `√(I r) = √I · √r` for `r > 0`. -/
theorem sqrt_I_mul {r : ℝ} (hr : 0 < r) :
    Complex.sqrt (I * (r : ℂ)) = Complex.sqrt I * ((Real.sqrt r : ℝ) : ℂ) := by
  have hz : I * (r : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hr.ne')
  rw [sqrt_eq_exp hz, sqrt_eq_exp I_ne_zero, mul_comm I, Complex.log_ofReal_mul hr I_ne_zero]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le, Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne')]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [Complex.ofReal_log hr.le]
  ring

/-- **Inversion of the Euler product.** For `t > 0` and `t' = 4π²/t`,
`e^{-t'/24} P(t') = √(t/(2π)) · e^{-t/24} P(t)`. -/
theorem eta_inversion_real {t : ℝ} (ht : 0 < t) :
    ((Real.exp (-(4 * Real.pi ^ 2 / t) / 24) : ℝ) : ℂ) * etaProd (4 * Real.pi ^ 2 / t) =
      ((Real.sqrt (t / (2 * Real.pi)) : ℝ) : ℂ) *
        (((Real.exp (-t / 24) : ℝ) : ℂ) * etaProd t) := by
  have hπ := Real.pi_pos
  set r : ℝ := t / (2 * Real.pi) with hr_def
  have hr : 0 < r := by positivity
  have hz : (I * (r : ℂ)) ∈ {z : ℂ | 0 < z.im} := by simpa using hr
  have h := eta_comp_eq_csqrt_I_inv hz
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have hinv : -1 / (I * (r : ℂ)) = I * ((4 * Real.pi ^ 2 / t / (2 * Real.pi) : ℝ) : ℂ) := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have : ((4 * Real.pi ^ 2 / t / (2 * Real.pi) : ℝ) : ℂ) = ((r : ℂ))⁻¹ := by
      rw [hr_def]; push_cast; field_simp; ring
    rw [this]
    field_simp
    simp [Complex.I_sq]
  rw [hinv, eta_imag, sqrt_I_mul hr, eta_imag t] at h
  have hI : Complex.sqrt I ≠ 0 := by simp [sqrt_eq_exp I_ne_zero, Complex.exp_ne_zero]
  rw [show (r : ℝ) = t / (2 * Real.pi) from rfl] at h
  rw [h]
  field_simp
  rw [hr_def]
  ring

end GppEtaInversion

#print axioms GppEtaInversion.eta_imag
#print axioms GppEtaInversion.eta_inversion_real
