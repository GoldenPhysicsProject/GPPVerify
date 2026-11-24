import GppVerify.RiemannHypothesis.EtaInversionReal
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The logarithmic Euler sum `K(t)` and its inversion law

`K(t) = Σ_{n ≥ 1} log (1 - e^{-n t})` for `t > 0`.  This module identifies the Euler product of
`EtaInversionReal` with `exp (K t)` and proves the inversion law

  `K(4π²/t) - K(t) = ½ log (t/(2π)) + (4π²/t - t)/24`,

so that `K(t) - t/24 + ¼ log t` is invariant under `t ↦ 4π²/t` (`K_symm`).  This is the functional
equation of the archimedean place written on the logarithmic Euler sum.
-/

open Complex

namespace GppEtaInversion

/-- `K(t) = Σ_{n ≥ 1} log (1 - e^{-n t})`. -/
noncomputable def K (t : ℝ) : ℝ := ∑' n : ℕ, Real.log (1 - Real.exp (-((n + 1 : ℝ) * t)))

theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  have := Real.exp_lt_exp.2 (show -x < 0 by linarith)
  simpa using this

theorem summable_exp_neg {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => Real.exp (-((n + 1 : ℝ) * t)) := by
  have hq : Real.exp (-t) < 1 := exp_neg_lt_one ht
  have hg := (summable_geometric_of_lt_one (Real.exp_pos (-t)).le hq).mul_left (Real.exp (-t))
  refine hg.congr (fun n => ?_)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) (n : ℕ) : 0 < 1 - Real.exp (-((n + 1 : ℝ) * t)) := by
  have hx : (0 : ℝ) < (n + 1 : ℝ) * t := by positivity
  have := exp_neg_lt_one hx
  linarith

theorem summable_log_terms {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => Real.log (1 - Real.exp (-((n + 1 : ℝ) * t))) := by
  have := Real.summable_log_one_add_of_summable (f := fun n : ℕ => -Real.exp (-((n + 1 : ℝ) * t)))
    (summable_exp_neg ht).neg
  simpa [sub_eq_add_neg] using this

/-- The Euler product is `exp (K t)`. -/
theorem etaProd_eq_exp_K {t : ℝ} (ht : 0 < t) : etaProd t = ((Real.exp (K t) : ℝ) : ℂ) := by
  have h := Real.rexp_tsum_eq_tprod (f := fun n : ℕ => 1 - Real.exp (-((n + 1 : ℝ) * t)))
    (one_sub_exp_pos ht) (summable_log_terms ht)
  have hM : Multipliable fun n : ℕ => 1 - Real.exp (-((n + 1 : ℝ) * t)) :=
    Real.multipliable_of_summable_log (one_sub_exp_pos ht) (summable_log_terms ht)
  have hc := (hM.hasProd.map Complex.ofRealHom Complex.continuous_ofReal).tprod_eq
  unfold etaProd K
  rw [h]
  simp only [Function.comp_def, Complex.ofRealHom_eq_coe, Complex.ofReal_sub, Complex.ofReal_one] at hc
  exact hc

/-- **Inversion law for the logarithmic Euler sum.** For `t > 0` and `t' = 4π²/t`,
`K(t') - K(t) = ½ log (t/(2π)) + (t' - t)/24`. -/
theorem K_inversion {t : ℝ} (ht : 0 < t) :
    K (4 * Real.pi ^ 2 / t) - K t =
      Real.log (t / (2 * Real.pi)) / 2 + (4 * Real.pi ^ 2 / t - t) / 24 := by
  have hπ := Real.pi_pos
  have ht' : 0 < 4 * Real.pi ^ 2 / t := by positivity
  have h := eta_inversion_real ht
  rw [etaProd_eq_exp_K ht', etaProd_eq_exp_K ht] at h
  have h2 : Real.exp (-(4 * Real.pi ^ 2 / t) / 24) * Real.exp (K (4 * Real.pi ^ 2 / t)) =
      Real.sqrt (t / (2 * Real.pi)) * (Real.exp (-t / 24) * Real.exp (K t)) := by
    exact_mod_cast h
  have hs : 0 < Real.sqrt (t / (2 * Real.pi)) := Real.sqrt_pos.2 (by positivity)
  have h3 := congrArg Real.log h2
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_mul hs.ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp,
    Real.log_exp, Real.log_sqrt (by positivity)] at h3
  rw [Real.log_exp] at h3
  linarith

/-- **The symmetric combination.** `K(t) - t/24 + ¼ log t` is invariant under `t ↦ 4π²/t`. -/
theorem K_symm {t : ℝ} (ht : 0 < t) :
    K (4 * Real.pi ^ 2 / t) - (4 * Real.pi ^ 2 / t) / 24 + Real.log (4 * Real.pi ^ 2 / t) / 4 =
      K t - t / 24 + Real.log t / 4 := by
  have hπ := Real.pi_pos
  have h := K_inversion ht
  have h1 : Real.log (4 * Real.pi ^ 2 / t) = Real.log (4 * Real.pi ^ 2) - Real.log t :=
    Real.log_div (by positivity) ht.ne'
  have h2 : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log (2 * Real.pi) :=
    Real.log_div ht.ne' (by positivity)
  have h3 : Real.log (4 * Real.pi ^ 2) = 2 * Real.log (2 * Real.pi) := by
    rw [show 4 * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring, Real.log_pow]; norm_num
  rw [h1]
  rw [h2] at h
  linarith

end GppEtaInversion

#print axioms GppEtaInversion.etaProd_eq_exp_K
#print axioms GppEtaInversion.K_inversion
#print axioms GppEtaInversion.K_symm
