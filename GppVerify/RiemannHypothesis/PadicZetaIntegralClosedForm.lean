import GppVerify.RiemannHypothesis.PadicFullZetaIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The full p-adic zeta integral: closed form

The capstone of this session's p-adic infrastructure thread: the exact geometric-series
evaluation of Tate's-thesis lecture notes' Example 4.10,
`∫_{ℤ_p} ‖x‖ˢ dμ = (1 - 1/p) · (1 - p⁻⁽ˢ⁺¹⁾)⁻¹`, for every real `s`. Not sourced from a
specific Golden Physics Project paper.

Assembles every piece built in this thread: the shell partition (`PadicFullZetaIntegral`),
the exact shell measure (`PadicShellMeasure`), the exact shell norm (`PadicShellNorm`), and
the origin's zero measure (`PadicOriginMeasure`), via `MeasureTheory.lintegral_iUnion` and
`ENNReal.tsum_geometric`.
-/

namespace GppPadicFullZeta

open MeasureTheory
open scoped ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- The integrand `‖x‖ˢ`, valued in `ℝ≥0∞`. -/
noncomputable def normRpow (s : ℝ) (x : PadicInt p) : ℝ≥0∞ := (ENNReal.ofReal ‖x‖) ^ s

theorem normRpow_const_on_shell (s : ℝ) {n : ℕ} {x : PadicInt p} (hx : x ∈ shell p n) :
    normRpow p s x = (ENNReal.ofReal ((p : ℝ) ^ (-(n : ℤ)))) ^ s := by
  unfold normRpow
  rw [GppPadicShellNorm.norm_eq_of_mem_shell p hx]

/-- **Shell term**: the integral of `‖x‖ˢ` over shell `n` is the genuine geometric term
    `(1 - 1/p) · (p⁻⁽ˢ⁺¹⁾)ⁿ`. -/
theorem shell_term_eq (s : ℝ) (n : ℕ) :
    ∫⁻ x in shell p n, normRpow p s x ∂(GppPadicHaar.haarMeasure p) =
      (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞) ^ (-(s + 1))) ^ n := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpow_pos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos hpR _
  rw [setLIntegral_congr_fun (measurableSet_shell p n)
        (Filter.Eventually.of_forall (fun x hx => normRpow_const_on_shell p s hx)),
      setLIntegral_const]
  have hshell_eq : shell p n = (Ideal.span {(p : PadicInt p) ^ n} : Set (PadicInt p)) \
      (Ideal.span {(p : PadicInt p) ^ (n + 1)} : Set (PadicInt p)) := rfl
  rw [hshell_eq, GppPadicShell.haarMeasure_shell]
  -- Goal: (ofReal (p^(-n:ℤ)))^s * ((p^n)⁻¹ - (p^(n+1))⁻¹) = (1-p⁻¹) * (p^(-(s+1)))^n
  have hval : ((p : ℝ) ^ (-(n : ℤ))) ^ s = (p : ℝ) ^ (-(n : ℝ) * s) := by
    rw [← Real.rpow_intCast (p : ℝ) (-(n : ℤ)), ← Real.rpow_mul hpR.le]
    norm_num
  rw [ENNReal.ofReal_rpow_of_pos hpow_pos, hval, ← ENNReal.ofReal_rpow_of_pos hpR]
  have hcast : ENNReal.ofReal (p : ℝ) = (p : ℝ≥0∞) := ENNReal.ofReal_natCast p
  rw [hcast]
  -- Goal: (p:ℝ≥0∞)^(-(n:ℝ)*s) * ((p^n)⁻¹ - (p^(n+1))⁻¹) = (1-p⁻¹) * (p^(-(s+1)))^n
  have hpEnne : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hpEntop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hshellmeasure : ((p : ℝ≥0∞) ^ n)⁻¹ - ((p : ℝ≥0∞) ^ (n + 1))⁻¹ =
      (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞) ^ n)⁻¹ := by
    rw [pow_succ, ENNReal.mul_inv (Or.inr hpEntop) (Or.inr hpEnne), tsub_mul, one_mul,
        mul_comm ((p : ℝ≥0∞) ^ n)⁻¹ (p : ℝ≥0∞)⁻¹]
  rw [hshellmeasure]
  rw [show (p : ℝ≥0∞) ^ (-(n : ℝ) * s) * ((1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞) ^ n)⁻¹) =
        (1 - (p : ℝ≥0∞)⁻¹) * ((p : ℝ≥0∞) ^ (-(n : ℝ) * s) * ((p : ℝ≥0∞) ^ n)⁻¹) by ring]
  congr 1
  have hpn : ((p : ℝ≥0∞) ^ n)⁻¹ = (p : ℝ≥0∞) ^ (-(n : ℝ)) := by
    rw [← ENNReal.rpow_natCast (p : ℝ≥0∞) n, ← ENNReal.rpow_neg]
  have hrhs : ((p : ℝ≥0∞) ^ (-(s + 1))) ^ n = (p : ℝ≥0∞) ^ (-(s + 1) * (n : ℝ)) := by
    rw [← ENNReal.rpow_natCast ((p : ℝ≥0∞) ^ (-(s + 1))) n, ← ENNReal.rpow_mul]
  rw [hpn, hrhs, ← ENNReal.rpow_add _ _ hpEnne hpEntop,
      show -(n : ℝ) * s + -(n : ℝ) = -(s + 1) * (n : ℝ) by ring]

/-- **The full p-adic zeta integral.** -/
theorem lintegral_norm_rpow (s : ℝ) :
    ∫⁻ x, normRpow p s x ∂(GppPadicHaar.haarMeasure p) =
      (1 - (p : ℝ≥0∞)⁻¹) * (1 - (p : ℝ≥0∞) ^ (-(s + 1)))⁻¹ := by
  have horigin : ∫⁻ x in ({0} : Set (PadicInt p)), normRpow p s x ∂(GppPadicHaar.haarMeasure p) = 0 := by
    show ∫⁻ x, normRpow p s x ∂((GppPadicHaar.haarMeasure p).restrict ({0} : Set (PadicInt p))) = 0
    rw [Measure.restrict_eq_zero.mpr (GppPadicOrigin.haarMeasure_singleton_zero p),
        lintegral_zero_measure]
  have hstep :
      ∫⁻ x, normRpow p s x ∂(GppPadicHaar.haarMeasure p) =
        ∫⁻ x in (Set.univ : Set (PadicInt p)), normRpow p s x ∂(GppPadicHaar.haarMeasure p) := by
    rw [Measure.restrict_univ]
  rw [hstep, univ_eq_shells p,
      lintegral_union (measurableSet_shell_iUnion p) (singleton_disjoint_shells p),
      horigin, zero_add,
      lintegral_iUnion (measurableSet_shell p) (shell_pairwise_disjoint p)]
  simp_rw [shell_term_eq p s]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

end GppPadicFullZeta
