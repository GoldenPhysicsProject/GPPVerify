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
        (fun x hx => normRpow_const_on_shell p s hx),
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
    rw [pow_succ, ENNReal.mul_inv (Or.inr hpEntop) (Or.inr hpEnne),
        ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr (pow_ne_zero n hpEnne)), one_mul,
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

/-- **Sanity check at `s = 0`**: the integral of the constant function `1` over `ℤ_p`
    is the total mass `μ(ℤ_p) = 1`. This is the `s = 0` instance of
    `lintegral_norm_rpow` collapsing to `GppPadicHaar.haarMeasure_univ`, and confirms
    the closed form is consistent at the one value where the answer is knowable by an
    entirely independent route. -/
theorem lintegral_norm_rpow_zero :
    ∫⁻ x, normRpow p 0 x ∂(GppPadicHaar.haarMeasure p) = 1 := by
  have hone : ∀ x : PadicInt p, normRpow p 0 x = 1 := by
    intro x; unfold normRpow; exact ENNReal.rpow_zero
  simp_rw [hone]
  rw [lintegral_const, GppPadicHaar.haarMeasure_univ, mul_one]

/-- **The `s = 1` instance**: `∫_{ℤ_p} ‖x‖ dμ`, the first absolute moment of the
    Haar-random `ℤ_p`-point under the p-adic norm. -/
theorem lintegral_norm_rpow_one :
    ∫⁻ x, normRpow p 1 x ∂(GppPadicHaar.haarMeasure p) =
      (1 - (p : ℝ≥0∞)⁻¹) * (1 - (p : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ := by
  rw [lintegral_norm_rpow]
  norm_num

/-- **Tate's local zeta integral, in Tate's own normalization.**

    Tate's thesis studies, for the unramified data `f = 1_{ℤ_p}` and the trivial
    character, the local zeta integral
    `Z(s) = ∫_{ℚ_p} f(x) |x|^s d^×x = ∫_{ℤ_p \ {0}} ‖x‖^s d^×x`
    against the *multiplicative* Haar measure `d^×x`. Taking `d^×x` to be the measure
    induced from our additive `μ` (`GppPadicHaar.haarMeasure`) by `d^×x := dμ / ‖x‖`
    — the standard construction — gives
    `Z(s) = ∫_{ℤ_p} ‖x‖^{s-1} dμ = lintegral_norm_rpow (s - 1)`,
    since dividing by `‖x‖` shifts the exponent down by one and `{0}` is `μ`-null
    (`GppPadicOrigin.haarMeasure_singleton_zero`) so extending the domain from `ℤ_p\{0}`
    back to all of `ℤ_p` changes nothing.

    Under this convention `d^×x` is *not* normalized to give `ℤ_p^×` total mass 1: one
    computes `vol(ℤ_p^×, d^×x) = μ(ℤ_p^×) = μ(ℤ_p) - μ(p ℤ_p) = 1 - p⁻¹` (using
    `GppPadicZetaIntegral.haarMeasure_span_pow` at `n = 1`), matching exactly the
    `(1 - p⁻¹)` prefactor below. So this is the classical non-archimedean local Euler
    factor `(1 - p^{-s})^{-1}` up to precisely that `(1 - p⁻¹)` measure-normalization
    constant — not an extra unexplained fudge factor, but the volume of `ℤ_p^×` under
    this specific choice of multiplicative Haar measure. -/
theorem tate_local_zeta_integral (s : ℝ) :
    ∫⁻ x, normRpow p (s - 1) x ∂(GppPadicHaar.haarMeasure p) =
      (1 - (p : ℝ≥0∞)⁻¹) * (1 - (p : ℝ≥0∞) ^ (-s))⁻¹ := by
  rw [lintegral_norm_rpow, show -(s - 1 + 1) = -s by ring]

end GppPadicFullZeta
