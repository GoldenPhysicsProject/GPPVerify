import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Tactic

/-!
# Prime Poisson radial bridge

For every real p>1 and a>0, the local Euler-factor logarithmic derivative on
s=a+it is exactly the Poisson kernel with radius r=p^{-a}.  This generalizes
the previously proved a=1/2 identity and supplies the radial parameter needed
to connect finite-prime positive-type kernels with the convergent-axis
von-Mangoldt/Hankel hierarchy.

No global prime sum or RH claim is made here.
-/

namespace GppPrimePoissonRadial

open Complex Real
open GppCutkoskyWeil

/-- The radius-a finite-prime Poisson response. -/
noncomputable def WpA (p a t : ℝ) : ℝ :=
  Real.log p * (KrClosed (p ^ (-a)) (t * Real.log p) - 1)

/-- Real rpow closed form in the exact exponent needed below. -/
theorem rpow_neg_eq_exp {p a : ℝ} (hp : 0 < p) :
    p ^ (-a) = Real.exp (-a * Real.log p) := by
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Exact arbitrary-radial local Euler-factor/Poisson-kernel identity. -/
theorem WpA_eq_two_mul_re_minusLogDerivZetaP
    {p a : ℝ} (hp : 1 < p) (ha : 0 < a) (t : ℝ) :
    WpA p a t = 2 * (minusLogDerivZetaP p (a + t * Complex.I)).re := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  set θ : ℝ := t * Real.log p with hθdef
  set r : ℝ := p ^ (-a) with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact Real.rpow_nonneg hp0.le _
  have hnega : -a < 0 := neg_lt_zero.mpr ha
  have hr1 : r < 1 := by
    rw [hrdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp hnega
  have hlogpC : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp0.le).symm
  have hrexp : r = Real.exp (-a * Real.log p) := by
    rw [hrdef]
    exact rpow_neg_eq_exp hp0
  clear_value r θ
  have hlogp_re : (Complex.log (p : ℂ)).re = Real.log p := Complex.log_ofReal_re p
  have hlogp_im : (Complex.log (p : ℂ)).im = 0 := by
    rw [hlogpC]
    exact Complex.ofReal_im _
  have hwre : (-(a + t * Complex.I) * Complex.log p).re = -a * Real.log p := by
    rw [Complex.mul_re, hlogp_re, hlogp_im]
    simp
  have hwim : (-(a + t * Complex.I) * Complex.log p).im = -θ := by
    rw [Complex.mul_im, hlogp_re, hlogp_im, hθdef]
    simp
  have hEre : (Complex.exp (-(a + t * Complex.I) * Complex.log p)).re =
      r * Real.cos θ := by
    rw [Complex.exp_re, hwre, hwim, ← hrexp, Real.cos_neg]
  have hEim : (Complex.exp (-(a + t * Complex.I) * Complex.log p)).im =
      -(r * Real.sin θ) := by
    rw [Complex.exp_im, hwre, hwim, ← hrexp, Real.sin_neg]
    ring
  have hNre :
      (Complex.log p * Complex.exp (-(a + t * Complex.I) * Complex.log p)).re =
        Real.log p * (r * Real.cos θ) := by
    rw [Complex.mul_re, hlogp_re, hlogp_im, hEre]
    ring
  have hNim :
      (Complex.log p * Complex.exp (-(a + t * Complex.I) * Complex.log p)).im =
        Real.log p * -(r * Real.sin θ) := by
    rw [Complex.mul_im, hlogp_re, hlogp_im, hEim]
    ring
  have hDre :
      (1 - Complex.exp (-(a + t * Complex.I) * Complex.log p)).re =
        1 - r * Real.cos θ := by
    rw [Complex.sub_re, Complex.one_re, hEre]
  have hDim :
      (1 - Complex.exp (-(a + t * Complex.I) * Complex.log p)).im =
        r * Real.sin θ := by
    rw [Complex.sub_im, Complex.one_im, hEim]
    ring
  unfold WpA minusLogDerivZetaP
  rw [Complex.div_re, Complex.normSq_apply, hNre, hNim, hDre, hDim]
  rw [← hrdef, ← hθdef]
  unfold KrClosed
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h1cos : (0 : ℝ) ≤ 1 - Real.cos θ := by
    linarith [Real.cos_le_one θ]
  have hdenpos : (0 : ℝ) < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    nlinarith [mul_pos h1r h1r, mul_nonneg hr0 h1cos]
  have hdeneq :
      (1 - r * Real.cos θ) * (1 - r * Real.cos θ) +
          (r * Real.sin θ) * (r * Real.sin θ) =
        1 - 2 * r * Real.cos θ + r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hdeneq]
  field_simp
  linear_combination (Real.log p) * (2 * r ^ 2) * Real.sin_sq_add_cos_sq θ

end GppPrimePoissonRadial

#print axioms GppPrimePoissonRadial.rpow_neg_eq_exp
#print axioms GppPrimePoissonRadial.WpA_eq_two_mul_re_minusLogDerivZetaP
