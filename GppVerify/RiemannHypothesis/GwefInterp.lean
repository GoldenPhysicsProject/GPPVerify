import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity
import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.MeyerSpectralWeil
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly
import GppVerify.RiemannHypothesis.XiZeroSymmetry
import GppVerify.RiemannHypothesis.XiReflection
import GppVerify.RiemannHypothesis.MellinInterpolation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Push

import GppVerify.RiemannHypothesis.ExplicitFormulaE1Strip
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# GW-EF interpolation (ported from Codex's audited scratch, run 3)

Source: Codex, GW-EF interpolation scratch, run 3 (C1 closed), deposited by Turbo
(Muse, GPPDiscovery4) at GPP-bridge `MuseResearch/gwefinterp-scratch-2026-11-10.lean`,
commit `e399cf19`, SHA-256 `144f933f…6321` (70,341 bytes, 1,398 lines); verified by
Turbo on GPP-bridge PR #11 (issuecomment-6782134494). Ported into GPPVerify by
Heart of the Cosmos / Grok, superseding the conditional port of PR #553.
Credit: Daniel Toupin / Golden Physics Project, with AI assistance (Codex, Turbo, Grok).

Phase 1 (Vandermonde core, finite evaluation surjectivity, translated bump
interpolation, the weighted `ℓ²` carrier, density ⇔ annihilator), the Gaussian
C2 step (`coefficients_zero_of_gaussian_identity`) and C1 (the cutoff transform
bound uniform in the cutoff index, `GppGwefC1.gaussian_cutoff_uniform_bound`,
and the passage to the Gaussian identity, `StripData.gaussian_identity`) are
proved, so `gaussian_annihilator` holds under its original hypotheses.

Port changes (only these): this header replaces the scratch header, and the
trailing `#print axioms` block is dropped (CI runs its own axiom gate). All other
declarations are byte-identical to the deposit. The PR #553 hypothesis
`StripData.GaussianIdentityC1` and stub `open_gaussian_identity_c1` are removed.

The Hilbert carrier uses coordinates `sqrt(m(rho)) * Psi(f)(rho)`, so its norm
is exactly the weighted square sum. Density is relative to the real subspace
`v(conj rho) = conj(v rho)`, not the whole complex Hilbert space.

Honest boundary: this is the interpolation (density) link of the GW-EF chain.
It does not prove ARP, and RH remains OPEN.
-/

open Complex MeasureTheory Filter
open GppMeyerSpectralWeil GppWeilCriterion GppExplicitFormulaE1
open scoped ContDiff lp ComplexConjugate Topology

noncomputable section
set_option maxHeartbeats 800000
namespace GppGwefC1

def transform (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((z - 1 / 2) * u)

theorem transform_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (z : ℂ) :
    transform (deriv g) z = -(z - 1 / 2) * transform g z := by
  have hd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.1 hg).2
  let e : ℝ → ℂ := fun u => Complex.exp ((z - 1 / 2) * u)
  let e' : ℝ → ℂ := fun u => (z - 1 / 2) * e u
  have he : ∀ u, HasDerivAt e (e' u) u := by
    intro u
    convert ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (z - 1 / 2)).cexp using 1 <;>
      dsimp [e, e'] <;> ring
  have hc : Continuous e := by dsimp [e]; fun_prop
  have hi : Integrable (e * deriv g) :=
    (hc.mul hd.continuous).integrable_of_hasCompactSupport hgc.deriv.mul_left
  have hi' : Integrable (e' * g) :=
    ((continuous_const.mul hc).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi₀ : Integrable (e * g) :=
    (hc.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun u _ => he u) (fun u _ => (hg.differentiable (by simp) u).hasDerivAt) hi hi' hi₀
  have h₁ : transform (deriv g) z = ∫ u, e u * deriv g u := by
    unfold transform
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => mul_comm _ _)
  rw [h₁, h]
  dsimp only [Pi.mul_apply, e', e]
  rw [show (fun u : ℝ => (z - 1 / 2) * Complex.exp ((z - 1 / 2) * u) * g u) =
    (fun u : ℝ => (z - 1 / 2) * (g u * Complex.exp ((z - 1 / 2) * u))) by
    funext u; ring, integral_const_mul]
  simp only [transform, neg_mul]

theorem transform_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (n : ℕ) (z : ℂ) :
    transform (iteratedDeriv n g) z = (-(z - 1 / 2)) ^ n * transform g z := by
  rw [iteratedDeriv_eq_iterate]
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply,
      ih (contDiff_infty_iff_deriv.1 hg).2 hgc.deriv, transform_deriv hg hgc, pow_succ]
    ring

theorem norm_transform_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {z : ℂ} (h₀ : 0 ≤ z.re) (h₁ : z.re ≤ 1) :
    ‖transform g z‖ ≤ ∫ u : ℝ, ‖g u‖ * Real.exp (|u| / 2) := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _))
    ((by fun_prop : Continuous (fun u => ‖g u‖ * Real.exp (|u| / 2))).integrable_of_hasCompactSupport
      hgc.norm.mul_right)
  apply Eventually.of_forall
  intro u
  simp only [norm_mul, Complex.norm_exp]
  gcongr
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.div_ofNat_re, Complex.one_re]
  have hb : |z.re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc (z.re - 1 / 2) * u ≤ |(z.re - 1 / 2) * u| := le_abs_self _
    _ = |z.re - 1 / 2| * |u| := abs_mul _ _
    _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := by ring

theorem norm_iteratedDeriv_cutoff_le (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (M : ℕ → ℝ) (_hM₀ : ∀ j, 0 ≤ M j) (hM : ∀ j u, ‖iteratedDeriv j χ u‖ ≤ M j)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (j : ℕ) (u : ℝ) :
    ‖iteratedDeriv j (fun x => χ (t * x)) u‖ ≤ M j := by
  rw [iteratedDeriv_comp_const_smul (n := j) (hχ.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))) t]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg ht₀]
  calc t ^ j * ‖iteratedDeriv j χ (t * u)‖ ≤ 1 * M j :=
    mul_le_mul (pow_le_one₀ ht₀ ht₁) (hM _ _) (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem cutoff_derivative_bound (g χ : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hχ : ContDiff ℝ ∞ χ)
    (M : ℕ → ℝ) (hM₀ : ∀ j, 0 ≤ M j) (hM : ∀ j u, ‖iteratedDeriv j χ u‖ ≤ M j)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (fun x => g x * χ (t * x)) u‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ‖iteratedDeriv j g u‖ * M (n - j) := by
  have hχt : ContDiff ℝ ∞ (fun x => χ (t * x)) :=
    hχ.comp (contDiff_const.mul contDiff_id)
  rw [iteratedDeriv_fun_mul (n := n) (hg.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hχt.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  simp only [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedDeriv_cutoff_le χ hχ M hM₀ hM t ht₀ ht₁ _ _) (by positivity)

theorem smooth_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.1 ih).2

theorem compact_iteratedDeriv {g : ℝ → ℂ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem exists_cutoff_constants {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ j u, ‖iteratedDeriv j χ u‖ ≤ M j := by
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖iteratedDeriv j χ u‖ ≤ C := by
    obtain ⟨C, hC⟩ := (smooth_iteratedDeriv hχ j).continuous.bounded_above_of_compact_support
      (compact_iteratedDeriv hχc j)
    exact ⟨max C 0, le_max_right _ _, fun u => (hC u).trans (le_max_left _ _)⟩
  choose M hM₀ hM using hb
  exact ⟨M, hM₀, hM⟩

/-- A single derivative L1 bound for every scale t in (0,1]. -/
theorem cutoff_integral_bound (g χ : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hL : ∀ j : ℕ, Integrable (fun u => ‖iteratedDeriv j g u‖ * Real.exp (|u| / 2)))
    (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫ u : ℝ, ‖iteratedDeriv n (fun x => g x * χ (t * x)) u‖ * Real.exp (|u| / 2) ≤ B := by
  obtain ⟨M, hM₀, hM⟩ := exists_cutoff_constants hχ hχc
  let H : ℝ → ℝ := fun u => ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℝ) * ‖iteratedDeriv j g u‖ * M (n - j) * Real.exp (|u| / 2)
  have hH : Integrable H := by
    apply integrable_finsetSum
    intro j hj
    exact (((hL j).const_mul (n.choose j : ℝ)).mul_const (M (n - j))).congr
      (Eventually.of_forall fun u => by dsimp; ring)
  have hH₀ : ∀ u, 0 ≤ H u := by
    intro u
    apply Finset.sum_nonneg
    intro j hj
    have := hM₀ (n - j)
    positivity
  refine ⟨∫ u, H u, integral_nonneg hH₀, fun t ht ht₁ => ?_⟩
  apply integral_mono_of_nonneg (Eventually.of_forall (fun u => by positivity)) hH
  apply Eventually.of_forall
  intro u
  dsimp [H]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (cutoff_derivative_bound g χ hg hχ M hM₀ hM t ht.le ht₁ n u) (Real.exp_pos _).le

/-- Uniform strip decay for all cutoffs, provided the original function has
integrable exponentially weighted derivatives. B is chosen before t or z. -/
theorem uniform_cutoff_bound (g χ : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hL : ∀ j : ℕ, Integrable (fun u => ‖iteratedDeriv j g u‖ * Real.exp (|u| / 2)))
    (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
        (1 + ‖z‖) ^ N * ‖transform (fun x => g x * χ (t * x)) z‖ ≤ C := by
  obtain ⟨B₀, hB₀, hb₀⟩ := cutoff_integral_bound g χ hg hχ hχc hL 0
  obtain ⟨Bₙ, hBₙ, hbₙ⟩ := cutoff_integral_bound g χ hg hχ hχc hL N
  refine ⟨3 ^ N * (B₀ + Bₙ), by positivity, fun t ht ht₁ z hz₀ hz₁ => ?_⟩
  let f : ℝ → ℂ := fun x => g x * χ (t * x)
  have hf : ContDiff ℝ ∞ f := hg.mul (hχ.comp (contDiff_const.mul contDiff_id))
  have hfc : HasCompactSupport f :=
    (hχc.comp_homeomorph (Homeomorph.mulLeft₀ t ht.ne')).mul_left
  have hb0 : ‖transform f z‖ ≤ B₀ :=
    (norm_transform_le hf hfc hz₀ hz₁).trans (by simpa only [iteratedDeriv_zero] using hb₀ t ht ht₁)
  have hbn : ‖z - 1 / 2‖ ^ N * ‖transform f z‖ ≤ Bₙ := by
    have h := (norm_transform_le (smooth_iteratedDeriv hf N)
      (compact_iteratedDeriv hfc N) hz₀ hz₁).trans (hbₙ t ht ht₁)
    rwa [transform_iteratedDeriv hf hfc, norm_mul, norm_pow, norm_neg] at h
  have htri : ‖z‖ ≤ ‖z - 1 / 2‖ + 1 / 2 := by
    calc ‖z‖ = ‖(z - 1 / 2) + (1 / 2 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ = _ := by norm_num
  change (1 + ‖z‖) ^ N * ‖transform f z‖ ≤ _
  by_cases hsmall : ‖z - 1 / 2‖ ≤ 1
  · have hp : (1 + ‖z‖) ^ N ≤ (3 : ℝ) ^ N := by gcongr; linarith
    exact mul_le_mul hp (hb0.trans (by linarith)) (norm_nonneg _) (by positivity)
  · have hp : (1 + ‖z‖) ^ N ≤ (3 * ‖z - 1 / 2‖) ^ N := by gcongr; linarith
    calc (1 + ‖z‖) ^ N * ‖transform f z‖ ≤
        (3 * ‖z - 1 / 2‖) ^ N * ‖transform f z‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 3 ^ N * (‖z - 1 / 2‖ ^ N * ‖transform f z‖) := by rw [mul_pow]; ring
      _ ≤ 3 ^ N * Bₙ := mul_le_mul_of_nonneg_left hbn (by positivity)
      _ ≤ _ := by gcongr; linarith

def packet (q : ℝ) (v : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(q : ℂ) * (u : ℂ) ^ 2 + v * u)

theorem packet_smooth (q : ℝ) (v : ℂ) : ContDiff ℝ ∞ (packet q v) := by
  unfold packet
  have hc : ContDiff ℝ ∞ (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((contDiff_const.mul (hc.pow 2)).add (contDiff_const.mul hc)).cexp

theorem packet_norm (q : ℝ) (v : ℂ) (u : ℝ) :
    ‖packet q v u‖ = Real.exp (-q * u ^ 2 + v.re * u) := by
  simp [packet, Complex.norm_exp, Complex.mul_re, Complex.mul_im, pow_two]

theorem integrable_abs_pow_gaussian (n : ℕ) {q : ℝ} (hq : 0 < q) :
    Integrable (fun u : ℝ => |u| ^ n * Real.exp (-q * u ^ 2)) := by
  simpa [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)] using
    (integrable_rpow_mul_exp_neg_mul_sq hq (s := (n : ℝ)) (by
      have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm

theorem packet_weight_le {q : ℝ} (hq : 0 < q) (v : ℂ) (u : ℝ) :
    ‖packet q v u‖ * Real.exp (|u| / 2) ≤
      Real.exp ((|v.re| + 1 / 2) ^ 2 / (2 * q)) * Real.exp (-(q / 2) * u ^ 2) := by
  rw [packet_norm, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlin : v.re * u ≤ |v.re| * |u| := (le_abs_self _).trans_eq (abs_mul _ _)
  have hquad : 0 ≤ (q / 2) * u ^ 2 + (|v.re| + 1 / 2) ^ 2 / (2 * q) -
      (|v.re| + 1 / 2) * |u| := by
    have heq : (q / 2) * u ^ 2 + (|v.re| + 1 / 2) ^ 2 / (2 * q) -
        (|v.re| + 1 / 2) * |u| = (q * |u| - (|v.re| + 1 / 2)) ^ 2 / (2 * q) := by
      rw [← sq_abs u]
      field_simp
      ring
    rw [heq]
    positivity
  linarith

theorem packet_monomial_integrable {q : ℝ} (hq : 0 < q) (v : ℂ) (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n * (‖packet q v u‖ * Real.exp (|u| / 2))) := by
  apply ((integrable_abs_pow_gaussian n (show 0 < q / 2 by positivity)).const_mul
    (Real.exp ((|v.re| + 1 / 2) ^ 2 / (2 * q)))).mono'
    (((continuous_abs.pow n).mul ((packet_smooth q v).continuous.norm.mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2)))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro u
  dsimp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ |u| ^ n * (Real.exp ((|v.re| + 1 / 2) ^ 2 / (2 * q)) *
        Real.exp (-(q / 2) * u ^ 2)) :=
      mul_le_mul_of_nonneg_left (packet_weight_le hq v u) (by positivity)
    _ = _ := by ring

theorem packet_polynomial_integrable {q : ℝ} (hq : 0 < q) (v : ℂ) (P : Polynomial ℂ) :
    Integrable (fun u : ℝ => ‖P.eval (u : ℂ) * packet q v u‖ * Real.exp (|u| / 2)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    apply (hP.add hQ).mono'
      ((((P + Q).continuous.comp Complex.continuous_ofReal).mul (packet_smooth q v).continuous).norm.mul
        (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
    apply Eventually.of_forall
    intro u
    dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Polynomial.eval_add, add_mul]
    calc _ ≤ (‖P.eval (u : ℂ) * packet q v u‖ +
        ‖Q.eval (u : ℂ) * packet q v u‖) * Real.exp (|u| / 2) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
      _ = _ := by ring
  | monomial n a =>
    convert (packet_monomial_integrable hq v n).const_mul ‖a‖ using 1
    funext u
    simp only [Polynomial.eval_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    ring

theorem packet_deriv (q : ℝ) (v : ℂ) (P : Polynomial ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => P.eval (x : ℂ) * packet q v x)
      ((P.derivative + P * (Polynomial.C v - Polynomial.C (2 * (q : ℂ)) * Polynomial.X)).eval
        (u : ℂ) * packet q v u) u := by
  have he : HasDerivAt (packet q v) ((-2 * (q : ℂ) * u + v) * packet q v u) u := by
    unfold packet
    convert (((Complex.ofRealCLM.hasDerivAt (x := u)).pow 2).const_mul (-(q : ℂ)) |>.add
      ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul v)).cexp using 1 <;>
      simp only [Pi.add_apply, Pi.pow_apply, Complex.ofRealCLM_apply, Complex.ofReal_one] <;> ring
  have hP : (P.derivative + P * (Polynomial.C v - Polynomial.C (2 * (q : ℂ)) * Polynomial.X)).eval
      (u : ℂ) * packet q v u =
      P.derivative.eval (u : ℂ) * packet q v u +
        P.eval (u : ℂ) * ((-2 * (q : ℂ) * u + v) * packet q v u) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [hP]
  exact ((P.hasDerivAt (u : ℂ)).comp_ofReal).mul he

theorem packet_derivative_polynomial (q : ℝ) (v : ℂ) (n : ℕ) :
    ∃ P : Polynomial ℂ, iteratedDeriv n (packet q v) =
      fun u : ℝ => P.eval (u : ℂ) * packet q v u := by
  induction n with
  | zero => exact ⟨1, by ext u; simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.derivative + P * (Polynomial.C v - Polynomial.C (2 * (q : ℂ)) * Polynomial.X), ?_⟩
    rw [iteratedDeriv_succ, hP]
    funext u
    exact (packet_deriv q v P u).deriv

theorem packet_weighted_derivatives {q : ℝ} (hq : 0 < q) (v : ℂ) (n : ℕ) :
    Integrable (fun u : ℝ => ‖iteratedDeriv n (packet q v) u‖ * Real.exp (|u| / 2)) := by
  obtain ⟨P, hP⟩ := packet_derivative_polynomial q v n
  rw [hP]
  exact packet_polynomial_integrable hq v P

def scale (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

theorem scale_pos (k : ℕ) : 0 < scale k := by dsimp [scale]; positivity

theorem scale_le_one (k : ℕ) : scale k ≤ 1 := by
  dsimp [scale]
  exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem transform_cutoff_tendsto (g χ : ℝ → ℂ)
    (hg : Continuous g) (hχ : Continuous χ) (hχ₀ : χ 0 = 1)
    (M : ℝ) (hM : ∀ u, ‖χ u‖ ≤ M)
    (hL : Integrable (fun u => ‖g u‖ * Real.exp (|u| / 2)))
    (z : ℂ) (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1) :
    Tendsto (fun k : ℕ => transform (fun u => g u * χ (scale k * u)) z)
      atTop (𝓝 (transform g z)) := by
  have hnorm (u : ℝ) : ‖Complex.exp ((z - 1 / 2) * u)‖ ≤ Real.exp (|u| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re]
    have hb : |z.re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc (z.re - 1 / 2) * u ≤ |(z.re - 1 / 2) * u| := le_abs_self _
      _ = |z.re - 1 / 2| * |u| := abs_mul _ _
      _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = _ := by ring
  apply tendsto_integral_of_dominated_convergence (fun u => M * (‖g u‖ * Real.exp (|u| / 2)))
  · intro k
    exact ((hg.mul (hχ.comp (continuous_const.mul continuous_id))).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  · exact hL.const_mul M
  · intro k
    apply Eventually.of_forall
    intro u
    simp only [norm_mul]
    calc ‖g u‖ * ‖χ (scale k * u)‖ * ‖Complex.exp ((z - 1 / 2) * u)‖ ≤
        ‖g u‖ * M * Real.exp (|u| / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
            (hnorm u) (norm_nonneg _) (by have := (norm_nonneg (χ 0)).trans (hM 0); positivity)
      _ = _ := by ring
  · apply Eventually.of_forall
    intro u
    have ht : Tendsto (fun k : ℕ => χ (scale k * u)) atTop (𝓝 1) := by
      have := hχ.continuousAt.tendsto.comp (scale_tendsto.mul_const u)
      simpa only [Function.comp_def, zero_mul, hχ₀] using this
    simpa using (tendsto_const_nhds.mul ht).mul tendsto_const_nhds

theorem packet_transform {q : ℝ} (hq : 0 < q) (v z : ℂ) :
    transform (packet q v) z = (Real.pi / (q : ℂ)) ^ (1 / 2 : ℂ) *
      Complex.exp ((v + z - 1 / 2) ^ 2 / (4 * (q : ℂ))) := by
  have hb : (-(q : ℂ)).re < 0 := by simpa using neg_neg_of_pos hq
  calc transform (packet q v) z =
      ∫ u : ℝ, Complex.exp (-(q : ℂ) * (u : ℂ) ^ 2 + (v + z - 1 / 2) * u + 0) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro u
        dsimp [packet]
        rw [← Complex.exp_add]
        congr 1
        ring
    _ = _ := by
      rw [integral_cexp_quadratic hb]
      congr 2
      · simp
      · ring

def χ (u : ℝ) : ℂ := ((default : ContDiffBump (0 : ℝ)) u : ℂ)

theorem χ_smooth : ContDiff ℝ ∞ χ :=
  Complex.ofRealCLM.contDiff.comp (default : ContDiffBump (0 : ℝ)).contDiff

theorem χ_compact : HasCompactSupport χ :=
  (default : ContDiffBump (0 : ℝ)).hasCompactSupport.comp_left Complex.ofReal_zero

theorem χ_zero : χ 0 = 1 := by
  have h := (default : ContDiffBump (0 : ℝ)).one_of_mem_closedBall
    (Metric.mem_closedBall_self (default : ContDiffBump (0 : ℝ)).rIn_pos.le)
  simp only [χ, h, Complex.ofReal_one]

theorem χ_norm (u : ℝ) : ‖χ u‖ ≤ 1 := by
  rw [χ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (default : ContDiffBump (0 : ℝ)).nonneg]
  exact (default : ContDiffBump (0 : ℝ)).le_one

def cutoff (q : ℝ) (v : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  packet q v u * χ (scale k * u)

theorem cutoff_smooth (q : ℝ) (v : ℂ) (k : ℕ) : ContDiff ℝ ∞ (cutoff q v k) :=
  (packet_smooth q v).mul (χ_smooth.comp (contDiff_const.mul contDiff_id))

theorem cutoff_compact (q : ℝ) (v : ℂ) (k : ℕ) : HasCompactSupport (cutoff q v k) :=
  (χ_compact.comp_homeomorph (Homeomorph.mulLeft₀ (scale k) (scale_pos k).ne')).mul_left

/-- The cutoff constant is independent of k, at every polynomial order N. -/
theorem gaussian_cutoff_uniform_bound {q : ℝ} (hq : 0 < q) (v : ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      (1 + ‖z‖) ^ N * ‖transform (cutoff q v k) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_cutoff_bound (packet q v) χ (packet_smooth q v)
    χ_smooth χ_compact (packet_weighted_derivatives hq v) N
  exact ⟨C, hC, fun k => hb (scale k) (scale_pos k) (scale_le_one k)⟩

theorem gaussian_cutoff_transform_tendsto {q : ℝ} (hq : 0 < q) (v z : ℂ)
    (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1) :
    Tendsto (fun k : ℕ => transform (cutoff q v k) z) atTop (𝓝 (transform (packet q v) z)) := by
  apply transform_cutoff_tendsto (packet q v) χ (packet_smooth q v).continuous χ_smooth.continuous
    χ_zero 1 χ_norm
    (by simpa only [iteratedDeriv_zero] using packet_weighted_derivatives hq v 0) z hz₀ hz₁

theorem gaussian_cutoff_series_tendsto (Z : Set ℂ) (m : ℂ → ℕ)
    (hcount : ∃ N : ℕ, Summable (fun z : Z =>
      (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1)
    (c : Z → ℂ) (A : ℝ) (hA : 0 ≤ A) (hc : ∀ z : Z, ‖c z‖ ≤ A * (m z : ℝ))
    {q : ℝ} (hq : 0 < q) (v : ℂ) :
    Tendsto (fun k : ℕ => ∑' z : Z, c z * transform (cutoff q v k) z) atTop
      (𝓝 (∑' z : Z, c z * transform (packet q v) z)) := by
  obtain ⟨N, hN⟩ := hcount
  obtain ⟨C, hC, hbound⟩ := gaussian_cutoff_uniform_bound hq v N
  apply tendsto_tsum_of_dominated_convergence (hN.mul_left (A * C))
  · intro z
    exact tendsto_const_nhds.mul
      (gaussian_cutoff_transform_tendsto hq v z (hstrip z z.property).1.le (hstrip z z.property).2.le)
  · apply Eventually.of_forall
    intro k z
    rw [norm_mul]
    have hp : 0 < (1 + ‖(z : ℂ)‖) ^ N := by positivity
    have hB : ‖transform (cutoff q v k) z‖ ≤ C * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp]
      simpa only [mul_comm] using hbound k z (hstrip z z.property).1.le (hstrip z z.property).2.le
    calc ‖c z‖ * ‖transform (cutoff q v k) z‖ ≤
        (A * (m z : ℝ)) * (C * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹) :=
          mul_le_mul (hc z) hB (norm_nonneg _) (by positivity)
      _ = _ := by ring

end GppGwefC1

namespace GppGwefGaussian

def score (a b : ℝ) (z : ℂ) : ℝ :=
  (z.re - 1 / 2 + b) ^ 2 - (z.im - a) ^ 2

theorem exists_outside_countable {A : Set ℝ} (hA : A.Countable) : ∃ x, x ∉ A := by
  by_contra h
  have hU : A = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  exact Set.not_countable_univ (hU ▸ hA)

/-- Two explicit countable sets of forbidden real parameters suffice to break
all ties. No genericity premise is assumed. -/
theorem exists_score_injective (Z : Set ℂ) [Countable Z] :
    ∃ a b : ℝ, Function.Injective (fun z : Z => score a b z) := by
  let badB : Z × Z → ℝ := fun p => -((p.1 : ℂ).re + (p.2 : ℂ).re - 1) / 2
  obtain ⟨b, hb⟩ := exists_outside_countable (Set.countable_range badB)
  let badA : Z × Z → ℝ := fun p =>
    -(((p.1 : ℂ).re - 1 / 2 + b) ^ 2 - ((p.2 : ℂ).re - 1 / 2 + b) ^ 2 -
      (p.1 : ℂ).im ^ 2 + (p.2 : ℂ).im ^ 2) /
      (2 * ((p.1 : ℂ).im - (p.2 : ℂ).im))
  obtain ⟨a, ha⟩ := exists_outside_countable (Set.countable_range badA)
  refine ⟨a, b, fun p q hpq => ?_⟩
  change score a b (p : ℂ) = score a b (q : ℂ) at hpq
  unfold score at hpq
  by_cases hi : (p : ℂ).im = (q : ℂ).im
  · have hr : (p : ℂ).re = (q : ℂ).re := by
      by_contra hne
      apply hb
      refine ⟨(p, q), ?_⟩
      dsimp [badB]
      have hfactor : ((p : ℂ).re - (q : ℂ).re) *
          ((p : ℂ).re + (q : ℂ).re - 1 + 2 * b) = 0 := by
        rw [hi] at hpq
        nlinarith
      have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
      linarith
    exact Subtype.ext (Complex.ext hr hi)
  · exfalso
    apply ha
    refine ⟨(p, q), ?_⟩
    dsimp [badA]
    apply (div_eq_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hi))).2
    nlinarith

/-- In a vertical strip, every score superlevel set is contained in an
explicit bounded ball, so local finiteness supplies a finite maximum search. -/
theorem finite_score_superlevel (Z : Set ℂ)
    (hloc : ∀ R : ℝ, {z ∈ Z | ‖z‖ ≤ R}.Finite)
    (hstrip : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1) (a b L : ℝ) :
    {z ∈ Z | L ≤ score a b z}.Finite := by
  refine (hloc (1 + ((|b| + 1) ^ 2 + |L| + 1) + |a|)).subset ?_
  rintro z ⟨hz, hL⟩
  refine ⟨hz, ?_⟩
  obtain ⟨hr0, hr1⟩ := hstrip z hz
  have hreal : |z.re| ≤ 1 := by rw [abs_of_pos hr0]; exact hr1.le
  have hdelta : |z.re - 1 / 2 + b| ≤ |b| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self b, neg_abs_le b]
  have hdelta2 : (z.re - 1 / 2 + b) ^ 2 ≤ (|b| + 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdelta 2
  have him : |z.im - a| ≤ (|b| + 1) ^ 2 + |L| + 1 := by
    unfold score at hL
    nlinarith [sq_nonneg (|z.im - a| - 1), sq_abs (z.im - a), neg_abs_le L]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + (|z.im - a| + |a|) :=
      add_le_add hreal (by simpa using (abs_sub_le z.im a 0))
    _ ≤ _ := by linarith

/-- A nonempty coefficient support has a unique score maximizer for the
explicitly constructed parameters. The maximum is taken in a finite superlevel. -/
theorem exists_unique_maximizer (Z : Set ℂ) [Countable Z]
    (hloc : ∀ R : ℝ, {z ∈ Z | ‖z‖ ≤ R}.Finite)
    (hstrip : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1)
    (c : Z → ℂ) (hc : ∃ z, c z ≠ 0) :
    ∃ a b : ℝ, ∃ z₀ : Z, c z₀ ≠ 0 ∧
      ∀ z : Z, c z ≠ 0 → z ≠ z₀ → score a b z < score a b z₀ := by
  classical
  obtain ⟨a, b, hinj⟩ := exists_score_injective Z
  obtain ⟨p, hp⟩ := hc
  let F : Set Z := {z | c z ≠ 0 ∧ score a b p ≤ score a b z}
  have hfinite : F.Finite := by
    have h := Set.Finite.preimage (f := fun z : Z => (z : ℂ))
      Subtype.val_injective.injOn (finite_score_superlevel Z hloc hstrip a b (score a b p))
    exact h.subset (fun z hz => ⟨z.property, hz.2⟩)
  obtain ⟨z₀, hz₀, hmax⟩ := Set.exists_max_image F
    (fun z : Z => score a b z) hfinite ⟨p, hp, le_rfl⟩
  refine ⟨a, b, z₀, hz₀.1, fun z hz hne => ?_⟩
  have hle : score a b z ≤ score a b z₀ := by
    by_cases h : score a b p ≤ score a b z
    · exact hmax z ⟨hz, h⟩
    · exact (le_of_not_ge h).trans hz₀.2
  exact lt_of_le_of_ne hle (fun h => hne (hinj h))

/-- Once the Gaussian envelope is summable, the normalized off-maximum sum
vanishes. Tannery's theorem implements the finite-sum / summable-tail split. -/
theorem normalized_tail_tendsto {ι : Type*} (c z : ι → ℂ) (i₀ : ι)
    (hmax : ∀ i, c i ≠ 0 → i ≠ i₀ → (z i).re < (z i₀).re)
    (hsum : Summable (fun i => ‖c i‖ * Real.exp (z i).re)) :
    Tendsto (fun s : ℝ => ∑' i : {i : ι // i ≠ i₀},
      c i * Complex.exp ((s : ℂ) * (z i - z i₀))) atTop (𝓝 0) := by
  have hbound : Summable (fun i : {i : ι // i ≠ i₀} =>
      Real.exp (-(z i₀).re) * (‖c i‖ * Real.exp (z i).re)) :=
    (hsum.subtype _).mul_left _
  have h := tendsto_tsum_of_dominated_convergence hbound
    (𝓕 := atTop) (f := fun s : ℝ => fun i : {i : ι // i ≠ i₀} =>
      c i * Complex.exp ((s : ℂ) * (z i - z i₀)))
    (g := fun _ => (0 : ℂ)) ?_ ?_
  · simpa using h
  · intro i
    by_cases hc : c i = 0
    · simp only [hc, zero_mul]
      exact tendsto_const_nhds
    · have hneg : (z i - z i₀).re < 0 := by
        simpa only [Complex.sub_re, sub_neg] using hmax i hc i.property
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      simpa only [mul_zero, Function.comp_def, id_eq] using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp
        (tendsto_id.atTop_mul_const_of_neg hneg))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs i
    by_cases hc : c i = 0
    · simp [hc]
    · have hgap : (z i).re - (z i₀).re < 0 := by
        exact sub_neg.mpr (hmax i hc i.property)
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
      calc ‖c i‖ * Real.exp (s * ((z i).re - (z i₀).re))
          ≤ ‖c i‖ * Real.exp ((z i).re - (z i₀).re) := by
            gcongr
            nlinarith
        _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring

/-- An elementary factorial bound, with no asymptotic hypothesis. -/
theorem polynomial_gaussian_bound (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-(r ^ 2 / 4)) ≤
      4 ^ N * (N.factorial : ℝ) * Real.exp 1 := by
  have harg : 1 + r ≤ 4 * (1 + r ^ 2 / 4) := by nlinarith [sq_nonneg (r - 1)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + r) harg N
  have hf : (1 + r ^ 2 / 4) ^ N ≤ Real.exp (1 + r ^ 2 / 4) * (N.factorial : ℝ) :=
    (div_le_iff₀ (by positivity)).mp
      (Real.pow_div_factorial_le_exp (1 + r ^ 2 / 4) (by positivity) N)
  calc (1 + r) ^ N * Real.exp (-(r ^ 2 / 4))
      ≤ (4 * (1 + r ^ 2 / 4)) ^ N * Real.exp (-(r ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 4 ^ N * ((1 + r ^ 2 / 4) ^ N * Real.exp (-(r ^ 2 / 4))) := by rw [mul_pow]; ring
    _ ≤ 4 ^ N * ((Real.exp (1 + r ^ 2 / 4) * N.factorial) *
        Real.exp (-(r ^ 2 / 4))) := by gcongr
    _ = _ := by
      calc _ = 4 ^ N * (N.factorial : ℝ) *
          (Real.exp (1 + r ^ 2 / 4) * Real.exp (-(r ^ 2 / 4))) := by ring
        _ = _ := by rw [← Real.exp_add]; ring_nf

/-- The strip Gaussian beats the exact polynomial weight appearing in (P). -/
theorem score_polynomial_bound (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → z.re < 1 →
      (1 + ‖z‖) ^ N * Real.exp (score a b z / 2) ≤ C := by
  let K : ℝ := (|b| + 1) ^ 2 + a ^ 2 + 1
  refine ⟨Real.exp (K / 2) * (4 ^ N * N.factorial * Real.exp 1), by positivity,
    fun z hr0 hr1 => ?_⟩
  have hdelta : |z.re - 1 / 2 + b| ≤ |b| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self b, neg_abs_le b]
  have hd2 : (z.re - 1 / 2 + b) ^ 2 ≤ (|b| + 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdelta 2
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hs : score a b z / 2 ≤ K / 2 - ‖z‖ ^ 2 / 4 := by
    dsimp [score, K]
    nlinarith [sq_nonneg (z.im - 2 * a), mul_nonneg hr0.le (show 0 ≤ 1 - z.re by linarith)]
  calc (1 + ‖z‖) ^ N * Real.exp (score a b z / 2)
      ≤ (1 + ‖z‖) ^ N * Real.exp (K / 2 - ‖z‖ ^ 2 / 4) := by gcongr
    _ = Real.exp (K / 2) * ((1 + ‖z‖) ^ N * Real.exp (-(‖z‖ ^ 2 / 4))) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_gaussian_bound N ‖z‖ (norm_nonneg _))
      (Real.exp_pos _).le

/-- Polynomial counting pays for the Gaussian envelope used in the tail limit. -/
theorem coefficient_envelope_summable (Z : Set ℂ) (m : ℂ → ℕ)
    (hcount : ∃ N : ℕ, Summable (fun z : Z =>
      (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1)
    (c : Z → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ z : Z, ‖c z‖ ≤ A * (m z : ℝ)) (a b : ℝ) :
    Summable (fun z : Z => ‖c z‖ * Real.exp (score a b z / 2)) := by
  obtain ⟨N, hN⟩ := hcount
  obtain ⟨C, hC, hbound⟩ := score_polynomial_bound a b N
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hN.mul_left (A * C))
  intro z
  have hp : 0 < (1 + ‖(z : ℂ)‖) ^ N := by positivity
  have he : Real.exp (score a b z / 2) ≤ C * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    simpa [mul_comm] using hbound z (hstrip z z.property).1 (hstrip z z.property).2
  calc ‖c z‖ * Real.exp (score a b z / 2)
      ≤ (A * (m z : ℝ)) * (C * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹) :=
        mul_le_mul (hc z) he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem countable_of_counting (Z : Set ℂ) (m : ℂ → ℕ)
    (hm : ∀ z ∈ Z, 1 ≤ m z)
    (hcount : ∃ N : ℕ, Summable (fun z : Z =>
      (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹)) : Countable Z := by
  obtain ⟨N, hN⟩ := hcount
  have hsupport : Function.support (fun z : Z =>
      (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    change (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹ ≠ 0
    have hmpos : (0 : ℝ) < m z := by exact_mod_cast (hm z z.property)
    exact (mul_pos hmpos (by positivity)).ne'
  exact Set.countable_univ_iff.mp (hsupport ▸ hN.countable_support)

/-- Gaussian exponent for theta = a + i b, including the factor 1/2. -/
def exponent (a b : ℝ) (z : ℂ) : ℂ :=
  (z - 1 / 2 - Complex.I * ((a : ℂ) + Complex.I * b)) ^ 2 / 2

theorem exponent_re (a b : ℝ) (z : ℂ) : (exponent a b z).re = score a b z / 2 := by
  simp [exponent, score, pow_two, Complex.mul_re, Complex.mul_im]

/-- The dominant coefficient must vanish if the Gaussian sum vanishes. -/
theorem dominant_coefficient_zero {ι : Type*} (c z : ι → ℂ) (i₀ : ι)
    (hmax : ∀ i, c i ≠ 0 → i ≠ i₀ → (z i).re < (z i₀).re)
    (hsum : Summable (fun i => ‖c i‖ * Real.exp (z i).re))
    (hid : ∀ s : ℝ, 0 < s → ∑' i, c i * Complex.exp ((s : ℂ) * z i) = 0) :
    c i₀ = 0 := by
  classical
  have htail := normalized_tail_tendsto c z i₀ hmax hsum
  have hevent : ∀ᶠ s : ℝ in atTop,
      (∑' i : {i : ι // i ≠ i₀}, c i * Complex.exp ((s : ℂ) * (z i - z i₀))) = -c i₀ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hsummable : Summable (fun i => c i * Complex.exp ((s : ℂ) * (z i - z i₀))) := by
      apply (hsum.mul_left (Real.exp (-(z i₀).re))).of_norm_bounded
      intro i
      by_cases hc : c i = 0
      · simp [hc]
      · have hgap : (z i).re - (z i₀).re ≤ 0 := by
          by_cases hi : i = i₀
          · simp [hi]
          · exact (sub_neg.mpr (hmax i hc hi)).le
        simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
        calc ‖c i‖ * Real.exp (s * ((z i).re - (z i₀).re))
            ≤ ‖c i‖ * Real.exp ((z i).re - (z i₀).re) := by gcongr; nlinarith
          _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring
    have hzero : (∑' i, c i * Complex.exp ((s : ℂ) * (z i - z i₀))) = 0 := by
      have heq (i : ι) : c i * Complex.exp ((s : ℂ) * (z i - z i₀)) =
          (c i * Complex.exp ((s : ℂ) * z i)) * Complex.exp (-((s : ℂ) * z i₀)) := by
        rw [mul_sub, Complex.exp_sub, Complex.exp_neg]
        ring
      simp_rw [heq]
      rw [tsum_mul_right, hid s (lt_of_lt_of_le zero_lt_one hs), zero_mul]
    have hsplit := hsummable.sum_add_tsum_compl (s := {i₀})
    have hsets : ((↑({i₀} : Finset ι) : Set ι)ᶜ) = {i : ι | i ≠ i₀} := by
      ext i
      simp
    rw [hsets] at hsplit
    simp only [Finset.sum_singleton, sub_self, mul_zero, Complex.exp_zero, mul_one,
      hzero] at hsplit
    exact eq_neg_of_add_eq_zero_right hsplit
  have hconst : Tendsto (fun s : ℝ => ∑' i : {i : ι // i ≠ i₀},
      c i * Complex.exp ((s : ℂ) * (z i - z i₀))) atTop (𝓝 (-c i₀)) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ hs => hs.symm)
  exact neg_eq_zero.mp (tendsto_nhds_unique htail hconst).symm

/-- C2, with the polynomial counting and local finiteness hypotheses discharged.
The Gaussian identity is the explicit C1 input, not a density assumption. -/
theorem coefficients_zero_of_gaussian_identity (Z : Set ℂ) (m : ℂ → ℕ)
    (hloc : ∀ R : ℝ, {z ∈ Z | ‖z‖ ≤ R}.Finite)
    (hm : ∀ z ∈ Z, 1 ≤ m z)
    (hcount : ∃ N : ℕ, Summable (fun z : Z =>
      (m z : ℝ) * ((1 + ‖(z : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1)
    (c : Z → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ z : Z, ‖c z‖ ≤ A * (m z : ℝ))
    (hid : ∀ a b s : ℝ, 0 < s →
      ∑' z : Z, c z * Complex.exp ((s : ℂ) * exponent a b z) = 0) :
    ∀ z : Z, c z = 0 := by
  have : Countable Z := countable_of_counting Z m hm hcount
  by_contra h
  push Not at h
  obtain ⟨a, b, z₀, hz₀, hmax⟩ := exists_unique_maximizer Z hloc hstrip c h
  have hsum := coefficient_envelope_summable Z m hcount hstrip c A hA hc a b
  have hzero := dominant_coefficient_zero c (fun z : Z => exponent a b z) z₀
    (by intro z hz hne; simpa only [exponent_re, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
      using hmax z hz hne)
    (by simpa only [exponent_re] using hsum) (hid a b)
  exact hz₀ hzero

end GppGwefGaussian

namespace GppGwefInterp

theorem vandermonde_surjective {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (v : Fin n → ℂ) :
    ∃ a : Fin n → ℂ, ∀ j, (∑ k : Fin n, z j ^ (k : ℕ) * a k) = v j := by
  have hunit : IsUnit (Matrix.vandermonde z) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hz))
  obtain ⟨a, ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hunit) v
  exact ⟨a, fun j => congrFun ha j⟩

/-- The generalized Vandermonde core, including the nonzero bump factors. -/
theorem weighted_vandermonde_surjective {n : ℕ} (z b : Fin n → ℂ)
    (hz : Function.Injective z) (hb : ∀ j, b j ≠ 0) (v : Fin n → ℂ) :
    ∃ a : Fin n → ℂ, ∀ j, b j * (∑ k : Fin n, z j ^ (k : ℕ) * a k) = v j := by
  obtain ⟨a, ha⟩ := vandermonde_surjective z hz (fun j => v j / b j)
  exact ⟨a, fun j => by rw [ha]; exact mul_div_cancel₀ (v j) (hb j)⟩

/-- Complexification is explicit; compact support and smoothness are real statements. -/
def complexTests : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | ContDiff ℝ ∞ g ∧ HasCompactSupport g}
  zero_mem' := ⟨contDiff_const, by change IsCompact (tsupport (0 : ℝ → ℂ)); simp⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' a g hg := ⟨hg.1.const_smul a, hg.2.smul_left⟩

instance : CoeFun complexTests (fun _ => ℝ → ℂ) := ⟨fun f => f.val⟩

def complexTransform (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * u)

theorem transform_integrable (g : complexTests) (s : ℂ) :
    Integrable (fun u : ℝ => g u * Complex.exp ((s - 1 / 2) * u)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ g.property.2.mul_right
  exact g.property.1.continuous.mul (by fun_prop)

def finiteEvaluation (S : Finset ℂ) : complexTests →ₗ[ℂ] (S → ℂ) where
  toFun g s := complexTransform g s
  map_add' g h := by
    ext s
    simp only [complexTransform, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (transform_integrable g s) (transform_integrable h s)
  map_smul' a g := by
    ext s
    simp only [complexTransform, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc, integral_const_mul]

/-- Finite complex interpolation, using the already proved independence-of-exponentials core. -/
theorem finiteEvaluation_surjective (S : Finset ℂ) :
    Function.Surjective (finiteEvaluation S) := by
  apply LinearMap.range_eq_top.1
  apply top_unique
  rw [← GppMellinInterpolation.span_spectralVectors_eq_top S]
  apply Submodule.span_le.2
  rintro w ⟨f, hf, rfl⟩
  refine ⟨⟨fun u => (f u : ℂ), ?_⟩, rfl⟩
  exact ⟨Complex.ofRealCLM.contDiff.comp hf.1, hf.2.comp_left Complex.ofReal_zero⟩

def translatedTest (g : complexTests) (t : ℝ) : complexTests :=
  ⟨fun u => g (u - t), g.property.1.comp (contDiff_id.sub contDiff_const),
    g.property.2.comp_homeomorph (Homeomorph.subRight t)⟩

theorem complexTransform_translate (g : complexTests) (t : ℝ) (s : ℂ) :
    complexTransform (translatedTest g t) s =
      Complex.exp ((s - 1 / 2) * t) * complexTransform g s := by
  unfold complexTransform
  have heq : (fun u : ℝ => translatedTest g t u * Complex.exp ((s - 1 / 2) * u)) =
      ((fun u : ℝ => Complex.exp ((s - 1 / 2) * t) *
        (g u * Complex.exp ((s - 1 / 2) * u))) ∘ (fun u : ℝ => u - t)) := by
    funext u
    dsimp [translatedTest]
    rw [← mul_assoc, mul_comm (Complex.exp _) (g _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq]
  dsimp only [Function.comp_def]
  rw [integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => Complex.exp ((s - 1 / 2) * t) *
      (g u * Complex.exp ((s - 1 / 2) * u))) t, integral_const_mul]

/-- Interpolation within a fixed finite family of translated smooth bumps.
The injective exponential nodes and nonzero bump values are the exact matrix
conditions; no tail cutoff parameter occurs in them. -/
theorem translated_bump_interpolation {n : ℕ} (s : Fin n → ℂ) (δ : ℝ)
    (hδ : Function.Injective (fun j => Complex.exp ((s j - 1 / 2) * δ)))
    (g : complexTests) (hg : ∀ j, complexTransform g (s j) ≠ 0) (v : Fin n → ℂ) :
    ∃ a : Fin n → ℂ, ∀ j,
      complexTransform (∑ k : Fin n, a k • translatedTest g ((k : ℕ) * δ)) (s j) = v j := by
  obtain ⟨a, ha⟩ := weighted_vandermonde_surjective _ _ hδ hg v
  refine ⟨a, fun j => ?_⟩
  have heval : complexTransform
      (∑ k : Fin n, a k • (translatedTest g ((k : ℕ) * δ) : ℝ → ℂ)) (s j) =
      ∑ k : Fin n, a k * complexTransform (translatedTest g ((k : ℕ) * δ)) (s j) := by
    simp only [complexTransform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro k _
      exact (transform_integrable (translatedTest g ((k : ℕ) * δ)) (s j)).const_mul (a k)
  rw [heval]
  simp only [complexTransform_translate]
  have hexp (k : Fin n) : Complex.exp ((s j - 1 / 2) * (((k : ℕ) : ℝ) * δ)) =
      Complex.exp ((s j - 1 / 2) * δ) ^ (k : ℕ) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  calc
    _ = complexTransform g (s j) *
        (∑ k : Fin n, Complex.exp ((s j - 1 / 2) * δ) ^ (k : ℕ) * a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Complex.ofReal_mul, hexp]
      ring
    _ = v j := ha j

/-- E1b in the polynomial weight convention used by the counting hypothesis. -/
theorem spectralTransform_polynomial_bound {f : ℝ → ℝ} (hf : IsTestFunction f) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      (1 + ‖s‖) ^ N * ‖spectralTransform f s‖ ≤ C := by
  obtain ⟨C₀, h₀⟩ := spectralTransform_decay_strip hf 0
  obtain ⟨Cₙ, hₙ⟩ := spectralTransform_decay_strip hf N
  refine ⟨3 ^ N * (|C₀| + |Cₙ|), by positivity, fun s hs₀ hs₁ => ?_⟩
  have htri : ‖s‖ ≤ ‖s - 1 / 2‖ + 1 / 2 := by
    calc ‖s‖ = ‖(s - 1 / 2) + (1 / 2 : ℂ)‖ := by congr 1; ring
         _ ≤ ‖s - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
         _ = _ := by norm_num
  by_cases hsmall : ‖s - 1 / 2‖ ≤ 1
  · have hp : (1 + ‖s‖) ^ N ≤ (3 : ℝ) ^ N := by gcongr; linarith
    have hb : ‖spectralTransform f s‖ ≤ |C₀| + |Cₙ| := by
      have := h₀ s hs₀ hs₁
      simp only [pow_zero, one_mul] at this
      linarith [le_abs_self C₀, abs_nonneg Cₙ]
    exact mul_le_mul hp hb (norm_nonneg _) (by positivity)
  · have hp : (1 + ‖s‖) ^ N ≤ (3 * ‖s - 1 / 2‖) ^ N := by gcongr; linarith
    calc (1 + ‖s‖) ^ N * ‖spectralTransform f s‖
        ≤ (3 * ‖s - 1 / 2‖) ^ N * ‖spectralTransform f s‖ :=
          mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 3 ^ N * (‖s - 1 / 2‖ ^ N * ‖spectralTransform f s‖) := by rw [mul_pow]; ring
      _ ≤ 3 ^ N * Cₙ := mul_le_mul_of_nonneg_left (hₙ s hs₀ hs₁) (by positivity)
      _ ≤ _ := by gcongr; linarith [le_abs_self Cₙ, abs_nonneg C₀]

def weightedValues (Z : Set ℂ) (m : ℂ → ℕ) (f : ℝ → ℝ) (ρ : Z) : ℂ :=
  (Real.sqrt (m ρ) : ℂ) * spectralTransform f ρ

theorem weightedValues_norm_sq (Z : Set ℂ) (m : ℂ → ℕ) (f : ℝ → ℝ) (ρ : Z) :
    ‖weightedValues Z m f ρ‖ ^ 2 = (m ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2 := by
  simp [weightedValues, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (m ρ))]

/-- The actual counting premise plus E1b suffices for square summability. -/
theorem weightedValues_memℓp (Z : Set ℂ) (m : ℂ → ℕ)
    (hcount : ∃ N : ℕ, Summable (fun ρ : Z =>
      (m ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    {f : ℝ → ℝ} (hf : IsTestFunction f) : Memℓp (weightedValues Z m f) 2 := by
  obtain ⟨N, hN⟩ := hcount
  obtain ⟨C, hC, hb⟩ := spectralTransform_polynomial_bound hf N
  apply (memℓp_gen_iff (p := 2) (by norm_num)).2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hN.mul_left (C ^ 2))
  intro ρ
  rw [weightedValues_norm_sq]
  have hp : 1 ≤ (1 + ‖(ρ : ℂ)‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg (ρ : ℂ)])
  have hp₀ : 0 < (1 + ‖(ρ : ℂ)‖) ^ N := lt_of_lt_of_le zero_lt_one hp
  have hb' := hb ρ (hstrip ρ ρ.property).1.le (hstrip ρ ρ.property).2.le
  have hy := norm_nonneg (spectralTransform f ρ)
  have hyC : ‖spectralTransform f ρ‖ ≤ C := by nlinarith
  have hsq : ‖spectralTransform f ρ‖ ^ 2 ≤ C ^ 2 * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp₀]
    nlinarith [mul_le_mul_of_nonneg_right hb' hy]
  calc (m ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2
      ≤ (m ρ : ℝ) * (C ^ 2 * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹) :=
        mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = _ := by ring

abbrev SpectralHilbert (Z : Set ℂ) := ℓ²(Z, ℂ)

def testFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsTestFunction f}
  zero_mem' := ⟨contDiff_const, by change IsCompact (tsupport (0 : ℝ → ℝ)); simp⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' a f hf := ⟨hf.1.const_smul a, hf.2.smul_left⟩

instance : CoeFun testFunctions (fun _ => ℝ → ℝ) := ⟨fun f => f.val⟩

def spectralMap (Z : Set ℂ) (m : ℂ → ℕ)
    (hcount : ∃ N : ℕ, Summable (fun ρ : Z =>
      (m ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹))
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (f : testFunctions) : SpectralHilbert Z :=
  ⟨weightedValues Z m f, weightedValues_memℓp Z m hcount hstrip f.property⟩

/-- Reindexing is an isometry of the actual infinite Hilbert space. -/
def reindex {ι : Type*} (e : ι ≃ ι) : ℓ²(ι, ℂ) →ₗᵢ[ℂ] ℓ²(ι, ℂ) where
  toFun v := ⟨fun i => v (e i), by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).2
    exact e.summable_iff.2 ((memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp v))⟩
  map_add' v w := by ext i; rfl
  map_smul' a v := by ext i; rfl
  norm_map' v := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    congr 1
    exact e.tsum_eq (fun i => ‖v i‖ ^ (2 : ENNReal).toReal)

def quadraticForm {ι : Type*} (e : ι ≃ ι) (v : ℓ²(ι, ℂ)) : ℂ :=
  inner ℂ (reindex e v) v

theorem quadraticForm_eq_tsum {ι : Type*} (e : ι ≃ ι) (v : ℓ²(ι, ℂ)) :
    quadraticForm e v = ∑' i, conj (v (e i)) * v i := by
  simp [quadraticForm, lp.inner_eq_tsum, reindex, RCLike.inner_apply, mul_comm]

theorem quadraticForm_summable {ι : Type*} (e : ι ≃ ι) (v : ℓ²(ι, ℂ)) :
    Summable (fun i => conj (v (e i)) * v i) := by
  simpa [reindex, RCLike.inner_apply, mul_comm] using
    lp.summable_inner (𝕜 := ℂ) (reindex e v) v

theorem quadraticForm_bound {ι : Type*} (e : ι ≃ ι) (v : ℓ²(ι, ℂ)) :
    ‖quadraticForm e v‖ ≤ ‖v‖ ^ 2 := by
  simpa [quadraticForm, pow_two] using norm_inner_le_norm (reindex e v) v

theorem quadraticForm_continuous {ι : Type*} (e : ι ≃ ι) :
    Continuous (quadraticForm e) :=
  (reindex e).continuous.inner continuous_id

/-- All zero-set hypotheses of the sheet, without an arithmetic specialization. -/
structure StripData where
  Z : Set ℂ
  m : ℂ → ℕ
  locallyFinite : ∀ R : ℝ, {ρ ∈ Z | ‖ρ‖ ≤ R}.Finite
  positive : ∀ ρ ∈ Z, 1 ≤ m ρ
  counting : ∃ N : ℕ, Summable (fun ρ : Z =>
    (m ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹)
  strip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1
  reflection : ∀ ρ ∈ Z, zetaInvolution ρ ∈ Z ∧ m (zetaInvolution ρ) = m ρ
  conjugation : ∀ ρ ∈ Z, conj ρ ∈ Z ∧ m (conj ρ) = m ρ

def StripData.iota (D : StripData) : D.Z ≃ D.Z where
  toFun ρ := ⟨zetaInvolution ρ, (D.reflection ρ ρ.property).1⟩
  invFun ρ := ⟨zetaInvolution ρ, (D.reflection ρ ρ.property).1⟩
  left_inv ρ := Subtype.ext (zetaInvolution_involutive ρ)
  right_inv ρ := Subtype.ext (zetaInvolution_involutive ρ)

def StripData.conjugate (D : StripData) : D.Z ≃ D.Z where
  toFun ρ := ⟨conj ρ, (D.conjugation ρ ρ.property).1⟩
  invFun ρ := ⟨conj ρ, (D.conjugation ρ ρ.property).1⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

def StripData.realSubspace (D : StripData) : Submodule ℝ (SpectralHilbert D.Z) where
  carrier := {v | ∀ ρ, v (D.conjugate ρ) = conj (v ρ)}
  zero_mem' := by simp
  add_mem' hv hw := by intro ρ; simp [hv ρ, hw ρ]
  smul_mem' a v hv := by intro ρ; simp [hv ρ, Complex.real_smul]

theorem StripData.realSubspace_closed (D : StripData) :
    IsClosed (D.realSubspace : Set (SpectralHilbert D.Z)) := by
  have heval (ρ : D.Z) : Continuous (fun v : SpectralHilbert D.Z => v ρ) :=
    (lp.evalCLM ℝ (fun _ : D.Z => ℂ) 2 ρ).continuous
  change IsClosed {v : SpectralHilbert D.Z | ∀ ρ, v (D.conjugate ρ) = conj (v ρ)}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun ρ => isClosed_eq (heval _) (Complex.continuous_conj.comp (heval _))

instance (D : StripData) : CompleteSpace D.realSubspace :=
  D.realSubspace_closed.completeSpace_coe

theorem spectralTransform_conjugate (f : ℝ → ℝ) (s : ℂ) :
    spectralTransform f (conj s) = conj (spectralTransform f s) := by
  unfold spectralTransform
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  have htwo : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp [map_mul, map_sub, ← Complex.exp_conj, htwo]

theorem StripData.spectralMap_mem_realSubspace (D : StripData) (f : testFunctions) :
    spectralMap D.Z D.m D.counting D.strip f ∈ D.realSubspace := by
  intro ρ
  change (Real.sqrt (D.m (conj (ρ : ℂ))) : ℂ) * spectralTransform f (conj ρ) =
    conj ((Real.sqrt (D.m ρ) : ℂ) * spectralTransform f ρ)
  rw [(D.conjugation ρ ρ.property).2, spectralTransform_conjugate]
  simp

def realTestComplex (f : testFunctions) : complexTests :=
  ⟨fun u => (f u : ℂ),
    Complex.ofRealCLM.contDiff.comp f.property.1,
    f.property.2.comp_left Complex.ofReal_zero⟩

theorem spectralTransform_add (f g : testFunctions) (s : ℂ) :
    spectralTransform (fun u => f u + g u) s =
      spectralTransform f s + spectralTransform g s := by
  unfold spectralTransform
  simp only [Complex.ofReal_add, add_mul]
  exact integral_add (transform_integrable (realTestComplex f) s)
    (transform_integrable (realTestComplex g) s)

theorem spectralTransform_smul (a : ℝ) (f : testFunctions) (s : ℂ) :
    spectralTransform (fun u => a * f u) s = (a : ℂ) * spectralTransform f s := by
  simp only [spectralTransform, Complex.ofReal_mul, mul_assoc, integral_const_mul]

def StripData.spectralLinearMap (D : StripData) : testFunctions →ₗ[ℝ] SpectralHilbert D.Z where
  toFun := spectralMap D.Z D.m D.counting D.strip
  map_add' f g := by
    apply lp.ext
    funext ρ
    change (Real.sqrt (D.m ρ) : ℂ) * spectralTransform (fun u => f u + g u) ρ = _
    rw [spectralTransform_add]
    simp only [lp.coeFn_add, Pi.add_apply, spectralMap, weightedValues, mul_add]
  map_smul' a f := by
    apply lp.ext
    funext ρ
    change (Real.sqrt (D.m ρ) : ℂ) * spectralTransform (fun u => a * f u) ρ = _
    rw [spectralTransform_smul]
    simp only [RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply, spectralMap,
      weightedValues, Complex.real_smul]
    ring

def StripData.realSpectralMap (D : StripData) : testFunctions →ₗ[ℝ] D.realSubspace :=
  D.spectralLinearMap.codRestrict D.realSubspace D.spectralMap_mem_realSubspace

/-- The Hilbert form has exactly the normalization of the sheet's full zero sum. -/
theorem StripData.quadraticForm_spectralMap (D : StripData) (f : testFunctions) :
    quadraticForm D.iota (D.spectralLinearMap f) =
      ∑' ρ : D.Z, (D.m ρ : ℂ) *
        (spectralTransform f ρ * spectralTransform f (1 - ρ)) := by
  rw [quadraticForm_eq_tsum]
  congr 1
  funext ρ
  change conj ((Real.sqrt (D.m (zetaInvolution ρ)) : ℂ) *
    spectralTransform f (zetaInvolution ρ)) *
      ((Real.sqrt (D.m ρ) : ℂ) * spectralTransform f ρ) = _
  rw [(D.reflection ρ ρ.property).2, map_mul, Complex.conj_ofReal,
    ← spectralTransform_conjugate]
  have hc : conj (zetaInvolution (ρ : ℂ)) = 1 - ρ := by simp [zetaInvolution]
  rw [hc]
  have hs : (Real.sqrt (D.m ρ) : ℂ) ^ 2 = (D.m ρ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_cast
  calc _ = (Real.sqrt (D.m ρ) : ℂ) ^ 2 *
      (spectralTransform f ρ * spectralTransform f (1 - ρ)) := by ring
    _ = _ := by rw [hs]

/-- Absolute convergence of the sheet's quadratic sum is already a Phase 1 consequence. -/
theorem StripData.spectralPairing_summable (D : StripData) (f : testFunctions) :
    Summable (fun ρ : D.Z => (D.m ρ : ℂ) *
      (spectralTransform f ρ * spectralTransform f (1 - ρ))) := by
  have h := quadraticForm_summable D.iota (D.spectralLinearMap f)
  have heq : (fun ρ : D.Z => conj (D.spectralLinearMap f (D.iota ρ)) *
      D.spectralLinearMap f ρ) = (fun ρ : D.Z => (D.m ρ : ℂ) *
        (spectralTransform f ρ * spectralTransform f (1 - ρ))) := by
    funext ρ
    change conj ((Real.sqrt (D.m (zetaInvolution ρ)) : ℂ) *
      spectralTransform f (zetaInvolution ρ)) *
        ((Real.sqrt (D.m ρ) : ℂ) * spectralTransform f ρ) = _
    rw [(D.reflection ρ ρ.property).2, map_mul, Complex.conj_ofReal,
      ← spectralTransform_conjugate]
    have hc : conj (zetaInvolution (ρ : ℂ)) = 1 - ρ := by simp [zetaInvolution]
    rw [hc]
    have hs : (Real.sqrt (D.m ρ) : ℂ) ^ 2 = (D.m ρ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      norm_cast
    calc _ = (Real.sqrt (D.m ρ) : ℂ) ^ 2 *
        (spectralTransform f ρ * spectralTransform f (1 - ρ)) := by ring
      _ = _ := by rw [hs]
  rwa [heq] at h

/-- Density is an equivalent formulation of the annihilator problem, not an extra premise. -/
theorem StripData.density_iff_annihilator (D : StripData) :
    DenseRange D.realSpectralMap ↔
      ∀ w : D.realSubspace, (∀ f : testFunctions,
        inner ℝ w (D.realSpectralMap f) = 0) → w = 0 := by
  change Dense (Set.range D.realSpectralMap) ↔ _
  rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  constructor
  · intro h w hw
    have hmem : w ∈ (LinearMap.range D.realSpectralMap)ᗮ := by
      rw [Submodule.mem_orthogonal']
      rintro _ ⟨f, rfl⟩
      exact hw f
    simpa [h] using hmem
  · intro h
    apply (Submodule.eq_bot_iff _).2
    intro w hw
    apply h w
    intro f
    exact (Submodule.mem_orthogonal' _ w).1 hw _ ⟨f, rfl⟩

def StripData.annihilatorCoefficients (D : StripData) (w : SpectralHilbert D.Z)
    (ρ : D.Z) : ℂ := conj (w ρ) * (Real.sqrt (D.m ρ) : ℂ)

theorem StripData.annihilatorCoefficients_bound (D : StripData) (w : SpectralHilbert D.Z)
    (ρ : D.Z) : ‖D.annihilatorCoefficients w ρ‖ ≤ ‖w‖ * (D.m ρ : ℝ) := by
  have hm : (1 : ℝ) ≤ D.m ρ := by exact_mod_cast D.positive ρ ρ.property
  have hs : Real.sqrt (D.m ρ) ≤ (D.m ρ : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr hm)
  rw [StripData.annihilatorCoefficients, norm_mul, norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) w ρ) hs
    (Real.sqrt_nonneg _) (norm_nonneg _)

theorem StripData.inner_conjugation_real (D : StripData) (w v : D.realSubspace) :
    conj (inner ℂ (w : SpectralHilbert D.Z) (v : SpectralHilbert D.Z)) =
      inner ℂ (w : SpectralHilbert D.Z) (v : SpectralHilbert D.Z) := by
  simp only [lp.inner_eq_tsum, RCLike.inner_apply, Complex.conj_tsum, map_mul, conj_conj]
  have h := D.conjugate.tsum_eq (fun ρ => (v : SpectralHilbert D.Z) ρ *
    conj ((w : SpectralHilbert D.Z) ρ))
  rw [← h]
  congr 1
  funext ρ
  rw [v.property, w.property]
  simp only [conj_conj]

theorem StripData.real_inner_eq (D : StripData) (w v : SpectralHilbert D.Z) :
    inner ℝ w v = (inner ℂ w v).re := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    Complex.re_tsum (lp.summable_inner (𝕜 := ℂ) w v)]
  congr 1

theorem StripData.annihilator_real_test (D : StripData) (w : D.realSubspace)
    (hann : ∀ f : testFunctions, inner ℝ w (D.realSpectralMap f) = 0)
    (f : testFunctions) :
    ∑' ρ : D.Z, D.annihilatorCoefficients w ρ * spectralTransform f ρ = 0 := by
  have hr := hann f
  change inner ℝ (w : SpectralHilbert D.Z) (D.spectralLinearMap f) = 0 at hr
  rw [D.real_inner_eq] at hr
  have hi := D.inner_conjugation_real w (D.realSpectralMap f)
  have hz : inner ℂ (w : SpectralHilbert D.Z) (D.spectralLinearMap f) = 0 := by
    apply Complex.ext hr
    have him := congrArg Complex.im hi
    simp only [Complex.conj_im] at him
    change -(inner ℂ (w : SpectralHilbert D.Z) (D.spectralLinearMap f)).im =
      (inner ℂ (w : SpectralHilbert D.Z) (D.spectralLinearMap f)).im at him
    change (inner ℂ (w : SpectralHilbert D.Z) (D.spectralLinearMap f)).im = 0
    linarith
  rw [lp.inner_eq_tsum] at hz
  convert hz using 1
  congr 1
  funext ρ
  simp [StripData.annihilatorCoefficients, spectralLinearMap, spectralMap, weightedValues,
    RCLike.inner_apply, mul_comm, mul_assoc]

theorem StripData.annihilator_real_test_summable (D : StripData) (w : SpectralHilbert D.Z)
    (f : testFunctions) :
    Summable (fun ρ : D.Z => D.annihilatorCoefficients w ρ * spectralTransform f ρ) := by
  have h := lp.summable_inner (𝕜 := ℂ) w (D.spectralLinearMap f)
  simpa [StripData.annihilatorCoefficients, StripData.spectralLinearMap, spectralMap, weightedValues,
    RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc] using h

theorem StripData.annihilator_complex_test (D : StripData) (w : D.realSubspace)
    (hann : ∀ f : testFunctions, inner ℝ w (D.realSpectralMap f) = 0)
    (g : complexTests) :
    ∑' ρ : D.Z, D.annihilatorCoefficients w ρ * complexTransform g ρ = 0 := by
  let f₁ : testFunctions := ⟨fun u => (g u).re,
    Complex.reCLM.contDiff.comp g.property.1,
    g.property.2.comp_left (by rfl)⟩
  let f₂ : testFunctions := ⟨fun u => (g u).im,
    Complex.imCLM.contDiff.comp g.property.1,
    g.property.2.comp_left (by rfl)⟩
  have heq (z : ℂ) : complexTransform g z =
      spectralTransform f₁ z + Complex.I * spectralTransform f₂ z := by
    have h₁ := transform_integrable (realTestComplex f₁) z
    have h₂ := (transform_integrable (realTestComplex f₂) z).const_mul Complex.I
    change Integrable (fun u : ℝ => (f₁ u : ℂ) * Complex.exp ((z - 1 / 2) * u)) at h₁
    change Integrable (fun u : ℝ => Complex.I * ((f₂ u : ℂ) * Complex.exp ((z - 1 / 2) * u))) at h₂
    change (∫ u : ℝ, g u * Complex.exp ((z - 1 / 2) * u)) = _
    rw [show (fun u : ℝ => g u * Complex.exp ((z - 1 / 2) * u)) =
      (fun u : ℝ => (f₁ u : ℂ) * Complex.exp ((z - 1 / 2) * u) +
        Complex.I * ((f₂ u : ℂ) * Complex.exp ((z - 1 / 2) * u))) by
      funext u
      dsimp [f₁, f₂]
      rw [← mul_assoc, mul_comm Complex.I, ← add_mul, Complex.re_add_im],
      integral_add h₁ h₂, integral_const_mul]
    rfl
  simp_rw [heq, mul_add, mul_left_comm (D.annihilatorCoefficients w _) Complex.I]
  rw [Summable.tsum_add (D.annihilator_real_test_summable w f₁)
    ((D.annihilator_real_test_summable w f₂).mul_left Complex.I), tsum_mul_left,
    D.annihilator_real_test w hann f₁, D.annihilator_real_test w hann f₂]
  simp

theorem StripData.gaussian_identity (D : StripData) (w : D.realSubspace)
    (hann : ∀ f : testFunctions, inner ℝ w (D.realSpectralMap f) = 0)
    (a b s : ℝ) (hs : 0 < s) :
    ∑' ρ : D.Z, D.annihilatorCoefficients w ρ *
      Complex.exp ((s : ℂ) * GppGwefGaussian.exponent a b ρ) = 0 := by
  let q : ℝ := 1 / (2 * s)
  let v : ℂ := -Complex.I * ((a : ℂ) + Complex.I * b)
  have hq : 0 < q := by dsimp [q]; positivity
  let f (k : ℕ) : complexTests := ⟨GppGwefC1.cutoff q v k,
    GppGwefC1.cutoff_smooth q v k, GppGwefC1.cutoff_compact q v k⟩
  have hzero (k : ℕ) : ∑' ρ : D.Z, D.annihilatorCoefficients w ρ *
      GppGwefC1.transform (GppGwefC1.cutoff q v k) ρ = 0 :=
    D.annihilator_complex_test w hann (f k)
  have hlim := GppGwefC1.gaussian_cutoff_series_tendsto D.Z D.m D.counting D.strip
    (D.annihilatorCoefficients w) ‖(w : SpectralHilbert D.Z)‖ (norm_nonneg _)
    (D.annihilatorCoefficients_bound w) hq v
  have hid : ∑' ρ : D.Z, D.annihilatorCoefficients w ρ *
      GppGwefC1.transform (GppGwefC1.packet q v) ρ = 0 := by
    have hlim₀ : Tendsto (fun k : ℕ => ∑' ρ : D.Z, D.annihilatorCoefficients w ρ *
        GppGwefC1.transform (GppGwefC1.cutoff q v k) ρ) atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hlim hlim₀
  have hexp (z : ℂ) : (v + z - 1 / 2) ^ 2 / (4 * (q : ℂ)) =
      (s : ℂ) * GppGwefGaussian.exponent a b z := by
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    dsimp [v, q, GppGwefGaussian.exponent]
    push_cast
    field_simp
    <;> ring
  simp_rw [GppGwefC1.packet_transform hq, hexp,
    mul_left_comm (D.annihilatorCoefficients w _) ((Real.pi / (q : ℂ)) ^ (1 / 2 : ℂ))] at hid
  rw [tsum_mul_left] at hid
  have hK : (Real.pi / (q : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.ofReal_ne_zero.mpr hq.ne'))
  exact (mul_eq_zero.mp hid).resolve_left hK

/-- The annihilator vanishes: C1 supplies the Gaussian identities through
smooth cutoffs with one summable dominator; C2 separates a unique dominant
coefficient and sends the normalized tail to zero. All data are explicit in
`StripData`; neither step assumes a location for the points within the strip. -/
theorem gaussian_annihilator (D : StripData) (w : D.realSubspace)
    (hann : ∀ f : testFunctions, inner ℝ w (D.realSpectralMap f) = 0) : w = 0 := by
  let c : D.Z → ℂ := D.annihilatorCoefficients w
  have hGaussian : ∀ a b s : ℝ, 0 < s →
      ∑' ρ : D.Z, c ρ * Complex.exp ((s : ℂ) * GppGwefGaussian.exponent a b ρ) = 0 := by
    intro a b s hs
    exact D.gaussian_identity w hann a b s hs
  have hc := GppGwefGaussian.coefficients_zero_of_gaussian_identity D.Z D.m
    D.locallyFinite D.positive D.counting D.strip c ‖(w : SpectralHilbert D.Z)‖
    (norm_nonneg _) (D.annihilatorCoefficients_bound w) hGaussian
  apply Subtype.ext
  apply lp.ext
  funext ρ
  change (w : SpectralHilbert D.Z) ρ = 0
  have hm : (0 : ℝ) < D.m ρ := by exact_mod_cast D.positive ρ ρ.property
  have hs : (Real.sqrt (D.m ρ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne'
  have hρ : conj ((w : SpectralHilbert D.Z) ρ) = 0 :=
    (mul_eq_zero.mp (hc ρ)).resolve_right hs
  simpa using hρ

end GppGwefInterp
