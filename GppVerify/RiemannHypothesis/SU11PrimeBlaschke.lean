import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The prime TFD state as an SU(1,1) coherent state: Euler factor, Blaschke channel, mass

Source: Codex, GPPDiscovery2 `research/` (read from the bridge copy at `a0ab790`..`59bf0a2`):
* `2026-09-27_prime_su11_tfd_euler_blaschke_closure.md` §§1–8;
* `2026-09-27_prime_tfd_equals_local_euler_blaschke_scattering.md` §§1–7;
* `2026-09-27_exact_prime_to_archimedean_su11_intertwiner.md` §§3–9 (the algebraic/trigonometric
  part).

Throughout, `a = p^{-1/2}` is the critical TFD radius at a prime `p`, and
`P_a(θ) = (1 − a²)/(1 − 2a cos θ + a²)` is the Poisson kernel.

## What is proved

**Coherent state and Euler factor.**
* `coherent_normalization`: `Σ_m (1 − r²) r^{2m} = 1`, so `|z⟩ = √(1−|z|²) Σ z^m |m,m⟩` is
  normalized.
* `coherent_overlap`: `⟨Ω_r, Ω_s⟩ = √((1−r²)(1−s²)) / (1 − r s)`.
* `purity_hasSum` and `purity_prime`: `Tr ρ² = (1−r²)/(1+r²)`, which is `(p−1)/(p+1)` at
  `r² = 1/p`.
* `euler_factor_intensity`: `(1 − r²) · ‖(1 − r e^{−iθ})⁻¹‖² = P_r(θ)`. With `r = p^{-σ}` and
  `θ = t log p` this is the note's `(1 − p^{-2σ}) |ζ_p(σ + it)|² = P_{p^{-σ}}(t log p)`.
* `cpow_polar`: `p^{-(σ+it)} = p^{-σ} e^{−i t log p}` for `p > 0`, the dictionary between the two.

**Blaschke transfer.** With `B_a(z) = (z − a)/(1 − a z)`:
* `blaschke_euler_transfer`: `z · ζ_p(s)/ζ_p(1−s) = B_a(z)` for `z = p^{1/2−s}`, `a = p^{-1/2}`;
* `blaschke_zero`, `blaschke_inv`, `blaschke_norm_one`: `B_a(a) = 0`, `B_a(1/z) = B_a(z)⁻¹`, and
  `|B_a(z)| = 1` on `|z| = 1` for real `|a| < 1`;
* `blaschke_hasDerivAt`, `blaschke_boundary_delay`: `z B_a'(z)/B_a(z) = P_a(θ)` on `z = e^{iθ}`.
  This is the note's "group delay is the Poisson kernel".

**Shadow reflection.**
* `shadow_inv`: `z_p(1−s) = z_p(s)⁻¹` for `z_p(s) = p^{1/2−s}`;
* `norm_zp_eq_one_iff`: `‖z_p(s)‖ = 1 ⟺ Re s = ½` (for `p > 1`);
* `shadow_conj_disk`: `z_p(1 − s̄) = (conj z_p(s))⁻¹`, i.e. the shadow is `w ↦ 1/w̄`.

**Hyperbolic distance and mass.** With `κ = artanh a`:
* `poisson_zero`, `poisson_pi`, `poisson_zero_mul_pi`: `P_a(0) = e^{2κ}`, `P_a(π) = e^{−2κ}`,
  product `1`;
* `cayley_eq_exp`: `(1−a)/(1+a) = e^{−2κ}`;
* `mass_anisotropy`: `μ² = P_a(0) + P_a(π) − 2` for `μ = 2 sinh κ`.

**Archimedean tilt, algebraic part.** With `α = arctan r`, `cos 2α = (1−r²)/(1+r²)`
(`cos_two_arctan`), the overlap in the tilted picture equals the occupation-basis overlap
(`overlap_trig`), the mean is `r/(1−r²) = ½ tan 2α` (`mean_eq_tan`), and
`Var − mean² = ¼` (`var_sub_mean_sq`).

## Checks

Every identity above was checked by hand in the notes; no corrections. In particular the
generating function `G(z,x) = e^{2x arctan z}/√(1+z²)` satisfies the ODE the note derives from the
Jacobi recurrence, and the secant moment formula `∫ e^{tx} sech(πx) dx = sec(t/2)` is the standard
Fourier transform of `sech`.

## Scope

Local identities only. **Not formalized:** the SU(1,1) Lie-algebra representation on the doubled
oscillator, the Jacobi transform `U` and its generating function (the series
`Σ P_n z^n` of the orthonormal polynomials), the secant moment integral, the Fisher-metric
statement `d_H = √2 D_F`, the Euler-product statement
`|ζ(σ+it)|²/ζ(2σ) = ∏_p P_{p^{-σ}}(t log p)`, and the adelic sewing (the note's open global
target). No RH claim.
-/

open Complex

namespace GppSU11Prime

/-- The Poisson kernel `P_r(θ) = (1 − r²)/(1 − 2 r cos θ + r²)`. -/
noncomputable def poisson (r θ : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)

/-- The Blaschke disk automorphism `B_a(z) = (z − a)/(1 − a z)`. -/
noncomputable def blaschke (a z : ℂ) : ℂ := (z - a) / (1 - a * z)

lemma den_pos (r θ : ℝ) (hr : |r| < 1) : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
  have h1 := Real.cos_le_one θ
  have h2 := Real.neg_one_le_cos θ
  have hr' := abs_lt.mp hr
  rcases le_total 0 r with h | h
  · nlinarith [mul_nonneg h (sub_nonneg.mpr h1)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr (by linarith : -1 ≤ Real.cos θ))]

/-! ### Coherent state -/

/-- **Normalization of the coherent state.** `Σ_m (1 − r²) r^{2m} = 1`. -/
theorem coherent_normalization (r : ℝ) (hr : |r| < 1) :
    HasSum (fun m : ℕ => (1 - r ^ 2) * (r ^ 2) ^ m) 1 := by
  have h : |r ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg r]
  have hg := (hasSum_geometric_of_abs_lt_one h).mul_left (1 - r ^ 2)
  have hne : 1 - r ^ 2 ≠ 0 := by nlinarith [abs_nonneg r, sq_abs r]
  rwa [mul_inv_cancel₀ hne] at hg

/-- **Overlap of two coherent states.** `⟨Ω_r, Ω_s⟩ = √((1−r²)(1−s²))/(1 − r s)`. -/
theorem coherent_overlap (r s : ℝ) (hr : |r| < 1) (hs : |s| < 1) :
    HasSum (fun m : ℕ => Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) * (r * s) ^ m)
      (Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) / (1 - r * s)) := by
  have h : |r * s| < 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg r, abs_nonneg s]
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)))
  rwa [← div_eq_mul_inv] at this

/-- **Purity.** `Σ_m ((1 − r²) r^{2m})² = (1 − r²)/(1 + r²)`. -/
theorem purity_hasSum (r : ℝ) (hr : |r| < 1) :
    HasSum (fun m : ℕ => ((1 - r ^ 2) * (r ^ 2) ^ m) ^ 2) ((1 - r ^ 2) / (1 + r ^ 2)) := by
  have h : |r ^ 4| < 1 := by
    rw [abs_pow]; have := abs_nonneg r; nlinarith [pow_lt_one₀ this hr (by norm_num : (4 : ℕ) ≠ 0)]
  have hg := (hasSum_geometric_of_abs_lt_one h).mul_left ((1 - r ^ 2) ^ 2)
  have h1 : 1 - r ^ 2 ≠ 0 := by nlinarith [abs_nonneg r, sq_abs r]
  have h2 : 1 + r ^ 2 ≠ 0 := by positivity
  have h3 : 1 - r ^ 4 = (1 - r ^ 2) * (1 + r ^ 2) := by ring
  have e : (fun m : ℕ => ((1 - r ^ 2) * (r ^ 2) ^ m) ^ 2) =
      fun m => (1 - r ^ 2) ^ 2 * (r ^ 4) ^ m := by
    funext m; rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  have e2 : (1 - r ^ 2) / (1 + r ^ 2) = (1 - r ^ 2) ^ 2 * (1 - r ^ 4)⁻¹ := by
    rw [h3]; field_simp
  rw [e, e2]; exact hg

/-- **Prime purity.** At `r² = 1/p`, the purity is `(p − 1)/(p + 1)`. -/
theorem purity_prime (p : ℝ) (hp : 1 < p) :
    (1 - 1 / p) / (1 + 1 / p) = (p - 1) / (p + 1) := by
  have : p ≠ 0 := by linarith
  have h : p + 1 ≠ 0 := by linarith
  field_simp

/-! ### The Euler factor is the boundary phase intensity -/

lemma normSq_one_sub_polar (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      1 - 2 * r * Real.cos θ + r ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **The Euler factor is the Poisson kernel.** `(1 − r²)‖(1 − r e^{−iθ})⁻¹‖² = P_r(θ)`. -/
theorem euler_factor_intensity (r θ : ℝ) (hr : |r| < 1) :
    (1 - r ^ 2) * ‖(1 - (r : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))⁻¹‖ ^ 2 =
      poisson r θ := by
  have hd := den_pos r θ hr
  rw [norm_inv, inv_pow, Complex.sq_norm, normSq_one_sub_polar, Real.cos_neg, poisson]
  field_simp

/-- **Polar form of `p^{-(σ+it)}`** for `p > 0`: modulus `p^{-σ}`, angle `−t log p`. -/
theorem cpow_polar (p σ t : ℝ) (hp : 0 < p) :
    (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ((p ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le,
    Real.rpow_def_of_pos hp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The Blaschke transfer -/


lemma zp_ne_zero (p : ℝ) (hp : 0 < p) (s : ℂ) : (p : ℂ) ^ ((1 / 2 : ℂ) - s) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  push_neg
  intro h; exact absurd h (by exact_mod_cast hp.ne')

/-- **The local Euler transfer is a Blaschke automorphism.** For `z = p^{1/2−s}` and
`a = p^{-1/2}`: `z · ζ_p(s)/ζ_p(1−s) = B_a(z)`, where `ζ_p(s) = (1 − p^{-s})⁻¹`. -/
theorem blaschke_euler_transfer (p : ℝ) (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ ((1 / 2 : ℂ) - s) *
        ((1 - (p : ℂ) ^ (-s))⁻¹ / (1 - (p : ℂ) ^ (-(1 - s)))⁻¹) =
      blaschke ((p : ℂ) ^ (-(1 / 2 : ℂ))) ((p : ℂ) ^ ((1 / 2 : ℂ) - s)) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set z := (p : ℂ) ^ ((1 / 2 : ℂ) - s) with hz
  set a := (p : ℂ) ^ (-(1 / 2 : ℂ)) with ha
  have hz0 : z ≠ 0 := zp_ne_zero p hp s
  have h1 : (p : ℂ) ^ (-s) = a * z := by
    rw [ha, hz, ← Complex.cpow_add _ _ hp']; congr 1; ring
  have h2 : (p : ℂ) ^ (-(1 - s)) = a / z := by
    rw [ha, hz, ← Complex.cpow_sub _ _ hp']; congr 1; ring
  rw [h1, h2, blaschke, inv_div_inv, ← mul_div_assoc]
  congr 1
  field_simp

/-- `B_a` sends its parameter to the origin. -/
theorem blaschke_zero (a : ℂ) : blaschke a a = 0 := by
  simp [blaschke]

/-- **Reciprocity.** `B_a(1/z) = B_a(z)⁻¹`. -/
theorem blaschke_inv (a z : ℂ) (hz : z ≠ 0) : blaschke a z⁻¹ = (blaschke a z)⁻¹ := by
  rw [blaschke, blaschke, inv_div]
  have h : z ≠ 0 := hz
  by_cases h1 : 1 - a / z = 0
  · have h2 : z - a = 0 := by
      have : z * (1 - a / z) = z - a := by field_simp
      rw [← this, h1, mul_zero]
    have h3 : 1 - a * z⁻¹ = 0 := by simpa [div_eq_mul_inv] using h1
    rw [h3, h2]; simp
  · have e1 : z⁻¹ - a = (1 - a * z) / z := by field_simp
    have e2 : 1 - a * z⁻¹ = (z - a) / z := by field_simp
    rw [e1, e2, div_div_div_cancel_right₀ hz]

/-- **Unitarity on the circle.** For real `|a| < 1` and `|z| = 1`: `‖B_a(z)‖ = 1`. -/
theorem blaschke_norm_one (a : ℝ) (ha : |a| < 1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖blaschke (a : ℂ) z‖ = 1 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at this
    nlinarith
  have hnum : Complex.normSq (z - a) = 1 - 2 * a * z.re + a ^ 2 := by
    rw [Complex.normSq_apply]; simp; nlinarith
  have hden : Complex.normSq (1 - (a : ℂ) * z) = 1 - 2 * a * z.re + a ^ 2 := by
    rw [Complex.normSq_apply]; simp; nlinarith
  have hpos : 0 < 1 - 2 * a * z.re + a ^ 2 := by
    have hre : |z.re| ≤ 1 := by nlinarith [sq_nonneg z.im, abs_nonneg z.re, sq_abs z.re]
    have := abs_le.mp hre
    have ha' := abs_lt.mp ha
    rcases le_total 0 a with h | h
    · nlinarith [mul_nonneg h (sub_nonneg.mpr this.2)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr (by linarith [this.1] : -1 ≤ z.re))]
  rw [blaschke, norm_div]
  have hn : ‖z - a‖ ^ 2 = ‖(1 : ℂ) - a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, hnum, hden]
  have hd0 : ‖(1 : ℂ) - a * z‖ ≠ 0 := by
    intro h
    have h0 : (1 : ℂ) - a * z = 0 := norm_eq_zero.mp h
    rw [h0, Complex.normSq_zero] at hden
    linarith
  have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn
  rw [this]; exact div_self hd0

/-- `B_a` has derivative `(1 − a²)/(1 − a z)²` away from its pole. -/
theorem blaschke_hasDerivAt (a z : ℂ) (hz : 1 - a * z ≠ 0) :
    HasDerivAt (blaschke a) ((1 - a ^ 2) / (1 - a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - a * w) (-a) z := by
    have h3 : HasDerivAt (fun w : ℂ => a * w) (a * 1) z := HasDerivAt.const_mul a (hasDerivAt_id z)
    have h4 : HasDerivAt (fun w : ℂ => 1 - a * w) (0 - a * 1) z :=
      HasDerivAt.fun_sub (hasDerivAt_const z (1 : ℂ)) h3
    exact HasDerivAt.congr_deriv h4 (by ring)
  have h := HasDerivAt.fun_div h1 h2 hz
  show HasDerivAt (fun w => (w - a) / (1 - a * w)) _ z
  exact HasDerivAt.congr_deriv h (by ring)

/-- **Group delay is the Poisson kernel.** On `z = e^{iθ}` and real `|a| < 1`:
`z · B_a'(z)/B_a(z) = P_a(θ)`. -/
theorem blaschke_boundary_delay (a θ : ℝ) (ha : |a| < 1) :
    Complex.exp ((θ : ℂ) * Complex.I) *
        ((1 - (a : ℂ) ^ 2) / (1 - a * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2) /
        blaschke (a : ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = (poisson a θ : ℂ) := by
  have hd := den_pos a θ ha
  set z : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hzdef
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzinv : z⁻¹ = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [hzdef, ← Complex.exp_neg]; congr 1; ring
  have hc : (2 : ℂ) * Complex.cos (θ : ℂ) = z + z⁻¹ := by
    rw [Complex.two_cos, hzinv]
  have e : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hprod : (1 - (a : ℂ) * z) * (z - a) =
      z * (((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ)) : ℂ) := by
    push_cast
    linear_combination (a : ℂ) * e + (a : ℂ) * z * hc
  have hDne : (((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hprod0 : (1 - (a : ℂ) * z) * (z - a) ≠ 0 := by
    rw [hprod]; exact mul_ne_zero hz0 hDne
  have h1 : 1 - (a : ℂ) * z ≠ 0 := left_ne_zero_of_mul hprod0
  have h2 : z - (a : ℂ) ≠ 0 := right_ne_zero_of_mul hprod0
  rw [blaschke, poisson]
  have e1 : z * ((1 - (a : ℂ) ^ 2) / (1 - (a : ℂ) * z) ^ 2) / ((z - (a : ℂ)) / (1 - (a : ℂ) * z)) =
      z * (1 - (a : ℂ) ^ 2) / ((1 - (a : ℂ) * z) * (z - a)) := by
    field_simp
  rw [e1, hprod]
  push_cast
  field_simp

/-! ### Shadow reflection -/

/-- The centered local coordinate `z_p(s) = p^{1/2 − s}`. -/
noncomputable def zp (p : ℝ) (s : ℂ) : ℂ := (p : ℂ) ^ ((1 / 2 : ℂ) - s)

/-- **Shadow is inversion.** `z_p(1 − s) = z_p(s)⁻¹`. -/
theorem shadow_inv (p : ℝ) (s : ℂ) : zp p (1 - s) = (zp p s)⁻¹ := by
  unfold zp
  rw [← Complex.cpow_neg]; congr 1; ring

/-- `‖z_p(s)‖ = p^{1/2 − Re s}`. -/
theorem norm_zp (p : ℝ) (hp : 0 < p) (s : ℂ) : ‖zp p s‖ = p ^ ((1 / 2 : ℝ) - s.re) := by
  unfold zp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

/-- **The critical line is the unit circle in every local coordinate.** For `p > 1`:
`‖z_p(s)‖ = 1 ⟺ Re s = ½`. -/
theorem norm_zp_eq_one_iff (p : ℝ) (hp : 1 < p) (s : ℂ) : ‖zp p s‖ = 1 ↔ s.re = 1 / 2 := by
  rw [norm_zp p (by linarith) s]
  constructor
  · intro h
    rcases lt_trichotomy ((1 / 2 : ℝ) - s.re) 0 with h0 | h0 | h0
    · have := Real.rpow_lt_one_of_one_lt_of_neg hp h0
      linarith
    · linarith
    · have := Real.one_lt_rpow hp h0
      linarith
  · intro h
    rw [h, sub_self, Real.rpow_zero]

/-- **Shadow is `w ↦ 1/w̄`.** `z_p(1 − s̄) = (conj z_p(s))⁻¹`. -/
theorem shadow_conj_disk (p : ℝ) (hp : 0 < p) (s : ℂ) :
    zp p (1 - (starRingEnd ℂ) s) = ((starRingEnd ℂ) (zp p s))⁻¹ := by
  have harg : (p : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hp.le]; exact Real.pi_ne_zero.symm
  have hconj : ∀ w : ℂ, (starRingEnd ℂ) ((p : ℂ) ^ w) = (p : ℂ) ^ ((starRingEnd ℂ) w) := by
    intro w
    have h := Complex.conj_cpow (p : ℂ) ((starRingEnd ℂ) w) harg
    rw [Complex.conj_ofReal, Complex.conj_conj] at h
    exact h.symm
  have e : (starRingEnd ℂ) ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) - (starRingEnd ℂ) s := by
    rw [map_sub, map_div₀, map_one, map_ofNat]
  unfold zp
  rw [hconj, e, ← Complex.cpow_neg]
  congr 1; ring

/-! ### Hyperbolic distance and the mass coordinate -/

lemma one_sub_ne (a : ℝ) (ha : |a| < 1) : 1 - a ≠ 0 := by
  have := (abs_lt.mp ha).2; linarith

lemma one_add_ne (a : ℝ) (ha : |a| < 1) : 1 + a ≠ 0 := by
  have := (abs_lt.mp ha).1; linarith

theorem poisson_zero (a : ℝ) (ha : |a| < 1) : poisson a 0 = (1 + a) / (1 - a) := by
  have h := one_sub_ne a ha
  simp only [poisson, Real.cos_zero]
  have : 1 - 2 * a * 1 + a ^ 2 = (1 - a) ^ 2 := by ring
  rw [this]; field_simp; ring

theorem poisson_pi (a : ℝ) (ha : |a| < 1) : poisson a Real.pi = (1 - a) / (1 + a) := by
  have h := one_add_ne a ha
  simp only [poisson, Real.cos_pi]
  have : 1 - 2 * a * (-1) + a ^ 2 = (1 + a) ^ 2 := by ring
  rw [this]; field_simp; ring

/-- The extremal delays are reciprocal: `P_a(0) · P_a(π) = 1`. -/
theorem poisson_zero_mul_pi (a : ℝ) (ha : |a| < 1) : poisson a 0 * poisson a Real.pi = 1 := by
  rw [poisson_zero a ha, poisson_pi a ha]
  field_simp [one_sub_ne a ha, one_add_ne a ha]

lemma mem_Ioo_of_abs (a : ℝ) (ha : |a| < 1) : a ∈ Set.Ioo (-1 : ℝ) 1 := by
  have := abs_lt.mp ha; exact ⟨this.1, this.2⟩

/-- `e^{2κ} = (1 + a)/(1 − a)` for `κ = artanh a`. -/
theorem exp_two_artanh (a : ℝ) (ha : |a| < 1) :
    Real.exp (2 * Real.artanh a) = (1 + a) / (1 - a) := by
  have hm := mem_Ioo_of_abs a ha
  have h1 : 0 < 1 - a := by linarith [hm.2]
  have h2 : 0 < 1 + a := by linarith [hm.1]
  rw [show 2 * Real.artanh a = Real.artanh a + Real.artanh a by ring, Real.exp_add,
    Real.exp_artanh hm, ← sq, Real.sq_sqrt (div_pos h2 h1).le]

/-- **Cayley coordinate.** `(1 − a)/(1 + a) = e^{−2κ}`. -/
theorem cayley_eq_exp (a : ℝ) (ha : |a| < 1) :
    (1 - a) / (1 + a) = Real.exp (-(2 * Real.artanh a)) := by
  rw [Real.exp_neg, exp_two_artanh a ha, inv_div]

theorem poisson_zero_eq_exp (a : ℝ) (ha : |a| < 1) :
    poisson a 0 = Real.exp (2 * Real.artanh a) := by
  rw [poisson_zero a ha, exp_two_artanh a ha]

theorem poisson_pi_eq_exp (a : ℝ) (ha : |a| < 1) :
    poisson a Real.pi = Real.exp (-(2 * Real.artanh a)) := by
  rw [poisson_pi a ha, cayley_eq_exp a ha]

/-- **Mass is delay anisotropy.** For `μ = 2 sinh κ`, `κ = artanh a`:
`μ² = P_a(0) + P_a(π) − 2`. -/
theorem mass_anisotropy (a : ℝ) (ha : |a| < 1) :
    (2 * Real.sinh (Real.artanh a)) ^ 2 = poisson a 0 + poisson a Real.pi - 2 := by
  have hm := mem_Ioo_of_abs a ha
  have h1 := one_sub_ne a ha
  have h2 := one_add_ne a ha
  have hsq : 0 < 1 - a ^ 2 := by nlinarith [abs_lt.mp ha, sq_abs a]
  rw [Real.sinh_artanh hm, mul_pow, div_pow, Real.sq_sqrt hsq.le, poisson_zero a ha,
    poisson_pi a ha]
  have h3 : 1 - a ^ 2 ≠ 0 := hsq.ne'
  field_simp
  ring

/-! ### The Archimedean exponential tilt: algebraic part -/

theorem cos_two_arctan (r : ℝ) : Real.cos (2 * Real.arctan r) = (1 - r ^ 2) / (1 + r ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have : 1 + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The two overlap formulas agree.** With `α = arctan r`, `β = arctan s`:
`√(cos 2α cos 2β)/cos(α+β) = √((1−r²)(1−s²))/(1 − r s)`. -/
theorem overlap_trig (r s : ℝ) (hr : |r| < 1) (hs : |s| < 1) :
    Real.sqrt (Real.cos (2 * Real.arctan r) * Real.cos (2 * Real.arctan s)) /
        Real.cos (Real.arctan r + Real.arctan s) =
      Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) / (1 - r * s) := by
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith [abs_lt.mp hr, sq_abs r]
  have hs2 : 0 < 1 - s ^ 2 := by nlinarith [abs_lt.mp hs, sq_abs s]
  have hrs : 0 < 1 - r * s := by
    have h1 : |r * s| < 1 := by
      rw [abs_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg r) hr hs.le
    have := le_abs_self (r * s)
    linarith
  have hu0 : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hv0 : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos (Real.arctan r + Real.arctan s) =
      (1 - r * s) / (Real.sqrt (1 + r ^ 2) * Real.sqrt (1 + s ^ 2)) := by
    rw [Real.cos_add, Real.cos_arctan, Real.cos_arctan, Real.sin_arctan, Real.sin_arctan]
    field_simp
  have hprod : Real.cos (2 * Real.arctan r) * Real.cos (2 * Real.arctan s) =
      ((1 - r ^ 2) * (1 - s ^ 2)) / (Real.sqrt (1 + r ^ 2) * Real.sqrt (1 + s ^ 2)) ^ 2 := by
    rw [cos_two_arctan, cos_two_arctan, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    field_simp
  rw [hcos, hprod, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- **The mean.** `½ tan(2 arctan r) = r/(1 − r²)`. -/
theorem mean_eq_tan (r : ℝ) : (1 / 2) * Real.tan (2 * Real.arctan r) = r / (1 - r ^ 2) := by
  rw [Real.tan_two_mul, Real.tan_arctan]
  ring

/-- **Variance minus mean squared is `¼`.** -/
theorem var_sub_mean_sq (r : ℝ) (hr : |r| < 1) :
    (1 / 4) * ((1 + r ^ 2) / (1 - r ^ 2)) ^ 2 - (r / (1 - r ^ 2)) ^ 2 = 1 / 4 := by
  have h : 1 - r ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hr, sq_abs r]
  field_simp
  ring

/-- `¼ sec²(2α) = ((1 + r²)/(2(1 − r²)))²`, the variance of the tilted law. -/
theorem var_eq_sec (r : ℝ) (hr : |r| < 1) :
    (1 / 4) * (1 / Real.cos (2 * Real.arctan r)) ^ 2 = ((1 + r ^ 2) / (2 * (1 - r ^ 2))) ^ 2 := by
  have h : 1 - r ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hr, sq_abs r]
  have h2 : 1 + r ^ 2 ≠ 0 := by positivity
  rw [cos_two_arctan]
  field_simp
  norm_num

end GppSU11Prime
