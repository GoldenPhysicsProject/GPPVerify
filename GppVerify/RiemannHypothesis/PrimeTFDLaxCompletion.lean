import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Prime TFD weights, the primitive lattice, and the weighted Lax–Phillips completion target

Source: Codex, GPP-bridge `research/codex/`:
* `2026-10-03_prime_tfd_primitive_lattice_bridge.md` (commit `59bf0a2`), §§1, 3, 5;
* `2026-10-03_critical_halfdensity_lax_completion.md` (commit `8360af0`), §§1–5;
* `2026-10-03_one_correlator_lax_criterion.md` (commit `ba705b1`), §4.

**Prime TFD vacuum weights are primitive densities.** The critical TFD state at `p` has vacuum
probability `1 − 1/p`, which is the Haar measure of `ℤ_p^×`. The product over `p ∣ n` is
`φ(n)/n` (`totient_div_eq_prod`). The embedding `V|n⟩ = n^{-1/2} Σ_{(d,n)=1} |n,d⟩` has
`‖V|n⟩‖² = φ(n)/n` (`embedding_norm_sq`), so `V*V = W` on the diagonal.

**The ω-family of positive fractional weights** (§5). With `a = p^{ω−½}` and `b = p^{−ω−½}`,
the local ratio `(1 − b x)/(1 − a x)` has `k`-th coefficient
`a^{k−1}(a − b) = p^{k(ω−½)}(1 − p^{−2ω})` (`local_coeff`, and `hasSum_local_ratio` for the
expansion). So `c_ω(n) = n^{ω−½} ∏_{p∣n}(1 − p^{−2ω})`:
* `c_omega_half`: `c_{1/2}(n) = φ(n)/n`;
* `c_omega_pos`: `c_ω(n) > 0` for `ω > 0`;
* `c_omega_zero`: `c_0(n) = 0` for `n > 1`, matching `S_0 = 1`.

**The weighted Lax–Phillips reduction** (critical half-density note).
* `zero_pole_pair`: for `F(z) = ξ(½ + z)` and `S_ω(s) = F(2s − ω)/F(2s + ω)`, the zero and the
  pole coming from `ρ` sit at `c_ρ ± ω/2` with `c_ρ = (ρ − ½)/2`.
* `weighted_conjugation`: `e^{−aτ}(−d/dτ + a)(e^{aτ} f) = −f'`, i.e.
  `M_a (A_c + a) M_a^{-1} = −d/dτ`.
* `boundary_flux`: on `[L, 0]`,
  `∫ e^{−2aτ}(−2 f f') + 2a ∫ e^{−2aτ} f² = −f(0)² + e^{−2aL} f(L)²`. When the weighted tail
  vanishes as `L → −∞`, this is the note's `2 Re⟨f, (A_c + a)f⟩_a = −|f(0)|²`.
* `re_eq_zero_of_metric`: if `ηC + Cᴴη = 0` and `Re(v*ηv) > 0` for every `v ≠ 0` (e.g. `η`
  positive definite), every eigenvalue of `C` is purely imaginary. This is the finite-dimensional
  core of the note's "positive metric forces RH" step.
* `metric_shift_iff`: `Aᴴη + ηA = −½η` iff `Cᴴη + ηC = 0` with `C = A + ¼`.
* `re_eq_half_of_forall_omega`: `|Re ρ − ½| ≤ ω` for every `ω > 0` forces `Re ρ = ½`.

## Checks and corrections

Every displayed identity in the three notes was checked by hand. The coefficient formula,
`c_{1/2} = φ/n`, the pole-set shift by `a_ω = ¼ − ω/2`, the conjugation, the boundary flux,
`Re ρ ≤ 1 − 2a`, and `ζ(2s)/ζ(2s+1) = Σ φ(n) n^{−2s−1}` all hold.

Two precision notes, recorded in the PR and to Codex:
* **Beta-integral domain** (prime-TFD note §6). The Laplace form of
  `Γ(s + ¼ − ω/2)/Γ(s + ¼ + ω/2)` needs `Re(s + ¼ − ω/2) > 0` as well as `ω > 0`.
* **"Equivalent forms" (A)–(D)** (number-hologram note). These are sufficient conditions for
  RH, not equivalent ones. Under RH, a bounded positive `η` with bounded inverse making `C`
  skew-adjoint needs `C` similar to a skew-adjoint operator, which fails for Jordan blocks or
  a non-Riesz eigenbasis. The weighted `L²` bound (B) needs Paley–Wiener growth control of the
  scalar resolvent on vertical lines, which RH alone does not give. `re_eq_zero_of_metric`
  formalizes only the direction that is used: metric ⇒ imaginary spectrum.

## Scope

Finite arithmetic, one local power series, finite matrices, and a finite-interval integration by
parts. Uetake's theorem (poles of `S_{c0}` = spectrum of `A_c`), the cyclicity of the
source-observer pair, and the Hardy-space step of the one-correlator note are not formalized.
No RH claim.
-/

open Finset Matrix

namespace GppPrimeTFDLax

/-- **Primitive density as a product of local TFD vacuum probabilities.**
`φ(n)/n = ∏_{p ∣ n} (1 − 1/p)` for `n > 0`. -/
theorem totient_div_eq_prod (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  rw [h, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]

/-- **The primitive-lattice embedding.** `‖V|n⟩‖² = #{d < n : (d,n) = 1} · (n^{-1/2})² = φ(n)/n`. -/
theorem embedding_norm_sq (n : ℕ) (hn : 0 < n) :
    ((Finset.range n).filter (fun d => n.Coprime d)).card * (1 / Real.sqrt n) ^ 2 =
      (n.totient : ℝ) / n := by
  rw [← Nat.totient_eq_card_coprime, div_pow, Real.sq_sqrt (by positivity), one_pow]
  ring

/-- **Local coefficient of the ω-ratio.** With `a = p^{ω−½}` and `b = p^{−ω−½}` (`p > 0`),
`a^{k−1}(a − b) = p^{k(ω−½)}(1 − p^{−2ω})` for `k ≥ 1`. -/
theorem local_coeff (p ω : ℝ) (hp : 0 < p) (k : ℕ) :
    (p ^ (ω - 1 / 2)) ^ k * (p ^ (ω - 1 / 2) - p ^ (-ω - 1 / 2)) =
      p ^ ((k + 1 : ℕ) * (ω - 1 / 2)) * (1 - p ^ (-2 * ω)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, mul_sub, ← Real.rpow_add hp,
    ← Real.rpow_add hp, mul_sub, mul_one, ← Real.rpow_add hp]
  congr 2 <;> push_cast <;> ring_nf

/-- **The local expansion.** For `|a x| < 1`: `(1 − b x)/(1 − a x) = 1 + Σ_{k≥1} a^{k−1}(a − b) x^k`,
written with the `k = 0` term split off. -/
theorem hasSum_local_ratio (a b x : ℝ) (hax : |a * x| < 1) :
    HasSum (fun k : ℕ => a ^ k * (a - b) * x ^ (k + 1)) ((1 - b * x) / (1 - a * x) - 1) := by
  have hg := (hasSum_geometric_of_abs_lt_one hax).mul_left ((a - b) * x)
  have hne : 1 - a * x ≠ 0 := by
    intro h; have : a * x = 1 := by linarith
    rw [this, abs_one] at hax; exact lt_irrefl _ hax
  have e1 : (fun k : ℕ => a ^ k * (a - b) * x ^ (k + 1)) =
      fun k => (a - b) * x * (a * x) ^ k := by
    funext k; rw [mul_pow, pow_succ]; ring
  have e2 : (1 - b * x) / (1 - a * x) - 1 = (a - b) * x * (1 - a * x)⁻¹ := by
    rw [div_sub_one hne, div_eq_mul_inv]; ring
  rw [e1, e2]; exact hg

/-- The fractional primitive weight `c_ω(n) = n^{ω−½} ∏_{p ∣ n} (1 − p^{−2ω})`. -/
noncomputable def cOmega (ω : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (ω - 1 / 2) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-2 * ω))

/-- At `ω = ½` the weight is `φ(n)/n`. -/
theorem c_omega_half (n : ℕ) (hn : 0 < n) : cOmega (1 / 2) n = (n.totient : ℝ) / n := by
  rw [cOmega, totient_div_eq_prod n hn]
  norm_num
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Real.rpow_neg_one]

/-- `c_ω(n) > 0` for `ω > 0` and `n > 0`. -/
theorem c_omega_pos (ω : ℝ) (hω : 0 < ω) (n : ℕ) (hn : 0 < n) : 0 < cOmega ω n := by
  apply mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have : (p : ℝ) ^ (-2 * ω) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-- `c_0(n) = 0` for `n > 1`: the family collapses to `S_0 = 1`. -/
theorem c_omega_zero (n : ℕ) (hn : 1 < n) : cOmega 0 n = 0 := by
  rw [cOmega]
  apply mul_eq_zero_of_right
  obtain ⟨p, hp⟩ : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  apply Finset.prod_eq_zero hp
  simp

/-- **The zero/pole pair of `S_ω` straddles the centered resonance.** If `2s − ω = ρ − ½` then
`s = c_ρ + ω/2`; if `2s + ω = ρ − ½` then `s = c_ρ − ω/2`, with `c_ρ = (ρ − ½)/2`. -/
theorem zero_pole_pair (ρ s : ℂ) (ω : ℝ) :
    (2 * s - ω = ρ - 1 / 2 ↔ s = (ρ - 1 / 2) / 2 + ω / 2) ∧
      (2 * s + ω = ρ - 1 / 2 ↔ s = (ρ - 1 / 2) / 2 - ω / 2) := by
  constructor <;> constructor <;> intro h
  · linear_combination h / 2
  · linear_combination 2 * h
  · linear_combination h / 2
  · linear_combination 2 * h

/-- **Weighted conjugation.** If `f` has derivative `f'` at `τ`, then
`e^{−aτ} · (−(e^{a·}f)'(τ) + a e^{aτ} f(τ)) = −f'(τ)`: `M_a (A_c + a) M_a^{-1} = −d/dτ`. -/
theorem weighted_conjugation (f : ℝ → ℝ) (f' a τ : ℝ) (hf : HasDerivAt f f' τ) :
    ∃ g', HasDerivAt (fun t => Real.exp (a * t) * f t) g' τ ∧
      Real.exp (-(a * τ)) * (-g' + a * (Real.exp (a * τ) * f τ)) = -f' := by
  have he : HasDerivAt (fun t => Real.exp (a * t)) (Real.exp (a * τ) * a) τ := by
    simpa using ((hasDerivAt_id τ).const_mul a).exp
  refine ⟨_, he.mul hf, ?_⟩
  have h1 : Real.exp (-(a * τ)) * Real.exp (a * τ) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-f') * h1

/-- **The boundary flux identity on `[L, 0]`.** For `C¹` real `f`,
`∫_L^0 e^{−2aτ}(−2 f f') + 2a ∫_L^0 e^{−2aτ} f² = −f(0)² + e^{−2aL} f(L)²`. -/
theorem boundary_flux (f f' : ℝ → ℝ) (a L : ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') :
    (∫ τ in L..0, Real.exp (-2 * a * τ) * (-2 * f τ * f' τ)) +
        2 * a * ∫ τ in L..0, Real.exp (-2 * a * τ) * f τ ^ 2 =
      -f 0 ^ 2 + Real.exp (-2 * a * L) * f L ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  set g : ℝ → ℝ := fun τ => Real.exp (-2 * a * τ) * f τ ^ 2
  set g' : ℝ → ℝ := fun τ =>
    Real.exp (-2 * a * τ) * (-2 * a) * f τ ^ 2 + Real.exp (-2 * a * τ) * (2 * f τ * f' τ)
  have hg : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have he : HasDerivAt (fun t => Real.exp (-2 * a * t)) (Real.exp (-2 * a * x) * (-2 * a)) x := by
      simpa using ((hasDerivAt_id x).const_mul (-2 * a)).exp
    have hsq : HasDerivAt (fun t => f t ^ 2) (2 * f x * f' x) x := by
      have h := (hf x).pow 2
      simp only [Nat.cast_ofNat, pow_one, show (2 : ℕ) - 1 = 1 from rfl] at h
      exact h
    exact he.mul hsq
  have hgc : Continuous g' := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
    (hgc.intervalIntegrable L 0)
  have i1 : IntervalIntegrable (fun τ => Real.exp (-2 * a * τ) * (-2 * a) * f τ ^ 2)
      MeasureTheory.volume L 0 := by apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun τ => Real.exp (-2 * a * τ) * (2 * f τ * f' τ))
      MeasureTheory.volume L 0 := by apply Continuous.intervalIntegrable; fun_prop
  simp only [g', g] at hint
  rw [intervalIntegral.integral_add i1 i2] at hint
  have e1 : (∫ τ in L..0, Real.exp (-2 * a * τ) * (-2 * a) * f τ ^ 2) =
      -2 * a * ∫ τ in L..0, Real.exp (-2 * a * τ) * f τ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext τ; ring
  have e2 : (∫ τ in L..0, Real.exp (-2 * a * τ) * (-2 * f τ * f' τ)) =
      -∫ τ in L..0, Real.exp (-2 * a * τ) * (2 * f τ * f' τ) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext τ; ring
  rw [e1] at hint
  rw [e2]
  simp only [mul_zero, Real.exp_zero, one_mul] at hint
  linarith

/-- **A positive metric forces imaginary spectrum.** If `Cᴴη + ηC = 0`, `Re(v*ηv) > 0` for all
`v ≠ 0`, and `C v = λ v` with `v ≠ 0`, then `Re λ = 0`. -/
theorem re_eq_zero_of_metric {n : Type*} [Fintype n] (C η : Matrix n n ℂ)
    (hη : ∀ v : n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (η *ᵥ v)).re)
    (hskew : C.conjTranspose * η + η * C = 0) (lam : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (hCv : C *ᵥ v = lam • v) : lam.re = 0 := by
  set q := star v ⬝ᵥ (η *ᵥ v)
  have h0 : star v ⬝ᵥ ((C.conjTranspose * η + η * C) *ᵥ v) = 0 := by
    rw [hskew, Matrix.zero_mulVec, dotProduct_zero]
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCv,
    Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hCv,
    star_smul, smul_dotProduct] at h0
  simp only [smul_eq_mul] at h0
  have h2 : (star lam + lam) * q = 0 := by rw [add_mul]; exact h0
  have hq : q ≠ 0 := by
    intro h; have := hη v hv; rw [show star v ⬝ᵥ (η *ᵥ v) = q from rfl, h] at this; simp at this
  have h3 : star lam + lam = 0 := (mul_eq_zero.mp h2).resolve_right hq
  have := congrArg Complex.re h3
  simp at this
  linarith

/-- `Aᴴη + ηA = −½η` iff `Cᴴη + ηC = 0` for `C = A + ¼`. -/
theorem metric_shift_iff {n : Type*} [Fintype n] [DecidableEq n] (A η : Matrix n n ℂ) :
    A.conjTranspose * η + η * A = -(1 / 2 : ℂ) • η ↔
      (A + (1 / 4 : ℂ) • 1).conjTranspose * η + η * (A + (1 / 4 : ℂ) • 1) = 0 := by
  have hc : ((1 / 4 : ℂ) • (1 : Matrix n n ℂ)).conjTranspose = (1 / 4 : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]; norm_num
  rw [Matrix.conjTranspose_add, hc, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro h
    rw [show A.conjTranspose * η + (1 / 4 : ℂ) • η + (η * A + (1 / 4 : ℂ) • η) =
      (A.conjTranspose * η + η * A) + (1 / 2 : ℂ) • η by
        rw [show (1 / 2 : ℂ) = 1 / 4 + 1 / 4 by norm_num, add_smul]; abel, h]
    simp
  · intro h
    have : A.conjTranspose * η + η * A = -(1 / 2 : ℂ) • η +
        (A.conjTranspose * η + (1 / 4 : ℂ) • η + (η * A + (1 / 4 : ℂ) • η)) := by
      rw [show (1 / 2 : ℂ) = 1 / 4 + 1 / 4 by norm_num, neg_smul, add_smul]; abel
    rw [this, h, add_zero]

/-- **Fixed-ω control for every ω forces the line.** -/
theorem re_eq_half_of_forall_omega (x : ℝ) (h : ∀ ω : ℝ, 0 < ω → |x - 1 / 2| ≤ ω) :
    x = 1 / 2 := by
  by_contra hx
  have hpos : 0 < |x - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have := h (|x - 1 / 2| / 2) (by positivity)
  linarith

end GppPrimeTFDLax
