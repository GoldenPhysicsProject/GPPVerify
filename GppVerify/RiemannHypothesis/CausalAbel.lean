/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Floor
import GppVerify.RiemannHypothesis.CausalKernels

/-!
# Abel summation for the causal kernels (Part D1 of the causal proof of `EnergyZeroInequality`)

**Unconditional; this is a lemma, not RH.** Part D1 of the four-part formalization of Codex's causal
proof (`causal_zero_bound.md` §3, GPPDiscovery2 `cae0656`, Turbo-audited): the closed forms for `Z`
and `k` that feed the norm bounds. The norm bounds themselves (`‖Z‖₂ ≤ 9`, `‖w‖₂ ≤ 5/2`, `‖k‖₁ ≤ 18`)
are Part D2 and are **not** in this file.

With `f(u) = e^{−u/2}{e^u}` (`ff`) and the kernels of `GppCausalKernels`:

* `Z_formula`: `Z(t) = g₃(t) − g₄(t)/2 − ∫₀ᵗ f(u) u₁(t − u) du`, `u₁ = g₂ − 2g₃ + (3/4)g₄`
  (polynomial form `u1`);
* `kk_formula`: `k(t) = g₂(t) − (3/2)g₃(t) + g₄(t)/2 − ∫₀ᵗ f(u) u₂(t − u) du`,
  `u₂ = g₁ − 3g₂ + (11/4)g₃ − (3/4)g₄` (polynomial form `u2`).

Both follow from one general statement, `euler_phi`: for `φ` differentiable with continuous
derivative `φ'` and `φ(0) = 0`, `Σ_{n ≤ e^t} φ(t − log n)/√n = φ(t) + ∫₀ᵗ e^{u/2} φ(t−u) du
− ∫₀ᵗ f(u)(φ' + φ/2)(t−u) du` (Euler's summation formula, from Mathlib's
`sum_mul_eq_sub_sub_integral_mul` with the substitution `s = e^u`), applied to `φ = w` and `φ = w′`
in polynomial-times-exponential form (`Pw`, `Pd`, `Pdd`), together with the closed forms
`∫₀ᵗ e^{u/2} w(t−u) du = g₄(t)` and `∫₀ᵗ e^{u/2} w′(t−u) du = g₃(t) − g₄(t)` (`Ew_closed`, `Ed_closed`).
No distribution API; every sum is a finite sum.
-/

open MeasureTheory Set GppCausalKernels

namespace GppCausalAbel

/-- Abel summation for the unit counting sequence, from `a = 1`:
`Σ_{k=1}^{⌊b⌋} ψ(k) = ψ(b)⌊b⌋ − ∫₁ᵇ ψ′(s) ⌊s⌋ ds`-type formula (before splitting off `ψ(1)`). -/
theorem abel_unit (ψ : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hd : ∀ s ∈ Icc (1:ℝ) b, DifferentiableAt ℝ ψ s)
    (hi : IntegrableOn (deriv ψ) (Icc (1:ℝ) b)) :
    ∑ k ∈ Finset.Icc 1 ⌊b⌋₊, ψ k =
      ψ b * ⌊b⌋₊ - ∫ s in Ioc (1:ℝ) b, deriv ψ s * (⌊s⌋₊ : ℝ) := by
  have h := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => if k = 0 then (0:ℝ) else 1)
    (f := ψ) (a := 1) (b := b) zero_le_one hb hd hi
  simp only [Nat.floor_one] at h
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, (if k = 0 then (0:ℝ) else 1) = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_Icc_succ_top (Nat.zero_le _), ih]; simp
  have hN : 1 ≤ ⌊b⌋₊ := Nat.le_floor (by simpa using hb)
  have hcons : Finset.Icc 1 ⌊b⌋₊ = insert 1 (Finset.Ioc 1 ⌊b⌋₊) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hcons, Finset.sum_insert (by simp)]
  have h2 : ∑ k ∈ Finset.Ioc 1 ⌊b⌋₊, ψ k = ∑ k ∈ Finset.Ioc 1 ⌊b⌋₊, ψ k * (if k = 0 then (0:ℝ) else 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by have := (Finset.mem_Ioc.1 hk).1; omega
    simp [this]
  rw [h2, h, hsum, hsum]
  have h3 : ∀ t : ℝ, deriv ψ t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then (0:ℝ) else 1) =
      deriv ψ t * (⌊t⌋₊ : ℝ) := fun t => by rw [hsum]
  simp_rw [h3]
  simp only [Nat.cast_one]
  ring


/-- Euler's summation formula (in the variable `s`), with an explicit continuous derivative `ψ'`:
`Σ_{k=1}^{⌊b⌋} ψ(k) = ψ(1) + ∫₁ᵇ ψ + ∫₁ᵇ ψ' · fract − fract(b) ψ(b)`. -/
theorem euler_sum (ψ ψ' : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hψ : ∀ s ∈ Icc (1:ℝ) b, HasDerivAt ψ (ψ' s) s) (hc : ContinuousOn ψ' (Icc (1:ℝ) b)) :
    ∑ k ∈ Finset.Icc 1 ⌊b⌋₊, ψ k =
      ψ 1 + (∫ s in Ioc (1:ℝ) b, ψ s) + (∫ s in Ioc (1:ℝ) b, ψ' s * Int.fract s)
        - Int.fract b * ψ b := by
  have hdv : ∀ s ∈ Icc (1:ℝ) b, deriv ψ s = ψ' s := fun s hs => (hψ s hs).deriv
  have hI : IntegrableOn ψ' (Icc (1:ℝ) b) := hc.integrableOn_Icc
  have hI' : IntegrableOn (deriv ψ) (Icc (1:ℝ) b) := hI.congr_fun (fun s hs => (hdv s hs).symm) measurableSet_Icc
  have hcont : ContinuousOn ψ (Icc (1:ℝ) b) := fun s hs => (hψ s hs).continuousAt.continuousWithinAt
  rw [abel_unit ψ hb (fun s hs => (hψ s hs).differentiableAt) hI']
  -- replace `deriv ψ` by `ψ'` on `Ioc 1 b`
  have hrep : ∫ s in Ioc (1:ℝ) b, deriv ψ s * (⌊s⌋₊ : ℝ) = ∫ s in Ioc (1:ℝ) b, ψ' s * (⌊s⌋₊ : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by rw [hdv s ⟨hs.1.le, hs.2⟩]
  rw [hrep]
  -- ⌊s⌋₊ = s - fract s
  have hfl : ∀ s : ℝ, 0 ≤ s → (⌊s⌋₊ : ℝ) = s - Int.fract s := by
    intro s hs
    rw [Int.fract, natCast_floor_eq_intCast_floor hs]; ring
  have hsplit : ∫ s in Ioc (1:ℝ) b, ψ' s * (⌊s⌋₊ : ℝ) =
      (∫ s in Ioc (1:ℝ) b, ψ' s * s) - ∫ s in Ioc (1:ℝ) b, ψ' s * Int.fract s := by
    have hm : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
    have h1 : IntegrableOn (fun s => ψ' s * s) (Ioc (1:ℝ) b) :=
      (hc.mul continuousOn_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun s => ψ' s * Int.fract s) (Ioc (1:ℝ) b) := by
      refine (hI.mono_set Ioc_subset_Icc_self).mul_bdd (c := 1) ?_ ?_
      · exact hm.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg s)]; exact (Int.fract_lt_one s).le
    rw [← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [hfl s (by linarith [hs.1])]; ring
  rw [hsplit]
  -- ∫ s ψ' = bψ(b) - ψ(1) - ∫ ψ   (product rule)
  have hprod : ∫ s in Ioc (1:ℝ) b, ψ' s * s = b * ψ b - ψ 1 - ∫ s in Ioc (1:ℝ) b, ψ s := by
    have hF : ∀ s ∈ uIcc (1:ℝ) b, HasDerivAt (fun s => s * ψ s) (ψ s + s * ψ' s) s := by
      intro s hs
      rw [uIcc_of_le hb] at hs
      refine ((hasDerivAt_id' s).mul (hψ s hs)).congr_deriv ?_
      ring
    have hcc : ContinuousOn (fun s => ψ s + s * ψ' s) (Icc (1:ℝ) b) :=
      hcont.add (continuousOn_id.mul hc)
    have hint : IntervalIntegrable (fun s => ψ s + s * ψ' s) volume 1 b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2 hcc.integrableOn_Icc
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
    rw [intervalIntegral.integral_of_le hb] at hftc
    have hi1 : IntegrableOn ψ (Ioc (1:ℝ) b) := (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hi2 : IntegrableOn (fun s => s * ψ' s) (Ioc (1:ℝ) b) :=
      ((continuousOn_id.mul hc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [integral_add hi1 hi2] at hftc
    have : ∫ s in Ioc (1:ℝ) b, ψ' s * s = ∫ s in Ioc (1:ℝ) b, s * ψ' s :=
      setIntegral_congr_fun measurableSet_Ioc fun s _ => by ring
    rw [this]
    simp only [one_mul] at hftc
    linarith
  rw [hprod]
  have hfb : (⌊b⌋₊ : ℝ) = b - Int.fract b := hfl b (by linarith)
  rw [hfb]
  ring


/-- Substitution `s = e^u`: `∫_{(1, e^t]} g(s) ds = ∫_{(0, t]} e^u g(e^u) du`. -/
theorem integral_Ioc_exp (g : ℝ → ℝ) (t : ℝ) :
    ∫ s in Ioc (1:ℝ) (Real.exp t), g s = ∫ u in Ioc (0:ℝ) t, Real.exp u * g (Real.exp u) := by
  have himg : Real.exp '' Ioc (0:ℝ) t = Ioc 1 (Real.exp t) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa using Real.exp_lt_exp.2 hx.1, Real.exp_le_exp.2 hx.2⟩
    · intro hy
      have hy0 : 0 < y := by linarith [hy.1]
      refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy0⟩
      · exact Real.log_pos hy.1
      · calc Real.log y ≤ Real.log (Real.exp t) := Real.log_le_log hy0 hy.2
          _ = t := Real.log_exp t
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp [abs_of_pos (Real.exp_pos x)]


theorem hasDerivAt_psi (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x) (t : ℝ) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (fun s => φ (t - Real.log s) / Real.sqrt s)
      (-(φ' (t - Real.log s) + φ (t - Real.log s) / 2) / (s * Real.sqrt s)) s := by
  have hA : HasDerivAt (fun s => φ (t - Real.log s)) (φ' (t - Real.log s) * (-(s⁻¹))) s :=
    (hφ _).comp s ((Real.hasDerivAt_log hs.ne').const_sub t)
  have hS : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  refine (hA.div hS hsq.ne').congr_deriv ?_
  have hss2 : Real.sqrt s ^ 2 = s := by rw [sq]; exact hss
  field_simp
  rw [hss2]
  ring


theorem sqrt_exp_eq (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  have : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this, Real.sqrt_sq (Real.exp_pos _).le]

/-- **Euler summation for the kernel sums.** For `φ` differentiable with continuous derivative `φ'`
and `φ(0) = 0`, and `t ≥ 0`:
`Σ_{n ≤ e^t} φ(t − log n)/√n = φ(t) + ∫₀ᵗ e^{u/2} φ(t−u) du − ∫₀ᵗ e^{−u/2}{e^u}(φ' + φ/2)(t−u) du`. -/
theorem euler_phi (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (h0 : φ 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, φ (t - Real.log n) / Real.sqrt n =
      φ t + (∫ u in Ioc (0:ℝ) t, Real.exp (u / 2) * φ (t - u))
        - ∫ u in Ioc (0:ℝ) t, (Real.exp (-u / 2) * Int.fract (Real.exp u)) *
            (φ' (t - u) + φ (t - u) / 2) := by
  have hb : 1 ≤ Real.exp t := Real.one_le_exp ht
  set ψ : ℝ → ℝ := fun s => φ (t - Real.log s) / Real.sqrt s with hψdef
  set ψ' : ℝ → ℝ := fun s =>
    -(φ' (t - Real.log s) + φ (t - Real.log s) / 2) / (s * Real.sqrt s) with hψ'def
  have hd : ∀ s ∈ Icc (1:ℝ) (Real.exp t), HasDerivAt ψ (ψ' s) s :=
    fun s hs => hasDerivAt_psi φ φ' hφ t (by linarith [hs.1])
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hc : ContinuousOn ψ' (Icc (1:ℝ) (Real.exp t)) := by
    have hlog : ContinuousOn (fun s : ℝ => Real.log s) (Icc 1 (Real.exp t)) :=
      Real.continuousOn_log.mono fun s hs => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [hs.1]
    have hnum : ContinuousOn (fun s : ℝ => -(φ' (t - Real.log s) + φ (t - Real.log s) / 2))
        (Icc 1 (Real.exp t)) := by
      have h1 : ContinuousOn (fun s : ℝ => t - Real.log s) (Icc 1 (Real.exp t)) :=
        continuousOn_const.sub hlog
      exact ((hφ'.comp_continuousOn h1).add ((hφc.comp_continuousOn h1).div_const 2)).neg
    have hden : ContinuousOn (fun s : ℝ => s * Real.sqrt s) (Icc 1 (Real.exp t)) :=
      continuousOn_id.mul Real.continuous_sqrt.continuousOn
    exact hnum.div hden fun s hs => by
      have : 0 < s := by linarith [hs.1]
      positivity
  have hE := euler_sum ψ ψ' hb hd hc
  have hψ1 : ψ 1 = φ t := by simp [hψdef]
  have hψb : ψ (Real.exp t) = 0 := by simp [hψdef, h0]
  rw [hψ1, hψb, mul_zero, sub_zero] at hE
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, φ (t - Real.log n) / Real.sqrt n =
      ∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, ψ k := rfl
  rw [hsum, hE]
  have i1 : ∫ s in Ioc (1:ℝ) (Real.exp t), ψ s = ∫ u in Ioc (0:ℝ) t, Real.exp (u / 2) * φ (t - u) := by
    rw [integral_Ioc_exp]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [hψdef, Real.log_exp, sqrt_exp_eq]
    have : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by rw [← Real.exp_add]; ring_nf
    have hp : 0 < Real.exp (u / 2) := Real.exp_pos _
    rw [this]; field_simp
  have i2 : ∫ s in Ioc (1:ℝ) (Real.exp t), ψ' s * Int.fract s =
      -∫ u in Ioc (0:ℝ) t, (Real.exp (-u / 2) * Int.fract (Real.exp u)) *
            (φ' (t - u) + φ (t - u) / 2) := by
    rw [integral_Ioc_exp (fun s => ψ' s * Int.fract s), ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [hψ'def, Real.log_exp, sqrt_exp_eq]
    have hu : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by rw [← Real.exp_add]; ring_nf
    have hp : 0 < Real.exp (u / 2) := Real.exp_pos _
    have hm : Real.exp (-u / 2) = (Real.exp (u / 2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
    rw [hm, hu]; field_simp
  rw [i1, i2]
  ring


/-- Polynomial-times-exponential forms, valid for all real arguments. -/
noncomputable def Pw (t : ℝ) : ℝ := Real.exp (-t) * (t ^ 2 / 2 - t ^ 3 / 4)
noncomputable def Pd (t : ℝ) : ℝ := Real.exp (-t) * (t - 5 / 4 * t ^ 2 + t ^ 3 / 4)
noncomputable def Pdd (t : ℝ) : ℝ := Real.exp (-t) * (1 - 7 / 2 * t + 2 * t ^ 2 - t ^ 3 / 4)

theorem hasDerivAt_exp_neg_mul_poly (Q : ℝ → ℝ) (d x : ℝ) (hQ : HasDerivAt Q d x) :
    HasDerivAt (fun t => Real.exp (-t) * Q t) (Real.exp (-x) * (d - Q x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    refine (hasDerivAt_neg x).exp.congr_deriv ?_
    ring
  refine (h1.mul hQ).congr_deriv ?_
  ring

theorem hasDerivAt_Pw (x : ℝ) : HasDerivAt Pw (Pd x) x := by
  have hQ : HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 4) (x - 3 / 4 * x ^ 2) x := by
    refine (((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 4)).congr_deriv ?_
    push_cast; ring
  refine (hasDerivAt_exp_neg_mul_poly _ _ x hQ).congr_deriv ?_
  simp only [Pd]; ring

theorem hasDerivAt_Pd (x : ℝ) : HasDerivAt Pd (Pdd x) x := by
  have hQ : HasDerivAt (fun t : ℝ => t - 5 / 4 * t ^ 2 + t ^ 3 / 4) (1 - 5 / 2 * x + 3 / 4 * x ^ 2) x := by
    have := ((hasDerivAt_id x).sub (((hasDerivAt_pow 2 x).const_mul (5 / 4)))).add
      ((hasDerivAt_pow 3 x).div_const 4)
    refine this.congr_deriv ?_
    push_cast; simp; ring
  refine (hasDerivAt_exp_neg_mul_poly _ _ x hQ).congr_deriv ?_
  simp only [Pdd]; ring

theorem continuous_Pd : Continuous Pd := by unfold Pd; fun_prop
theorem continuous_Pdd : Continuous Pdd := by unfold Pdd; fun_prop
theorem Pw_zero : Pw 0 = 0 := by simp [Pw]
theorem Pd_zero : Pd 0 = 0 := by simp [Pd]

theorem w_eq_Pw {x : ℝ} (hx : 0 ≤ x) : w x = Pw x := w_of_nonneg hx
theorem wd_eq_Pd {x : ℝ} (hx : 0 ≤ x) : wd x = Pd x := wd_of_nonneg hx


/-- `∫₀ᵗ e^{u/2} P(t−u) du = ∫₀ᵗ e^{(t−v)/2} P(v) dv` (reflection `v = t − u`). -/
theorem reflect_exp (P : ℝ → ℝ) (t : ℝ) :
    ∫ u in (0:ℝ)..t, Real.exp (u / 2) * P (t - u) =
      ∫ v in (0:ℝ)..t, Real.exp ((t - v) / 2) * P v := by
  have := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun v => Real.exp ((t - v) / 2) * P v) t
  simp only [sub_sub_cancel, sub_self, sub_zero] at this
  exact this

theorem Ew_closed {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in Ioc (0:ℝ) t, Real.exp (u / 2) * Pw (t - u) = Real.exp (-t) * t ^ 3 / 6 := by
  rw [← intervalIntegral.integral_of_le ht, reflect_exp]
  have hd : ∀ v ∈ uIcc (0:ℝ) t, HasDerivAt
      (fun v => Real.exp (t / 2) * (Real.exp (-(3 / 2 * v)) * v ^ 3 / 6))
      (Real.exp ((t - v) / 2) * Pw v) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => Real.exp (-(3 / 2 * v))) (Real.exp (-(3 / 2 * v)) * (-(3 / 2))) v := by
      have := ((hasDerivAt_id v).const_mul (3 / 2)).neg.exp
      simpa using this
    have h2 := ((h1.mul (hasDerivAt_pow 3 v)).div_const 6).const_mul (Real.exp (t / 2))
    refine h2.congr_deriv ?_
    have e1 : Real.exp ((t - v) / 2) = Real.exp (t / 2) * Real.exp (-(v / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(v / 2)) * Real.exp (-v) = Real.exp (-(3 / 2 * v)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [Pw]
    rw [e1, ← e2]
    push_cast
    ring
  have hint : IntervalIntegrable (fun v => Real.exp ((t - v) / 2) * Pw v) volume 0 t := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold Pw; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have e3 : Real.exp (t / 2) * Real.exp (-(3 / 2 * t)) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [mul_zero, zero_pow (by norm_num : (3:ℕ) ≠ 0)]
  rw [← e3]; ring


theorem Ed_closed {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in Ioc (0:ℝ) t, Real.exp (u / 2) * Pd (t - u) =
      Real.exp (-t) * (t ^ 2 / 2 - t ^ 3 / 6) := by
  rw [← intervalIntegral.integral_of_le ht, reflect_exp]
  have hd : ∀ v ∈ uIcc (0:ℝ) t, HasDerivAt
      (fun v => Real.exp (t / 2) * (Real.exp (-(3 / 2 * v)) * (v ^ 2 / 2 - v ^ 3 / 6)))
      (Real.exp ((t - v) / 2) * Pd v) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => Real.exp (-(3 / 2 * v))) (Real.exp (-(3 / 2 * v)) * (-(3 / 2))) v := by
      have := ((hasDerivAt_id v).const_mul (3 / 2)).neg.exp
      simpa using this
    have hq : HasDerivAt (fun v : ℝ => v ^ 2 / 2 - v ^ 3 / 6) (v - v ^ 2 / 2) v := by
      refine (((hasDerivAt_pow 2 v).div_const 2).sub ((hasDerivAt_pow 3 v).div_const 6)).congr_deriv ?_
      push_cast; ring
    have h2 := (h1.mul hq).const_mul (Real.exp (t / 2))
    refine h2.congr_deriv ?_
    have e1 : Real.exp ((t - v) / 2) = Real.exp (t / 2) * Real.exp (-(v / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(v / 2)) * Real.exp (-v) = Real.exp (-(3 / 2 * v)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [Pd]
    rw [e1, ← e2]
    ring
  have hint : IntervalIntegrable (fun v => Real.exp ((t - v) / 2) * Pd v) volume 0 t := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold Pd; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have e3 : Real.exp (t / 2) * Real.exp (-(3 / 2 * t)) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_pow (by norm_num : (3:ℕ) ≠ 0)]
  rw [← e3]; ring


theorem g2_of_nonneg {t : ℝ} (ht : 0 ≤ t) : g 2 t = Real.exp (-t) * t := by
  simp [g, ht]

theorem g3_of_nonneg {t : ℝ} (ht : 0 ≤ t) : g 3 t = Real.exp (-t) * (t ^ 2 / 2) := by
  simp only [g, if_pos ht]; norm_num [Nat.factorial]; ring

theorem g4_of_nonneg {t : ℝ} (ht : 0 ≤ t) : g 4 t = Real.exp (-t) * (t ^ 3 / 6) := by
  simp only [g, if_pos ht]; norm_num [Nat.factorial]; ring

/-- The weight `f(u) = e^{−u/2} {e^u}` of the Abel-summation remainder. -/
noncomputable def ff (u : ℝ) : ℝ := Real.exp (-u / 2) * Int.fract (Real.exp u)

/-- `u₁ = g₂ − 2 g₃ + (3/4) g₄` on `[0, ∞)`, in polynomial form. -/
noncomputable def u1 (x : ℝ) : ℝ := Real.exp (-x) * (x - x ^ 2 + x ^ 3 / 8)

/-- `u₂ = g₁ − 3 g₂ + (11/4) g₃ − (3/4) g₄` on `[0, ∞)`, in polynomial form. -/
noncomputable def u2 (x : ℝ) : ℝ := Real.exp (-x) * (1 - 3 * x + 11 / 8 * x ^ 2 - x ^ 3 / 8)

/-- **Abel-summation formula for `Z`** (§3 of the note):
`Z(t) = g₃(t) − g₄(t)/2 − ∫₀ᵗ f(u) u₁(t − u) du`. -/
theorem Z_formula {t : ℝ} (ht : 0 ≤ t) :
    Z t = g 3 t - g 4 t / 2 - ∫ u in Ioc (0:ℝ) t, ff u * u1 (t - u) := by
  have hsum : Z t = ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, Pw (t - Real.log n) / Real.sqrt n := by
    unfold Z nuConv
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).1 (Finset.mem_Icc.1 hn).2
    have : Real.log n ≤ t := by
      calc Real.log n ≤ Real.log (Real.exp t) := Real.log_le_log hnpos hnN
        _ = t := Real.log_exp t
    rw [w_eq_Pw (by linarith)]
  rw [hsum, euler_phi Pw Pd hasDerivAt_Pw continuous_Pd Pw_zero ht, Ew_closed ht,
    g3_of_nonneg ht, g4_of_nonneg ht]
  have : (∫ u in Ioc (0:ℝ) t, (Real.exp (-u / 2) * Int.fract (Real.exp u)) * (Pd (t - u) + Pw (t - u) / 2)) =
      ∫ u in Ioc (0:ℝ) t, ff u * u1 (t - u) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [ff, u1, Pd, Pw]; ring
  rw [this]
  simp only [Pw]
  ring

/-- **Abel-summation formula for `k`**:
`k(t) = g₂(t) − (3/2) g₃(t) + g₄(t)/2 − ∫₀ᵗ f(u) u₂(t − u) du`. -/
theorem kk_formula {t : ℝ} (ht : 0 ≤ t) :
    kk t = g 2 t - 3 / 2 * g 3 t + g 4 t / 2 - ∫ u in Ioc (0:ℝ) t, ff u * u2 (t - u) := by
  have hsum : kk t = ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, Pd (t - Real.log n) / Real.sqrt n := by
    unfold kk nuConv
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).1 (Finset.mem_Icc.1 hn).2
    have : Real.log n ≤ t := by
      calc Real.log n ≤ Real.log (Real.exp t) := Real.log_le_log hnpos hnN
        _ = t := Real.log_exp t
    rw [wd_eq_Pd (by linarith)]
  rw [hsum, euler_phi Pd Pdd hasDerivAt_Pd continuous_Pdd Pd_zero ht, Ed_closed ht,
    g2_of_nonneg ht, g3_of_nonneg ht, g4_of_nonneg ht]
  have : (∫ u in Ioc (0:ℝ) t, (Real.exp (-u / 2) * Int.fract (Real.exp u)) * (Pdd (t - u) + Pd (t - u) / 2)) =
      ∫ u in Ioc (0:ℝ) t, ff u * u2 (t - u) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [ff, u2, Pdd, Pd]; ring
  rw [this]
  simp only [Pd]
  ring


end GppCausalAbel
