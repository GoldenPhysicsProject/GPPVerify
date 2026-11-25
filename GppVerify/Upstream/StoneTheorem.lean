/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Stone's theorem

A strongly continuous one-parameter group of isometries of a complex Hilbert space has a
self-adjoint generator.

## Main definitions

* `StronglyContinuousUnitaryGroup E`: a family `U t : E →ₗᵢ[ℂ] E`, `t : ℝ`, with `U 0 = 1`,
  `U (s + t) = U s ∘ U t`, and `t ↦ U t x` continuous for every `x`.
* `StronglyContinuousUnitaryGroup.generator`: the generator `A`, a `LinearPMap`, defined by
  `U t x = exp (i t A) x`, that is `A x = -i * d/dt (U t x) |_{t = 0}` on the domain where the
  derivative exists.

## Main results

* `StronglyContinuousUnitaryGroup.isSelfAdjoint_generator`: the generator is self-adjoint.
-/

open Filter Topology MeasureTheory Set intervalIntegral
open scoped InnerProductSpace ComplexConjugate

noncomputable section

/-- A strongly continuous one-parameter group of isometries (a unitary group) of `E`. -/
structure StronglyContinuousUnitaryGroup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  /-- The isometry at time `t`. -/
  toFun : ℝ → E →ₗᵢ[ℂ] E
  map_zero' : ∀ x, toFun 0 x = x
  map_add' : ∀ s t x, toFun (s + t) x = toFun s (toFun t x)
  continuous' : ∀ x, Continuous fun t => toFun t x

namespace StronglyContinuousUnitaryGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : StronglyContinuousUnitaryGroup E)

instance : CoeFun (StronglyContinuousUnitaryGroup E) (fun _ => ℝ → E →ₗᵢ[ℂ] E) := ⟨toFun⟩

@[simp] theorem map_zero (x : E) : U 0 x = x := U.map_zero' x

theorem map_add (s t : ℝ) (x : E) : U (s + t) x = U s (U t x) := U.map_add' s t x

theorem comm (s t : ℝ) (x : E) : U s (U t x) = U t (U s x) := by
  rw [← U.map_add, ← U.map_add, add_comm]

theorem continuous (x : E) : Continuous fun t => U t x := U.continuous' x

theorem norm_map (t : ℝ) (x : E) : ‖U t x‖ = ‖x‖ := (U t).norm_map x

theorem inner_map (t : ℝ) (x y : E) : ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ := (U t).inner_map_map x y

/-- The set of vectors at which `t ↦ U t x` is differentiable at `0`. -/
def domain : Submodule ℂ E where
  carrier := {x | ∃ y, HasDerivAt (fun t => U t x) y 0}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (fun t => U t (x + y)) = fun t => U t x + U t y := by funext t; simp
    rw [this]; exact ha.add hb
  zero_mem' := ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : E)⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    refine ⟨c • a, ?_⟩
    have : (fun t => U t (c • x)) = fun t => c • U t x := by funext t; simp
    rw [this]; exact ha.const_smul c

theorem mem_domain {x : E} : x ∈ U.domain ↔ ∃ y, HasDerivAt (fun t => U t x) y 0 := Iff.rfl


/-- The derivative at `0` of `t ↦ U t x`. -/
def dU (x : E) : E := deriv (fun t => U t x) 0

variable {U}

theorem hasDerivAt_dU {x : E} (hx : x ∈ U.domain) : HasDerivAt (fun t => U t x) (U.dU x) 0 := by
  obtain ⟨y, hy⟩ := hx
  rw [dU, hy.deriv]; exact hy

theorem dU_add {x y : E} (hx : x ∈ U.domain) (hy : y ∈ U.domain) :
    U.dU (x + y) = U.dU x + U.dU y := by
  have h1 := hasDerivAt_dU (U.domain.add_mem hx hy)
  have h2 : HasDerivAt (fun t => U t (x + y)) (U.dU x + U.dU y) 0 := by
    have : (fun t => U t (x + y)) = fun t => U t x + U t y := by funext t; simp
    rw [this]; exact (hasDerivAt_dU hx).add (hasDerivAt_dU hy)
  exact h1.unique h2

theorem dU_smul (c : ℂ) {x : E} (hx : x ∈ U.domain) : U.dU (c • x) = c • U.dU x := by
  have h1 := hasDerivAt_dU (U.domain.smul_mem c hx)
  have h2 : HasDerivAt (fun t => U t (c • x)) (c • U.dU x) 0 := by
    have : (fun t => U t (c • x)) = fun t => c • U t x := by funext t; simp
    rw [this]; exact (hasDerivAt_dU hx).const_smul c
  exact h1.unique h2

variable (U)

/-- The generator `A` of the group, `U t = exp (i t A)`: `A x = -i * d/dt (U t x) |_{t = 0}`, on the
domain where the derivative exists. -/
def generator : E →ₗ.[ℂ] E where
  domain := U.domain
  toFun :=
    { toFun := fun x => (-Complex.I) • U.dU x
      map_add' := fun x y => by
        rw [show ((x + y : U.domain) : E) = x + y from rfl, dU_add x.2 y.2, smul_add]
      map_smul' := fun c x => by
        rw [show ((c • x : U.domain) : E) = c • (x : E) from rfl, dU_smul c x.2, RingHom.id_apply,
          smul_comm] }

variable {U}

theorem generator_domain : U.generator.domain = U.domain := rfl

theorem generator_apply (x : U.domain) : U.generator x = (-Complex.I) • U.dU x := rfl

/-- On the domain, the derivative of the orbit at `0` is `i A x`. -/
theorem hasDerivAt_generator (x : U.domain) :
    HasDerivAt (fun t => U t x) (Complex.I • U.generator x) 0 := by
  rw [generator_apply, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  exact hasDerivAt_dU x.2

/-- The orbit of a domain vector is differentiable at every time, with derivative `U t (d x)`. -/
theorem hasDerivAt_orbit {x : E} (hx : x ∈ U.domain) (t : ℝ) :
    HasDerivAt (fun s => U s x) (U t (U.dU x)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) x) (U.dU x) t := by
    have := hasDerivAt_dU hx
    rw [← sub_self t] at this
    exact this.comp_sub_const t t
  have h2 := ((U t).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  have : (fun s => U s x) = fun s => U t (U (s - t) x) := by
    funext s; rw [← U.map_add]; congr 2; ring
  rw [this]; exact h2

theorem domain_invariant {x : E} (hx : x ∈ U.domain) (t : ℝ) : U t x ∈ U.domain := by
  refine ⟨U t (U.dU x), ?_⟩
  have h1 := hasDerivAt_dU hx
  have h2 := ((U t).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have : (fun s => U s (U t x)) = fun s => U t (U s x) := by funext s; exact U.comm s t x
  rw [this]; exact h2

theorem dU_map {x : E} (hx : x ∈ U.domain) (t : ℝ) : U.dU (U t x) = U t (U.dU x) := by
  have h1 := hasDerivAt_dU (domain_invariant hx t)
  have h2 : HasDerivAt (fun s => U s (U t x)) (U t (U.dU x)) 0 := by
    have h := ((U t).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_dU hx)
    have : (fun s => U s (U t x)) = fun s => U t (U s x) := by funext s; exact U.comm s t x
    rw [this]; exact h
  exact h1.unique h2


/-- `⟪d x, z⟫ + ⟪x, d z⟫ = 0`: differentiating `⟪U t x, U t z⟫ = ⟪x, z⟫` at `0`. -/
theorem inner_dU_add_inner_dU {x z : E} (hx : x ∈ U.domain) (hz : z ∈ U.domain) :
    ⟪U.dU x, z⟫_ℂ + ⟪x, U.dU z⟫_ℂ = 0 := by
  have hsx := (hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_dU hx))
  have hsz := (hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_dU hz))
  have hcz : Tendsto (fun t => U t z) (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
    have := (U.continuous z).tendsto 0
    rw [U.map_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => ⟪slope (fun s => U s x) 0 t, U t z⟫_ℂ +
      ⟪x, slope (fun s => U s z) 0 t⟫_ℂ) (𝓝[≠] 0) (𝓝 (⟪U.dU x, z⟫_ℂ + ⟪x, U.dU z⟫_ℂ)) :=
    (hsx.inner hcz).add (tendsto_const_nhds.inner hsz)
  have hzero : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ⟪slope (fun s => U s x) 0 t, U t z⟫_ℂ +
      ⟪x, slope (fun s => U s z) 0 t⟫_ℂ = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [slope_def_module, sub_zero, U.map_zero]
    have e : ∀ (r : ℝ) (v : E), r • v = (r : ℂ) • v := fun r v =>
      RCLike.real_smul_eq_coe_smul (K := ℂ) r v
    rw [e, e, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, U.inner_map,
      Complex.conj_ofReal]
    ring
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun t h => h.symm))

/-- The generator is symmetric. -/
theorem generator_isFormalAdjoint : U.generator.IsFormalAdjoint U.generator := by
  intro x y
  have h := inner_dU_add_inner_dU x.2 y.2
  have hx : U.dU x = Complex.I • U.generator x := by
    show _ = Complex.I • ((-Complex.I) • U.dU (x : E))
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have hy : U.dU y = Complex.I • U.generator y := by
    show _ = Complex.I • ((-Complex.I) • U.dU (y : E))
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rw [hx, hy, inner_smul_left, inner_smul_right] at h
  simp only [Complex.conj_I] at h
  have : Complex.I * (⟪(x : E), U.generator y⟫_ℂ - ⟪U.generator x, (y : E)⟫_ℂ) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 Complex.I_ne_zero
  · exact (sub_eq_zero.1 h0).symm


section Density

variable [CompleteSpace E]

/-- The primitive `Φ h = ∫₀ʰ U s z ds` of the orbit. -/
def prim (z : E) (h : ℝ) : E := ∫ s in (0 : ℝ)..h, U s z

theorem hasDerivAt_prim (z : E) (h : ℝ) : HasDerivAt (U.prim z) (U h z) h :=
  intervalIntegral.integral_hasDerivAt_right (U.continuous z |>.intervalIntegrable _ _)
    (U.continuous z).aestronglyMeasurable.stronglyMeasurableAtFilter (U.continuous z).continuousAt

omit [CompleteSpace E] in
theorem prim_zero (z : E) : U.prim z 0 = 0 := by simp [prim]

/-- `U h` of the average `Φ ε / ε` is `(Φ (ε + h) - Φ h) / ε`. -/
theorem map_prim (z : E) (h ε : ℝ) : U h (U.prim z ε) = U.prim z (ε + h) - U.prim z h := by
  unfold prim
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => U s z) volume a b := fun a b =>
    (U.continuous z).intervalIntegrable a b
  have h1 : U h (∫ s in (0 : ℝ)..ε, U s z) = ∫ s in (0 : ℝ)..ε, U h (U s z) :=
    ((U h).toContinuousLinearMap.intervalIntegral_comp_comm (hint 0 ε)).symm
  have h2 : (∫ s in (0 : ℝ)..ε, U h (U s z)) = ∫ s in (0 : ℝ)..ε, U (s + h) z := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [U.map_add, U.comm]
  have h3 : (∫ s in (0 : ℝ)..ε, U (s + h) z) = ∫ s in h..ε + h, U s z := by
    rw [intervalIntegral.integral_comp_add_right (fun s => U s z) h, zero_add]
  rw [h1, h2, h3, intervalIntegral.integral_interval_sub_left (hint 0 (ε + h)) (hint 0 h)]

/-- The averages `ε⁻¹ ∫₀^ε U s z ds` lie in the domain. -/
theorem smul_prim_mem_domain (z : E) (ε : ℝ) : (ε⁻¹ : ℝ) • U.prim z ε ∈ U.domain := by
  refine ⟨(ε⁻¹ : ℝ) • (U ε z - U 0 z), ?_⟩
  have hc : ∀ h, U h ((ε⁻¹ : ℝ) • U.prim z ε) = (ε⁻¹ : ℝ) • (U.prim z (ε + h) - U.prim z h) := by
    intro h
    have : U h ((ε⁻¹ : ℝ) • U.prim z ε) = (ε⁻¹ : ℝ) • U h (U.prim z ε) := by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    rw [this, U.map_prim]
  simp_rw [hc]
  have h1 : HasDerivAt (fun h => U.prim z (ε + h)) (U (ε + 0) z) 0 := by
    have := (U.hasDerivAt_prim z (ε + 0)).comp_const_add ε 0
    simpa using this
  have h2 := U.hasDerivAt_prim z 0
  have h3 := (h1.sub h2).const_smul (ε⁻¹ : ℝ)
  simp only [U.map_zero, add_zero] at h3 ⊢
  exact h3

/-- **The domain of the generator is dense.** -/
theorem dense_domain : Dense (U.domain : Set E) := by
  intro z
  have h0 := hasDerivAt_iff_tendsto_slope.1 (U.hasDerivAt_prim z 0)
  rw [U.map_zero] at h0
  have h1 : Tendsto (slope (U.prim z) 0) (𝓝[>] (0 : ℝ)) (𝓝 z) :=
    h0.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine mem_closure_of_tendsto h1 (Eventually.of_forall fun ε => ?_)
  rw [slope_def_module, sub_zero, U.prim_zero, sub_zero]
  exact U.smul_prim_mem_domain z ε

end Density

section Resolvent

variable [CompleteSpace E]

/-- The resolvent integrand `e^{-t} U t z`. -/
def resInt (z : E) (t : ℝ) : E := Real.exp (-t) • U t z

omit [CompleteSpace E] in
theorem continuous_resInt (z : E) : Continuous (U.resInt z) :=
  (Real.continuous_exp.comp continuous_neg).smul (U.continuous z)

theorem integrableOn_resInt (z : E) (a : ℝ) : IntegrableOn (U.resInt z) (Ioi a) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi a).const_mul ‖z‖)
    (U.continuous_resInt z).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  simp only [resInt, norm_smul, Real.norm_eq_abs, Real.abs_exp, U.norm_map]
  rw [mul_comm]

/-- The resolvent `∫₀^∞ e^{-t} U t z dt`. -/
def res (z : E) : E := ∫ t in Ioi (0 : ℝ), U.resInt z t

theorem integral_Ioi_comp_add_right (g : ℝ → E) (h : ℝ) :
    ∫ t in Ioi (0 : ℝ), g (t + h) = ∫ t in Ioi h, g t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  have : (Ioi (0 : ℝ)).indicator (fun t => g (t + h)) = fun t => (Ioi h).indicator g (t + h) := by
    funext t
    by_cases ht : 0 < t
    · simp [indicator_of_mem, ht, show h < t + h from by linarith]
    · simp [indicator_of_notMem, ht, show ¬ h < t + h from by intro; apply ht; linarith]
  rw [this]
  exact integral_add_right_eq_self (fun t => (Ioi h).indicator g t) h

/-- `U h` applied to the resolvent: `U h (R z) = e^h (R z - ∫₀ʰ e^{-s} U s z ds)`. -/
theorem map_res (z : E) (h : ℝ) :
    U h (U.res z) = Real.exp h • (U.res z - ∫ s in (0 : ℝ)..h, U.resInt z s) := by
  have h1 : U h (U.res z) = ∫ t in Ioi (0 : ℝ), U h (U.resInt z t) :=
    (((U h).toContinuousLinearMap.restrictScalars ℝ).integral_comp_comm
      (U.integrableOn_resInt z 0)).symm
  have h2 : ∀ t : ℝ, U h (U.resInt z t) = Real.exp h • U.resInt z (t + h) := by
    intro t
    simp only [resInt]
    have e : ∀ (r : ℝ) (v : E), U h (r • v) = r • U h v := fun r v => by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    rw [e, U.comm h t z, ← U.map_add, smul_smul, ← Real.exp_add]
    rw [add_comm t h]
    congr 2; ring
  simp_rw [h2] at h1
  rw [h1, MeasureTheory.integral_smul, integral_Ioi_comp_add_right (U.resInt z) h]
  congr 1
  have := intervalIntegral.integral_Ioi_sub_Ioi' (U.integrableOn_resInt z 0)
    (U.integrableOn_resInt z h)
  rw [res, ← this]; abel

theorem hasDerivAt_exp_smul (z : E) :
    HasDerivAt (fun h => Real.exp h • (U.res z - ∫ s in (0 : ℝ)..h, U.resInt z s))
      (U.res z - z) 0 := by
  have hΨ : HasDerivAt (fun h => ∫ s in (0 : ℝ)..h, U.resInt z s) (U.resInt z 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      ((U.continuous_resInt z).intervalIntegrable _ _)
      (U.continuous_resInt z).aestronglyMeasurable.stronglyMeasurableAtFilter
      (U.continuous_resInt z).continuousAt
  have hprod : HasDerivAt (fun h => Real.exp h • (U.res z - ∫ s in (0 : ℝ)..h, U.resInt z s))
      (Real.exp 0 • (0 - U.resInt z 0) +
        Real.exp 0 • (U.res z - ∫ s in (0 : ℝ)..0, U.resInt z s)) 0 :=
    (Real.hasDerivAt_exp 0).smul ((hasDerivAt_const (0 : ℝ) (U.res z)).sub hΨ)
  refine hprod.congr_deriv ?_
  simp [resInt]
  abel

/-- **The resolvent lies in the domain**, with `d (R z) = R z - z`. -/
theorem res_mem_domain (z : E) : U.res z ∈ U.domain := by
  refine ⟨U.res z - z, ?_⟩
  have hf : (fun h => U h (U.res z)) =
      fun h => Real.exp h • (U.res z - ∫ s in (0 : ℝ)..h, U.resInt z s) := by
    funext h; exact U.map_res z h
  rw [hf]; exact U.hasDerivAt_exp_smul z

theorem dU_res (z : E) : U.dU (U.res z) = U.res z - z := by
  have h1 := hasDerivAt_dU (U.res_mem_domain z)
  have hf : (fun h => U h (U.res z)) =
      fun h => Real.exp h • (U.res z - ∫ s in (0 : ℝ)..h, U.resInt z s) := by
    funext h; exact U.map_res z h
  have h2 : HasDerivAt (fun h => U h (U.res z)) (U.res z - z) 0 := by
    rw [hf]; exact U.hasDerivAt_exp_smul z
  exact h1.unique h2

end Resolvent



/-- The group run backwards, `t ↦ U (-t)`. -/
def reflect : StronglyContinuousUnitaryGroup E where
  toFun t := U (-t)
  map_zero' x := by simp
  map_add' s t x := by rw [neg_add, U.map_add]
  continuous' x := (U.continuous x).comp continuous_neg

theorem reflect_apply (t : ℝ) (x : E) : U.reflect t x = U (-t) x := rfl

theorem hasDerivAt_neg_comp {f : ℝ → E} {f' : E} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun t => f (-t)) (-f') 0 := by
  have hg : HasDerivAt f f' (-(0 : ℝ)) := by rwa [neg_zero]
  have := hg.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  simpa [Function.comp_def] using this

theorem mem_domain_reflect {x : E} (hx : x ∈ U.domain) : x ∈ U.reflect.domain := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨-y, hasDerivAt_neg_comp hy⟩

theorem dU_reflect {x : E} (hx : x ∈ U.domain) : U.reflect.dU x = -U.dU x := by
  have h1 := hasDerivAt_dU (U.mem_domain_reflect hx)
  have h2 : HasDerivAt (fun t => U.reflect t x) (-U.dU x) 0 :=
    hasDerivAt_neg_comp (hasDerivAt_dU hx)
  exact h1.unique h2

theorem mem_domain_of_reflect {x : E} (hx : x ∈ U.reflect.domain) : x ∈ U.domain := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨-y, ?_⟩
  have := hasDerivAt_neg_comp hy
  simpa [reflect_apply] using this

section SelfAdjoint

variable [CompleteSpace E]

/-- `A + i` is surjective. -/
theorem exists_add_I (w : E) : ∃ x : U.generator.domain, U.generator x + Complex.I • (x : E) = w := by
  have hz : (-Complex.I) • ((-Complex.I) • w) = -w := by
    rw [smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  refine ⟨⟨U.res ((-Complex.I) • w), U.res_mem_domain _⟩, ?_⟩
  show (-Complex.I) • U.dU (U.res ((-Complex.I) • w)) + Complex.I • U.res ((-Complex.I) • w) = w
  rw [U.dU_res, smul_sub, hz]
  simp only [neg_smul]
  abel

/-- `A - i` is surjective. -/
theorem exists_sub_I (w : E) : ∃ x : U.generator.domain, U.generator x - Complex.I • (x : E) = w := by
  have hz : (-Complex.I) • (Complex.I • w) = w := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hd : U.reflect.res (Complex.I • w) ∈ U.domain :=
    U.mem_domain_of_reflect (U.reflect.res_mem_domain _)
  refine ⟨⟨U.reflect.res (Complex.I • w), hd⟩, ?_⟩
  show (-Complex.I) • U.dU (U.reflect.res (Complex.I • w)) -
    Complex.I • U.reflect.res (Complex.I • w) = w
  have h3 : -U.dU (U.reflect.res (Complex.I • w)) =
      U.reflect.res (Complex.I • w) - Complex.I • w :=
    (U.dU_reflect hd).symm.trans (U.reflect.dU_res _)
  have h1 : U.dU (U.reflect.res (Complex.I • w)) =
      Complex.I • w - U.reflect.res (Complex.I • w) := by
    rw [← neg_sub, ← h3, neg_neg]
  rw [h1, smul_sub, hz]
  simp only [neg_smul]
  abel

/-- **Stone's theorem (easy half).** The generator of a strongly continuous unitary group on a
complex Hilbert space is self-adjoint. -/
theorem isSelfAdjoint_generator : IsSelfAdjoint U.generator := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hd : Dense (U.generator.domain : Set E) := U.dense_domain
  have hle : U.generator ≤ U.generator.adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd U.generator_isFormalAdjoint
  have hdom : U.generator.adjoint.domain ≤ U.generator.domain := by
    intro y hy
    obtain ⟨x, hx⟩ := U.exists_add_I ((U.generator.adjoint ⟨y, hy⟩) + Complex.I • y)
    have hxa : (x : E) ∈ U.generator.adjoint.domain := hle.1 x.2
    have hAx : U.generator.adjoint ⟨x, hxa⟩ = U.generator x := (hle.2 (x := x) (y := ⟨x, hxa⟩) rfl).symm
    -- `u = y - x` satisfies `A† u = - i u`
    set u : U.generator.adjoint.domain := ⟨y, hy⟩ - ⟨x, hxa⟩ with hu
    have hAu : U.generator.adjoint u = (-Complex.I) • (u : E) := by
      have hsub : U.generator.adjoint u =
          U.generator.adjoint ⟨y, hy⟩ - U.generator.adjoint ⟨x, hxa⟩ := by
        rw [hu]; exact U.generator.adjoint.toFun.map_sub _ _
      rw [hsub, hAx]
      have : U.generator x = U.generator.adjoint ⟨y, hy⟩ + Complex.I • y - Complex.I • (x : E) := by
        rw [← hx]; abel
      have hue : (u : E) = y - (x : E) := by rw [hu]; rfl
      rw [this, hue]
      simp only [smul_sub, neg_smul]
      abel
    have hperp : ∀ w : E, ⟪(u : E), w⟫_ℂ = 0 := by
      intro w
      obtain ⟨v, hv⟩ := U.exists_sub_I w
      have h1 := LinearPMap.adjoint_isFormalAdjoint (T := U.generator) hd u v
      rw [hAu, inner_smul_left] at h1
      simp only [map_neg, Complex.conj_I, neg_neg] at h1
      rw [← hv, inner_sub_right, inner_smul_right, ← h1]
      ring
    have hu0 : (u : E) = 0 := inner_self_eq_zero.1 (hperp u)
    have hyx : y = (x : E) := by
      have : (y : E) - x = 0 := by simpa [hu] using hu0
      exact sub_eq_zero.1 this
    rw [hyx]; exact x.2
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end SelfAdjoint

end StronglyContinuousUnitaryGroup

namespace StronglyContinuousUnitaryGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Stone's theorem** (generator direction). A strongly continuous one-parameter group of
isometries `U` of a complex Hilbert space has a self-adjoint generator `A`, with domain the set of
vectors whose orbit is differentiable at `0`, such that `d/dt (U t x) = i A x` at `t = 0` for
`x` in the domain; the domain is invariant under every `U t`, and the orbit of a domain vector is
differentiable at every time `t` with derivative `i A (U t x) = U t (i A x)`. -/
theorem stone (U : StronglyContinuousUnitaryGroup E) :
    ∃ A : E →ₗ.[ℂ] E, IsSelfAdjoint A ∧ A.domain = U.domain ∧
      (∀ x : A.domain, HasDerivAt (fun t => U t x) (Complex.I • A x) 0) ∧
      (∀ x : A.domain, ∀ t : ℝ, U t x ∈ A.domain ∧
        HasDerivAt (fun s => U s x) (U t (Complex.I • A x)) t) := by
  refine ⟨U.generator, U.isSelfAdjoint_generator, rfl, U.hasDerivAt_generator, fun x t => ?_⟩
  refine ⟨U.domain_invariant x.2 t, ?_⟩
  have hx : U.dU x = Complex.I • U.generator x := by
    show _ = Complex.I • ((-Complex.I) • U.dU (x : E))
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have := U.hasDerivAt_orbit x.2 t
  rwa [hx] at this

end StronglyContinuousUnitaryGroup

#print axioms StronglyContinuousUnitaryGroup.stone
#print axioms StronglyContinuousUnitaryGroup.isSelfAdjoint_generator
