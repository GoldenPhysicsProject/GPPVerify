/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicFiniteDuality
import GppVerify.Upstream.RatFiniteAdeleRingSchwartzBruhat


/-!
# Character orthogonality and the finite Fourier transform of coset indicators

On the finite adeles `Af = 𝔸_{ℚ,f}`, with the finite part `finChar` of the standard character and
the Haar measure `haar` (volume `1` on `∏ ℤ_v`):

* `integral_indicator_subgroup_char`: the integral of an additive character over an open subgroup
  `H` is `haar H` if the character is trivial on `H`, and `0` otherwise.
* `integral_natMulIntegral_char` and `integral_integralDivNat_char`: orthogonality for the dual
  pair of lattices `N ∏ ℤ_v` and `(1/N) ∏ ℤ_v`.
* `finFourier_cosetIndicator`: the transform of the indicator of `a + N ∏ ℤ_v` is
  `ψ_f(-ab) · N⁻¹ · 1_{(1/N)∏ℤ_v}(b)`.
* `finFourier_finFourier_cosetIndicator`: transforming twice gives `1_{-a + N∏ℤ_v}`.
-/

open MeasureTheory IsDedekindDomain GppIdeleQ Rat.FiniteAdeleRing

namespace GlobalTate.Poisson

/-- The finite part of the standard character, as a complex-valued function. -/
noncomputable def ψc (a : Af) : ℂ := (finChar a : ℂ)

theorem ψc_add (a b : Af) : ψc (a + b) = ψc a * ψc b := by
  simp [ψc, finChar_add]

theorem ψc_eq_one_iff (a : Af) : ψc a = 1 ↔ a ∈ intBox := by
  rw [← finChar_eq_one_iff]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; simp [ψc, h]

theorem norm_ψc (a : Af) : ‖ψc a‖ = 1 := Circle.norm_coe _

theorem continuous_ψc : Continuous ψc := by
  have : Continuous (finChar : Af → Circle) :=
    continuous_adeleChar.comp (Continuous.prodMk continuous_const continuous_id)
  exact continuous_subtype_val.comp this

open Classical in
/-- **Orthogonality over a subgroup.** -/
theorem integral_indicator_subgroup_char (H : AddSubgroup Af) (hH : MeasurableSet (H : Set Af))
    (χ : Af → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) :
    ∫ a, (H : Set Af).indicator χ a ∂haar =
      if ∀ s ∈ H, χ s = 1 then (haar (H : Set Af)).toReal else 0 := by
  by_cases hall : ∀ s ∈ H, χ s = 1
  · rw [if_pos hall, integral_indicator hH]
    rw [setIntegral_congr_fun hH (fun a ha => hall a ha), setIntegral_const]
    simp [Measure.real]
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨s, hs, hχs⟩ := hall
    set F : Af → ℂ := (H : Set Af).indicator χ with hF
    have hshift : ∀ a, F (a + s) = χ s * F a := by
      intro a
      by_cases ha : a ∈ H
      · have hs' : a + s ∈ H := H.add_mem ha hs
        simp only [hF, Set.indicator_of_mem (show a ∈ (H : Set Af) from ha),
          Set.indicator_of_mem (show a + s ∈ (H : Set Af) from hs'), hχ, mul_comm]
      · have hs' : a + s ∉ H := fun h => ha (by simpa using H.sub_mem h hs)
        simp [hF, Set.indicator_of_notMem (show a ∉ (H : Set Af) from ha),
          Set.indicator_of_notMem (show a + s ∉ (H : Set Af) from hs')]
    have h1 : ∫ a, F (a + s) ∂haar = ∫ a, F a ∂haar := integral_add_right_eq_self F s
    simp_rw [hshift, integral_const_mul] at h1
    have : (χ s - 1) * ∫ a, F a ∂haar = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hχs
    · exact h

/-! ### The dual pair of lattices `N ∏ ℤ_v`, `(1/N) ∏ ℤ_v` -/

section lattices

variable {N : ℕ}

/-- `(1/N) ∏ ℤ_v` as an additive subgroup. -/
def integralDivNatAddSubgroup (N : ℕ) : AddSubgroup Af where
  carrier := integralDivNat N
  zero_mem' := by
    show (N : Af) * 0 ∈ integralAdeles
    rw [mul_zero]; exact zero_mem_integralAdeles
  add_mem' := fun {a b} ha hb => by
    show (N : Af) * (a + b) ∈ integralAdeles
    rw [mul_add]; exact add_mem_integralAdeles ha hb
  neg_mem' := fun {a} ha => by
    show (N : Af) * (-a) ∈ integralAdeles
    rw [mul_neg]; exact neg_mem_integralAdeles ha

/-- The scalar `N⁻¹` as a finite adele. -/
noncomputable def invNat (N : ℕ) : Af := algebraMap ℚ Af ((N : ℚ)⁻¹)

theorem natCast_mul_invNat (hN : N ≠ 0) : (N : Af) * invNat N = 1 :=
  natCast_mul_algebraMap_inv hN

/-- `u ∈ N∏ℤ_v`, `b ∈ (1/N)∏ℤ_v` ⇒ `u b` is everywhere integral. -/
theorem mul_mem_intBox_of_mem_natMulIntegral {u b : Af} (hN : N ≠ 0)
    (hu : u ∈ natMulIntegral N) (hb : b ∈ integralDivNat N) : u * b ∈ intBox := by
  have hu' : invNat N * u ∈ integralAdeles := hu
  have hb' : (N : Af) * b ∈ integralAdeles := hb
  have h := mul_mem_integralAdeles hu' hb'
  have e : invNat N * u * ((N : Af) * b) = u * b := by
    have := natCast_mul_invNat hN
    calc invNat N * u * ((N : Af) * b) = ((N : Af) * invNat N) * (u * b) := by ring
      _ = u * b := by rw [this, one_mul]
  rwa [e] at h

/-- If `b ∉ (1/N)∏ℤ_v`, some `u ∈ N∏ℤ_v` has `u b` not everywhere integral. -/
theorem exists_mem_natMulIntegral_mul_not_mem {b : Af} (hN : N ≠ 0) (hb : b ∉ integralDivNat N) :
    ∃ u ∈ natMulIntegral N, u * b ∉ intBox := by
  have hb' : (N : Af) * b ∉ intBox := hb
  obtain ⟨m, hm⟩ := exists_natCast_mul_not_mem hb'
  refine ⟨(N : Af) * (m : Af), ?_, ?_⟩
  · show invNat N * ((N : Af) * (m : Af)) ∈ integralAdeles
    have : invNat N * ((N : Af) * (m : Af)) = (m : Af) := by
      rw [← mul_assoc, mul_comm (invNat N), natCast_mul_invNat hN, one_mul]
    rw [this]; exact natCast_mem_integralAdeles m
  · have : (N : Af) * (m : Af) * b = (m : Af) * ((N : Af) * b) := by ring
    rw [this]; exact hm

/-- `x ∈ N∏ℤ_v`, `b ∈ (1/N)∏ℤ_v` ⇒ `b x` is everywhere integral. -/
theorem mul_mem_intBox_of_mem_integralDivNat {x b : Af} (hN : N ≠ 0)
    (hx : x ∈ natMulIntegral N) (hb : b ∈ integralDivNat N) : b * x ∈ intBox := by
  rw [mul_comm]; exact mul_mem_intBox_of_mem_natMulIntegral hN hx hb

/-- If `x ∉ N∏ℤ_v`, some `b ∈ (1/N)∏ℤ_v` has `b x` not everywhere integral. -/
theorem exists_mem_integralDivNat_mul_not_mem {x : Af} (hN : N ≠ 0) (hx : x ∉ natMulIntegral N) :
    ∃ b ∈ integralDivNat N, b * x ∉ intBox := by
  have hx' : invNat N * x ∉ intBox := hx
  obtain ⟨m, hm⟩ := exists_natCast_mul_not_mem hx'
  refine ⟨invNat N * (m : Af), ?_, ?_⟩
  · show (N : Af) * (invNat N * (m : Af)) ∈ integralAdeles
    rw [← mul_assoc, natCast_mul_invNat hN, one_mul]
    exact natCast_mem_integralAdeles m
  · have : invNat N * (m : Af) * x = (m : Af) * (invNat N * x) := by ring
    rw [this]; exact hm

theorem haar_natMulIntegralAddSubgroup_toReal (hN : N ≠ 0) :
    (haar (natMulIntegralAddSubgroup N : Set Af)).toReal = (N : ℝ)⁻¹ := by
  have : (natMulIntegralAddSubgroup N : Set Af) = natMulIntegral N := rfl
  rw [this, haar_natMulIntegral hN]
  simp [ENNReal.toReal_inv]

theorem haar_integralDivNatAddSubgroup_toReal (hN : N ≠ 0) :
    (haar (integralDivNatAddSubgroup N : Set Af)).toReal = (N : ℝ) := by
  have : (integralDivNatAddSubgroup N : Set Af) = integralDivNat N := rfl
  rw [this, haar_integralDivNat hN]
  simp

open Classical in
/-- **Orthogonality for `N ∏ ℤ_v`.** -/
theorem integral_natMulIntegral_char (hN : N ≠ 0) (b : Af) :
    ∫ u, (natMulIntegral N).indicator (fun u => ψc (-(u * b))) u ∂haar =
      if b ∈ integralDivNat N then ((N : ℝ)⁻¹ : ℝ) else 0 := by
  have hH : MeasurableSet ((natMulIntegralAddSubgroup N : AddSubgroup Af) : Set Af) :=
    (isOpen_natMulIntegral N).measurableSet
  have key := integral_indicator_subgroup_char (natMulIntegralAddSubgroup N) hH
    (fun u => ψc (-(u * b))) (fun a c => by
      rw [add_mul, neg_add, ψc_add])
  have e : ((natMulIntegralAddSubgroup N : AddSubgroup Af) : Set Af) = natMulIntegral N := rfl
  rw [e] at key
  rw [key]
  by_cases hb : b ∈ integralDivNat N
  · have hall : ∀ s ∈ natMulIntegralAddSubgroup N, ψc (-(s * b)) = 1 := fun s hs =>
      (ψc_eq_one_iff _).2 (intBox_neg_mem (mul_mem_intBox_of_mem_natMulIntegral hN hs hb))
    rw [if_pos hall, if_pos hb]
    have := haar_natMulIntegralAddSubgroup_toReal hN
    rw [e] at this
    rw [this]
  · have hall : ¬ ∀ s ∈ natMulIntegralAddSubgroup N, ψc (-(s * b)) = 1 := by
      intro h
      obtain ⟨u, hu, hub⟩ := exists_mem_natMulIntegral_mul_not_mem hN hb
      apply hub
      have := (ψc_eq_one_iff _).1 (h u hu)
      simpa using intBox_neg_mem this
    rw [if_neg hall, if_neg hb]

open Classical in
/-- **Orthogonality for `(1/N) ∏ ℤ_v`.** -/
theorem integral_integralDivNat_char (hN : N ≠ 0) (x : Af) :
    ∫ b, (integralDivNat N).indicator (fun b => ψc (-(b * x))) b ∂haar =
      if x ∈ natMulIntegral N then (N : ℝ) else 0 := by
  have hH : MeasurableSet ((integralDivNatAddSubgroup N : AddSubgroup Af) : Set Af) :=
    (isOpen_integralDivNat N).measurableSet
  have key := integral_indicator_subgroup_char (integralDivNatAddSubgroup N) hH
    (fun b => ψc (-(b * x))) (fun a c => by
      rw [add_mul, neg_add, ψc_add])
  have e : ((integralDivNatAddSubgroup N : AddSubgroup Af) : Set Af) = integralDivNat N := rfl
  rw [e] at key
  rw [key]
  by_cases hx : x ∈ natMulIntegral N
  · have hall : ∀ s ∈ integralDivNatAddSubgroup N, ψc (-(s * x)) = 1 := fun s hs =>
      (ψc_eq_one_iff _).2 (intBox_neg_mem (mul_mem_intBox_of_mem_integralDivNat hN hx hs))
    rw [if_pos hall, if_pos hx]
    have := haar_integralDivNatAddSubgroup_toReal hN
    rw [e] at this
    rw [this]
  · have hall : ¬ ∀ s ∈ integralDivNatAddSubgroup N, ψc (-(s * x)) = 1 := by
      intro h
      obtain ⟨b, hb, hbx⟩ := exists_mem_integralDivNat_mul_not_mem hN hx
      apply hbx
      have := (ψc_eq_one_iff _).1 (h b hb)
      simpa using intBox_neg_mem this
    rw [if_neg hall, if_neg hx]

end lattices

/-! ### The transform of a coset indicator -/

/-- The indicator of the coset `a + N ∏ ℤ_v`. -/
noncomputable def cosetIndicator (N : ℕ) (a : Af) : Af → ℂ :=
  {y : Af | y - a ∈ natMulIntegral N}.indicator fun _ => (1 : ℂ)

open Classical in
/-- **The finite Fourier transform of a coset indicator**:
`𝓕 1_{a + N∏ℤ_v} (b) = ψ_f(-ab) · N⁻¹ · 1_{(1/N)∏ℤ_v}(b)`. -/
theorem finFourier_cosetIndicator {N : ℕ} (hN : N ≠ 0) (a b : Af) :
    finFourier (cosetIndicator N a) b =
      ψc (-(a * b)) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) b := by
  unfold finFourier
  set F : Af → ℂ := fun y => (finChar (-(y * b)) : ℂ) * cosetIndicator N a y with hF
  have h := integral_add_left_eq_self F a (μ := haar)
  rw [← h]
  have hpt : ∀ x, F (a + x) =
      ψc (-(a * b)) * (natMulIntegral N).indicator (fun u => ψc (-(u * b))) x := by
    intro x
    by_cases hx : x ∈ natMulIntegral N
    · have hx' : a + x - a ∈ natMulIntegral N := by rwa [add_sub_cancel_left]
      simp only [hF, cosetIndicator, Set.indicator_of_mem (show a + x ∈ {y : Af | y - a ∈ natMulIntegral N} from hx'),
        Set.indicator_of_mem hx]
      have : -((a + x) * b) = -(a * b) + -(x * b) := by ring
      show ψc (-((a + x) * b)) * 1 = _
      rw [this, ψc_add, mul_one]
    · have hx' : a + x ∉ {y : Af | y - a ∈ natMulIntegral N} := by
        intro h'
        apply hx
        have : a + x - a ∈ natMulIntegral N := h'
        rwa [add_sub_cancel_left] at this
      simp [hF, cosetIndicator, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  simp_rw [hpt, integral_const_mul]
  rw [integral_natMulIntegral_char hN b]
  by_cases hb : b ∈ integralDivNat N
  · simp [hb]
  · simp [hb]

open Classical in
/-- **Transforming twice**: `𝓕 (𝓕 1_{a + N∏ℤ_v}) = 1_{-a + N∏ℤ_v}`. -/
theorem finFourier_finFourier_cosetIndicator {N : ℕ} (hN : N ≠ 0) (a c : Af) :
    finFourier (finFourier (cosetIndicator N a)) c = cosetIndicator N (-a) c := by
  have h1 : finFourier (cosetIndicator N a) = fun b =>
      ψc (-(a * b)) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) b :=
    funext fun b => finFourier_cosetIndicator hN a b
  rw [h1]
  unfold finFourier
  have hpt : ∀ b : Af, (finChar (-(b * c)) : ℂ) *
      (ψc (-(a * b)) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) =
      ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun b => ψc (-(b * (a + c)))) b := by
    intro b
    by_cases hb : b ∈ integralDivNat N
    · simp only [Set.indicator_of_mem hb]
      have : -(b * (a + c)) = -(b * c) + -(a * b) := by ring
      show ψc (-(b * c)) * _ = _
      rw [this, ψc_add]
      ring
    · simp [Set.indicator_of_notMem hb]
  simp_rw [hpt, integral_const_mul]
  rw [integral_integralDivNat_char hN (a + c)]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  by_cases hx : a + c ∈ natMulIntegral N
  · have : c - -a ∈ natMulIntegral N := by rwa [sub_neg_eq_add, add_comm]
    simp only [if_pos hx, cosetIndicator, Set.indicator_of_mem (show c ∈ {y : Af | y - -a ∈ natMulIntegral N} from this)]
    push_cast
    field_simp
  · have : c ∉ {y : Af | y - -a ∈ natMulIntegral N} := by
      intro h'
      apply hx
      have h'' : c - -a ∈ natMulIntegral N := h'
      rwa [sub_neg_eq_add, add_comm] at h''
    rw [if_neg hx]
    unfold cosetIndicator
    rw [Set.indicator_of_notMem this]
    simp

/-! ### Integrability, linearity and the inversion theorem -/

section inversion

variable {N : ℕ}

theorem measurableSet_coset (N : ℕ) (a : Af) : MeasurableSet {y : Af | y - a ∈ natMulIntegral N} :=
  ((isOpen_natMulIntegral N).preimage (continuous_id.sub continuous_const)).measurableSet

theorem haar_coset_ne_top (hN : N ≠ 0) (a : Af) : haar {y : Af | y - a ∈ natMulIntegral N} ≠ ⊤ := by
  have : {y : Af | y - a ∈ natMulIntegral N} = (fun y : Af => y + -a) ⁻¹' natMulIntegral N := by
    ext y; simp [sub_eq_add_neg]
  rw [this, measure_preimage_add_right, haar_natMulIntegral hN]
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hN)

theorem integrable_cosetIndicator (hN : N ≠ 0) (a : Af) :
    Integrable (cosetIndicator N a) haar :=
  (integrable_indicator_iff (measurableSet_coset N a)).2
    (integrableOn_const (haar_coset_ne_top hN a))

theorem haar_integralDivNat_ne_top (hN : N ≠ 0) : haar (integralDivNat N) ≠ ⊤ := by
  rw [haar_integralDivNat hN]; exact ENNReal.natCast_ne_top N

theorem integrable_dualTerm (hN : N ≠ 0) (a : Af) :
    Integrable (fun b => ψc (-(a * b)) * ((N : ℂ)⁻¹) *
      (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) haar := by
  have hmeas : MeasurableSet (integralDivNat N) := (isOpen_integralDivNat N).measurableSet
  have h1 : Integrable ((integralDivNat N).indicator (fun _ => (N : ℂ)⁻¹)) haar :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const (haar_integralDivNat_ne_top hN))
  have hk : Continuous fun b : Af => ψc (-(a * b)) :=
    continuous_ψc.comp (continuous_const.mul continuous_id).neg
  have h2 := h1.bdd_mul (c := 1) hk.aestronglyMeasurable (Filter.Eventually.of_forall fun b => by
    simp [norm_ψc])
  refine h2.congr (Filter.Eventually.of_forall fun b => ?_)
  by_cases hb : b ∈ integralDivNat N
  · simp [Set.indicator_of_mem hb]
  · simp [Set.indicator_of_notMem hb]

theorem integrable_kernel_mul {f : Af → ℂ} (hf : Integrable f haar) (b : Af) :
    Integrable (fun y => (finChar (-(y * b)) : ℂ) * f y) haar := by
  have hk : Continuous fun y : Af => ψc (-(y * b)) :=
    continuous_ψc.comp (continuous_id.mul continuous_const).neg
  exact hf.bdd_mul (c := 1) hk.aestronglyMeasurable (Filter.Eventually.of_forall fun y =>
    (norm_ψc _).le)

theorem finFourier_const_mul (k : ℂ) (f : Af → ℂ) (b : Af) :
    finFourier (fun y => k * f y) b = k * finFourier f b := by
  unfold finFourier
  simp_rw [mul_left_comm _ k, integral_const_mul]

theorem finFourier_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Af → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) haar) (b : Af) :
    finFourier (fun y => ∑ i ∈ s, f i y) b = ∑ i ∈ s, finFourier (f i) b := by
  unfold finFourier
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_kernel_mul (hf i hi) b

/-- **The transform of a finite combination of coset indicators.** -/
theorem finFourier_expansion {ι : Type*} (hN : N ≠ 0) (s : Finset ι) (coef : ι → ℂ) (a : ι → Af)
    (b : Af) :
    finFourier (fun y => ∑ i ∈ s, coef i * cosetIndicator N (a i) y) b =
      ∑ i ∈ s, coef i * (ψc (-(a i * b)) * ((N : ℂ)⁻¹) *
        (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) := by
  rw [finFourier_finset_sum s _ (fun i _ => (integrable_cosetIndicator hN (a i)).const_mul (coef i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finFourier_const_mul, finFourier_cosetIndicator hN]

theorem finFourier_dualTerm (hN : N ≠ 0) (a c : Af) :
    finFourier (fun b => ψc (-(a * b)) * ((N : ℂ)⁻¹) *
      (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) c = cosetIndicator N (-a) c := by
  have h := finFourier_finFourier_cosetIndicator hN a c
  have h1 : finFourier (cosetIndicator N a) = fun b =>
      ψc (-(a * b)) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) b :=
    funext fun b => finFourier_cosetIndicator hN a b
  rwa [h1] at h

/-- **Transforming a finite combination twice.** -/
theorem finFourier_finFourier_expansion {ι : Type*} (hN : N ≠ 0) (s : Finset ι) (coef : ι → ℂ)
    (a : ι → Af) (c : Af) :
    finFourier (finFourier (fun y => ∑ i ∈ s, coef i * cosetIndicator N (a i) y)) c =
      ∑ i ∈ s, coef i * cosetIndicator N (-(a i)) c := by
  have h1 : finFourier (fun y => ∑ i ∈ s, coef i * cosetIndicator N (a i) y) = fun b =>
      ∑ i ∈ s, coef i * (ψc (-(a i * b)) * ((N : ℂ)⁻¹) *
        (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) :=
    funext fun b => finFourier_expansion hN s coef a b
  rw [h1, finFourier_finset_sum s _
    (fun i _ => (integrable_dualTerm hN (a i)).const_mul (coef i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finFourier_const_mul, finFourier_dualTerm hN]

theorem cosetIndicator_neg (N : ℕ) (a c : Af) : cosetIndicator N a (-c) = cosetIndicator N (-a) c := by
  unfold cosetIndicator
  have : (-c - a ∈ natMulIntegral N) ↔ (c - -a ∈ natMulIntegral N) := by
    have e : -c - a = -(c - -a) := by ring
    rw [e]
    exact ⟨fun h => by simpa using neg_mem_natMulIntegral h, neg_mem_natMulIntegral⟩
  by_cases h : -c - a ∈ natMulIntegral N
  · rw [Set.indicator_of_mem (show -c ∈ {y : Af | y - a ∈ natMulIntegral N} from h),
      Set.indicator_of_mem (show c ∈ {y : Af | y - -a ∈ natMulIntegral N} from this.1 h)]
  · rw [Set.indicator_of_notMem (show -c ∉ {y : Af | y - a ∈ natMulIntegral N} from h),
      Set.indicator_of_notMem (show c ∉ {y : Af | y - -a ∈ natMulIntegral N} from fun h' => h (this.2 h'))]

open Classical in
/-- Expansion of a uniformly locally constant, compactly supported function in coset indicators. -/
theorem exists_expansion {g : Af → ℂ} (hc : HasCompactSupport g)
    (huni : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x) :
    ∃ F : Finset (Af ⧸ natMulIntegralAddSubgroup N),
      ∀ y, g y = ∑ cl ∈ F, g cl.out * cosetIndicator N cl.out y := by
  obtain ⟨F, hF⟩ := exists_eq_sum_fiber_of_uniform hc huni
  refine ⟨F, fun y => ?_⟩
  rw [hF y]
  refine Finset.sum_congr rfl fun cl _ => ?_
  have hout : ((cl.out : Af) : Af ⧸ natMulIntegralAddSubgroup N) = cl := Quotient.out_eq _
  have h2 : ((y : Af ⧸ natMulIntegralAddSubgroup N) =
      ((cl.out : Af) : Af ⧸ natMulIntegralAddSubgroup N)) ↔
      -y + cl.out ∈ natMulIntegralAddSubgroup N := QuotientAddGroup.eq
  rw [hout] at h2
  have hiff : ((y : Af ⧸ natMulIntegralAddSubgroup N) = cl) ↔ y - cl.out ∈ natMulIntegral N := by
    rw [h2]
    have e : -y + cl.out = -(y - cl.out) := by ring
    rw [e]
    exact ⟨fun h => by simpa using neg_mem_natMulIntegral h, neg_mem_natMulIntegral⟩
  by_cases h : y - cl.out ∈ natMulIntegral N
  · rw [if_pos (hiff.2 h)]
    unfold cosetIndicator
    rw [Set.indicator_of_mem (show y ∈ {y : Af | y - cl.out ∈ natMulIntegral N} from h), mul_one]
  · rw [if_neg (fun h' => h (hiff.1 h'))]
    unfold cosetIndicator
    rw [Set.indicator_of_notMem (show y ∉ {y : Af | y - cl.out ∈ natMulIntegral N} from h), mul_zero]

/-- **Fourier inversion for the finite Schwartz–Bruhat class**, for a function invariant under a
given lattice: `𝓕 (𝓕 g) = g(-·)`. -/
theorem finFourier_finFourier_of_uniform {g : Af → ℂ} (hN : N ≠ 0) (hc : HasCompactSupport g)
    (huni : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x) (c : Af) :
    finFourier (finFourier g) c = g (-c) := by
  classical
  obtain ⟨F, hF⟩ := exists_expansion hc huni
  have hg : g = fun y => ∑ cl ∈ F, (fun cl : Af ⧸ natMulIntegralAddSubgroup N => g cl.out) cl *
      cosetIndicator N cl.out y := funext hF
  have h := finFourier_finFourier_expansion hN F (fun cl : Af ⧸ natMulIntegralAddSubgroup N => g cl.out)
    (fun cl => cl.out) c
  rw [← hg] at h
  rw [h, hF (-c)]
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [cosetIndicator_neg]

theorem finFourier_finFourier_schwartzBruhat {g : Af → ℂ} (hg : IsSchwartzBruhat g) (c : Af) :
    finFourier (finFourier g) c = g (-c) := by
  obtain ⟨N, hN0, huni⟩ := exists_uniform_of_isLocallyConstant hg.1 hg.2
  exact finFourier_finFourier_of_uniform hN0 hg.2 huni c

end inversion

/-! ### Parseval for coset indicators -/

section parseval

variable {N : ℕ}

theorem ψc_zero : ψc 0 = 1 := (ψc_eq_one_iff 0).2 (by
  intro v; exact zero_mem _)

theorem ψc_conj (x : Af) : starRingEnd ℂ (ψc x) = ψc (-x) := by
  have h1 : ψc x * ψc (-x) = 1 := by rw [← ψc_add, add_neg_cancel, ψc_zero]
  have h2 : ψc x * starRingEnd ℂ (ψc x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ψc]; simp
  exact mul_left_cancel₀ (fun h => by rw [h] at h1; simp at h1) (h2.trans h1.symm)

open Classical in
theorem integral_conj_cosetIndicator_mul (hN : N ≠ 0) (a a' : Af) :
    ∫ y, starRingEnd ℂ (cosetIndicator N a y) * cosetIndicator N a' y ∂haar =
      if a - a' ∈ natMulIntegral N then ((N : ℝ)⁻¹ : ℝ) else 0 := by
  by_cases h : a - a' ∈ natMulIntegral N
  · rw [if_pos h]
    have hset : {y : Af | y - a' ∈ natMulIntegral N} = {y : Af | y - a ∈ natMulIntegral N} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hy
        have := add_mem_natMulIntegral hy h
        have e : y - a' + (a - a') = y - a' + (a - a') := rfl
        have e2 : y - a = (y - a') - (a - a') := by ring
        rw [e2]; exact sub_mem_natMulIntegral hy h
      · intro hy
        have e2 : y - a' = (y - a) + (a - a') := by ring
        rw [e2]; exact add_mem_natMulIntegral hy h
    have hpt : ∀ y, starRingEnd ℂ (cosetIndicator N a y) * cosetIndicator N a' y =
        cosetIndicator N a y := by
      intro y
      unfold cosetIndicator
      rw [hset]
      by_cases hy : y ∈ {y : Af | y - a ∈ natMulIntegral N}
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [hpt]
    unfold cosetIndicator
    rw [integral_indicator (measurableSet_coset N a), setIntegral_const]
    have : haar {y : Af | y - a ∈ natMulIntegral N} = (N : ENNReal)⁻¹ := by
      have e : {y : Af | y - a ∈ natMulIntegral N} = (fun y : Af => y + -a) ⁻¹' natMulIntegral N := by
        ext y; simp [sub_eq_add_neg]
      rw [e, measure_preimage_add_right, haar_natMulIntegral hN]
    simp [Measure.real, this, ENNReal.toReal_inv]
  · rw [if_neg h]
    have hpt : ∀ y, starRingEnd ℂ (cosetIndicator N a y) * cosetIndicator N a' y = 0 := by
      intro y
      unfold cosetIndicator
      by_cases ha : y ∈ {y : Af | y - a ∈ natMulIntegral N}
      · have ha' : y ∉ {y : Af | y - a' ∈ natMulIntegral N} := by
          intro hy
          apply h
          have e : a - a' = (y - a') - (y - a) := by ring
          rw [e]; exact sub_mem_natMulIntegral hy ha
        simp [Set.indicator_of_notMem ha']
      · simp [Set.indicator_of_notMem ha]
    simp_rw [hpt]
    simp

open Classical in
/-- Parseval for coset indicators, on the Fourier side. -/
theorem integral_conj_finFourier_cosetIndicator_mul (hN : N ≠ 0) (a a' : Af) :
    ∫ b, starRingEnd ℂ (finFourier (cosetIndicator N a) b) * finFourier (cosetIndicator N a') b
        ∂haar =
      if a - a' ∈ natMulIntegral N then ((N : ℝ)⁻¹ : ℝ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hpt : ∀ b : Af, starRingEnd ℂ (finFourier (cosetIndicator N a) b) *
      finFourier (cosetIndicator N a') b =
      (((N : ℂ)⁻¹) ^ 2) * (integralDivNat N).indicator (fun b => ψc (-(b * (a' - a)))) b := by
    intro b
    rw [finFourier_cosetIndicator hN, finFourier_cosetIndicator hN]
    by_cases hb : b ∈ integralDivNat N
    · simp only [Set.indicator_of_mem hb, map_mul, ψc_conj, neg_neg, map_inv₀, Complex.conj_natCast,
        map_one]
      have : -(b * (a' - a)) = a * b + -(a' * b) := by ring
      rw [this, ψc_add]
      ring
    · simp [Set.indicator_of_notMem hb]
  simp_rw [hpt, integral_const_mul]
  rw [integral_integralDivNat_char hN (a' - a)]
  have hiff : a' - a ∈ natMulIntegral N ↔ a - a' ∈ natMulIntegral N := by
    have e : a' - a = -(a - a') := by ring
    rw [e]
    exact ⟨fun h => by simpa using neg_mem_natMulIntegral h, neg_mem_natMulIntegral⟩
  by_cases h : a - a' ∈ natMulIntegral N
  · rw [if_pos (hiff.2 h), if_pos h]
    push_cast
    field_simp
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    simp

end parseval

/-! ### Parseval for the finite Schwartz–Bruhat class -/

section parsevalSB

variable {N : ℕ}

/-- **Sesquilinear expansion** of the inner product of two finite combinations. -/
theorem integral_conj_sum_mul {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (u : ι → Af → ℂ) (v : κ → Af → ℂ)
    (hint : ∀ i j, Integrable (fun y => starRingEnd ℂ (u i y) * v j y) haar) :
    ∫ y, starRingEnd ℂ (∑ i ∈ s, c i * u i y) * (∑ j ∈ t, d j * v j y) ∂haar =
      ∑ i ∈ s, ∑ j ∈ t, starRingEnd ℂ (c i) * d j *
        ∫ y, starRingEnd ℂ (u i y) * v j y ∂haar := by
  have h1 : ∀ y, starRingEnd ℂ (∑ i ∈ s, c i * u i y) * (∑ j ∈ t, d j * v j y) =
      ∑ i ∈ s, ∑ j ∈ t, starRingEnd ℂ (c i) * d j * (starRingEnd ℂ (u i y) * v j y) := by
    intro y
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

theorem integrable_conj_cosetIndicator_mul (hN : N ≠ 0) (a a' : Af) :
    Integrable (fun y => starRingEnd ℂ (cosetIndicator N a y) * cosetIndicator N a' y) haar := by
  refine (integrable_cosetIndicator hN a').bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (Complex.continuous_conj.measurable.comp
      (measurable_const.indicator (measurableSet_coset N a))).aestronglyMeasurable
  · by_cases h : y ∈ {y : Af | y - a ∈ natMulIntegral N} <;> simp [cosetIndicator, h]

theorem integrable_conj_finFourier_cosetIndicator_mul (hN : N ≠ 0) (a a' : Af) :
    Integrable (fun b => starRingEnd ℂ (finFourier (cosetIndicator N a) b) *
      finFourier (cosetIndicator N a') b) haar := by
  have hpt : ∀ b : Af, starRingEnd ℂ (finFourier (cosetIndicator N a) b) *
      finFourier (cosetIndicator N a') b =
      (((N : ℂ)⁻¹) ^ 2) * (integralDivNat N).indicator (fun b => ψc (-(b * (a' - a)))) b := by
    intro b
    rw [finFourier_cosetIndicator hN, finFourier_cosetIndicator hN]
    by_cases hb : b ∈ integralDivNat N
    · simp only [Set.indicator_of_mem hb, map_mul, ψc_conj, neg_neg, map_inv₀, Complex.conj_natCast,
        map_one]
      have : -(b * (a' - a)) = a * b + -(a' * b) := by ring
      rw [this, ψc_add]
      ring
    · simp [Set.indicator_of_notMem hb]
  simp_rw [hpt]
  refine Integrable.const_mul ?_ _
  have hmeas : MeasurableSet (integralDivNat N) := (isOpen_integralDivNat N).measurableSet
  rw [integrable_indicator_iff hmeas]
  refine Measure.integrableOn_of_bounded (M := 1) (haar_integralDivNat_ne_top hN) ?_
    (Filter.Eventually.of_forall fun b => (norm_ψc _).le)
  exact (continuous_ψc.comp (continuous_id.mul continuous_const).neg).aestronglyMeasurable

open Classical in
/-- **Parseval for a pair of functions sharing a lattice.** -/
theorem finParseval_of_uniform {g h : Af → ℂ} (hN : N ≠ 0)
    (hgc : HasCompactSupport g) (hgu : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x)
    (hhc : HasCompactSupport h) (hhu : ∀ x, ∀ u ∈ natMulIntegral N, h (x + u) = h x) :
    ∫ b, starRingEnd ℂ (finFourier g b) * finFourier h b ∂haar =
      ∫ y, starRingEnd ℂ (g y) * h y ∂haar := by
  obtain ⟨F, hF⟩ := exists_expansion hgc hgu
  obtain ⟨G, hG⟩ := exists_expansion hhc hhu
  set c : Af ⧸ natMulIntegralAddSubgroup N → ℂ := fun cl => g cl.out with hc
  set d : Af ⧸ natMulIntegralAddSubgroup N → ℂ := fun cl => h cl.out with hd
  have hg : g = fun y => ∑ cl ∈ F, c cl * cosetIndicator N cl.out y := funext hF
  have hh : h = fun y => ∑ cl ∈ G, d cl * cosetIndicator N cl.out y := funext hG
  have hFg : ∀ b, finFourier g b = ∑ cl ∈ F, c cl * finFourier (cosetIndicator N cl.out) b := by
    intro b
    rw [hg, finFourier_finset_sum F _ (fun i _ => (integrable_cosetIndicator hN _).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => finFourier_const_mul _ _ _
  have hFh : ∀ b, finFourier h b = ∑ cl ∈ G, d cl * finFourier (cosetIndicator N cl.out) b := by
    intro b
    rw [hh, finFourier_finset_sum G _ (fun i _ => (integrable_cosetIndicator hN _).const_mul (d i))]
    exact Finset.sum_congr rfl fun i _ => finFourier_const_mul _ _ _
  simp_rw [hFg, hFh]
  conv_rhs => rw [hg, hh]
  rw [integral_conj_sum_mul F G c d _ _ (fun i j => integrable_conj_finFourier_cosetIndicator_mul hN _ _),
    integral_conj_sum_mul F G c d _ _ (fun i j => integrable_conj_cosetIndicator_mul hN _ _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [integral_conj_finFourier_cosetIndicator_mul hN, integral_conj_cosetIndicator_mul hN]

/-- **Parseval for the finite Schwartz–Bruhat class.** -/
theorem finParseval {g h : Af → ℂ} (hg : IsSchwartzBruhat g) (hh : IsSchwartzBruhat h) :
    ∫ b, starRingEnd ℂ (finFourier g b) * finFourier h b ∂haar =
      ∫ y, starRingEnd ℂ (g y) * h y ∂haar := by
  obtain ⟨N, hN, hu⟩ := exists_uniform_of_isLocallyConstant hg.1 hg.2
  obtain ⟨M, hM, hv⟩ := exists_uniform_of_isLocallyConstant hh.1 hh.2
  have hNM : N * M ≠ 0 := Nat.mul_ne_zero hN hM
  exact finParseval_of_uniform hNM hg.2 (uniform_of_dvd hN hNM (dvd_mul_right N M) hu) hh.2
    (uniform_of_dvd hM hNM (dvd_mul_left M N) hv)

end parsevalSB

/-! ### The transform preserves the Schwartz–Bruhat class -/

section preserves

variable {N : ℕ}

/-- The dual term `b ↦ ψ_f(-ab) N⁻¹ 1_{(1/N)∏ℤ_v}(b)` is uniformly locally constant. -/
theorem dualTerm_uniform (a : Af) (N : ℕ) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ b, ∀ u ∈ natMulIntegral M,
      ψc (-(a * (b + u))) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) (b + u) =
      ψc (-(a * b)) * ((N : ℂ)⁻¹) * (integralDivNat N).indicator (fun _ => (1 : ℂ)) b := by
  obtain ⟨M, hM, haM⟩ := exists_natCast_mul_mem_integralAdeles a
  refine ⟨M, hM, fun b u hu => ?_⟩
  have hau : u * a ∈ intBox := mul_mem_intBox_of_mem_natMulIntegral hM hu haM
  have hψ : ψc (-(a * u)) = 1 := by
    refine (ψc_eq_one_iff _).2 (intBox_neg_mem ?_)
    rw [mul_comm]; exact hau
  have hsplit : ψc (-(a * (b + u))) = ψc (-(a * b)) := by
    have : -(a * (b + u)) = -(a * b) + -(a * u) := by ring
    rw [this, ψc_add, hψ, mul_one]
  have huD : u ∈ integralDivNatAddSubgroup N := by
    show u ∈ integralDivNat N
    exact integralAdeles_subset_integralDivNat (natMulIntegral_subset hM hu)
  have hiff : b + u ∈ integralDivNat N ↔ b ∈ integralDivNat N :=
    AddSubgroup.add_mem_cancel_right (integralDivNatAddSubgroup N) huD
  rw [hsplit]
  by_cases hb : b ∈ integralDivNat N
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hiff.2 hb)]
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun h => hb (hiff.1 h))]

open Classical in
/-- **The finite Fourier transform preserves the Schwartz–Bruhat class.** -/
theorem isSchwartzBruhat_finFourier {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    IsSchwartzBruhat (finFourier g) := by
  obtain ⟨N, hN, huni⟩ := exists_uniform_of_isLocallyConstant hg.1 hg.2
  obtain ⟨F, hF⟩ := exists_expansion hg.2 huni
  set c : Af ⧸ natMulIntegralAddSubgroup N → ℂ := fun cl => g cl.out with hc
  have hgf : g = fun y => ∑ cl ∈ F, c cl * cosetIndicator N cl.out y := funext hF
  have hFg : finFourier g = fun b => ∑ cl ∈ F, c cl * (ψc (-(cl.out * b)) * ((N : ℂ)⁻¹) *
      (integralDivNat N).indicator (fun _ => (1 : ℂ)) b) := by
    funext b
    rw [hgf, finFourier_expansion hN F c (fun cl => cl.out) b]
  rw [hFg]
  constructor
  · have hsum : (fun b : Af => ∑ cl ∈ F, c cl * (ψc (-(cl.out * b)) * ((N : ℂ)⁻¹) *
        (integralDivNat N).indicator (fun _ => (1 : ℂ)) b)) =
        ∑ cl ∈ F, (fun b : Af => c cl * (ψc (-(cl.out * b)) * ((N : ℂ)⁻¹) *
        (integralDivNat N).indicator (fun _ => (1 : ℂ)) b)) := by
      funext b; simp [Finset.sum_apply]
    rw [hsum]
    refine Finset.sum_induction _ (fun f : Af → ℂ => IsLocallyConstant f)
      (fun f g hf hg => hf.add hg) IsLocallyConstant.zero (fun cl _ => ?_)
    obtain ⟨M, hM, hu⟩ := dualTerm_uniform cl.out N
    refine isLocallyConstant_of_uniform (N := M) (fun x u hx => ?_)
    have := hu x u hx
    show c cl * (ψc (-(cl.out * (x + u))) * ((N : ℂ)⁻¹) *
        (integralDivNat N).indicator (fun _ => (1 : ℂ)) (x + u)) = _
    rw [this]
  · refine HasCompactSupport.intro (isCompact_integralDivNat hN) (fun b hb => ?_)
    refine Finset.sum_eq_zero fun cl _ => ?_
    simp [Set.indicator_of_notMem hb]

end preserves

end GlobalTate.Poisson
