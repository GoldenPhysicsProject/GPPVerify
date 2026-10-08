import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import GppVerify.RiemannHypothesis.FixedWindowCurvature

/-!
# The completed odd collision form: Galerkin criterion and exact two-box quantities

Source: Daniel's astra note `work/2026-10-08_astra_completed_odd_collision_trace.md`
(bridge repo), which states that the full completed explicit formula on odd test functions is
`W(f * f̃) = E_L(f) − M_L ‖f‖² − 2 |⟨v_L, f⟩|²` with `v_L(x) = sinh(x/2)`, so that the completed
form is `Q_L = B_L − 2 |v_L⟩⟨v_L|`: a form `B_L` minus a **negative rank-one pole term**.

This file proves only the exact finite and calculus parts of that note.

## 1. Galerkin criterion (finite linear algebra)

`galerkin_criterion`: for a symmetric `B` that is positive definite and a vector `v`,
the matrix `B − 2 v vᵀ` is positive semidefinite iff `2 vᵀ B⁻¹ v ≤ 1`
(forward direction by testing at `B⁻¹ v`; reverse by Cauchy–Schwarz in the `B`-inner product).
`RankOneThresholdControls.pole_threshold_pos` is the equality case with the singularity
described; this is the full iff.

## 2. Exact two-box quantities

With `b_ℓ = ℓ^{-1/2} 1_{[-ℓ/2, ℓ/2]}` and `f_t = b_ℓ(· + t/2) − b_ℓ(· − t/2)`:

* `box_pairing`: `⟨sinh(·/2), f_t⟩ = −8 ℓ^{-1/2} sinh(ℓ/4) sinh(t/4)`;
* `pole_term_two_box`: `⟨v, f_t⟩² = 4 A_ℓ sinh²(t/4)` where `A_ℓ = 8 (cosh(ℓ/2) − 1)/ℓ`
  (`FixedWindowCurvature.AA`, which equals `H_ℓ(1/2)`);
* `norm_sq_two_box`: `‖f_t‖² = 2 (1 − max(0, 1 − t/ℓ))`, i.e. `2(1 − h_ℓ(t))`.

## 3. The energy identity `E_y = 2(N − h(y))`

`energy_defect`: in a real inner product space, `‖f − g‖² = ‖f‖² + ‖g‖² − 2⟨f,g⟩`; with
`‖T_y f‖ = ‖f‖` this is the note's `E_y = 2(N − h(y))` (a one-line fact, recorded for the
bookkeeping).

## Scope

**Not proved:** the completed explicit formula itself (`E_L`, `M_L` are not defined here), and
above all the positivity of `Q_L` for any `L`, which the note says is equivalent to RH and is open.
The numerics in the note (susceptibility `2 vᵀ B⁻¹ v ≈ 0.897–0.9999`) are finite Galerkin
floating-point checks, not certificates; being below one at finite dimension gives no bound for
the continuum supremum. No RH claim.
-/

open Matrix MeasureTheory

namespace GppOddCollision

/-! ### 1. Galerkin criterion -/

section Galerkin

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Galerkin criterion.** For `B` symmetric positive definite, `B − 2vvᵀ ⪰ 0` iff
`2 vᵀ B⁻¹ v ≤ 1`. -/
theorem galerkin_criterion (B : Matrix n n ℝ) (hsymm : B.IsSymm) (hdet : IsUnit B.det)
    (hpd : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x)) (v : n → ℝ) :
    (∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x) - 2 * (v ⬝ᵥ x) ^ 2) ↔
      2 * (v ⬝ᵥ (B⁻¹ *ᵥ v)) ≤ 1 := by
  set u : n → ℝ := B⁻¹ *ᵥ v with hu
  have hBu : B *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hs : v ⬝ᵥ u = u ⬝ᵥ (B *ᵥ u) := by rw [hBu, dotProduct_comm]
  have hsym : ∀ y z : n → ℝ, y ⬝ᵥ (B *ᵥ z) = z ⬝ᵥ (B *ᵥ y) := by
    intro y z
    have h1 : y ⬝ᵥ (B *ᵥ z) = (y ᵥ* B) ⬝ᵥ z := Matrix.dotProduct_mulVec _ _ _
    have h2 : y ᵥ* B = B *ᵥ y := by
      have := Matrix.vecMul_transpose B y
      rwa [hsymm] at this
    rw [h1, h2, dotProduct_comm]
  have hs0 : 0 ≤ u ⬝ᵥ (B *ᵥ u) := by
    by_cases h : u = 0
    · simp [h]
    · exact (hpd u h).le
  have hvx : ∀ x : n → ℝ, v ⬝ᵥ x = u ⬝ᵥ (B *ᵥ x) := by
    intro x; rw [hsym u x, hBu, dotProduct_comm]
  have hq : ∀ (x : n → ℝ) (t : ℝ), 0 ≤ x ⬝ᵥ (B *ᵥ x) - 2 * t * (v ⬝ᵥ x) + t ^ 2 * (u ⬝ᵥ (B *ᵥ u)) := by
    intro x t
    have hnn : 0 ≤ (x - t • u) ⬝ᵥ (B *ᵥ (x - t • u)) := by
      by_cases h : x - t • u = 0
      · simp [h]
      · exact (hpd _ h).le
    have e : (x - t • u) ⬝ᵥ (B *ᵥ (x - t • u)) =
        x ⬝ᵥ (B *ᵥ x) - 2 * t * (v ⬝ᵥ x) + t ^ 2 * (u ⬝ᵥ (B *ᵥ u)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, hsym u x, hvx x]
      simp only [smul_eq_mul]
      rw [hsym u x]
      ring
    linarith
  constructor
  · intro h
    have := h u
    rw [← hs] at this
    have hs' : u ⬝ᵥ (B *ᵥ u) = v ⬝ᵥ u := hs.symm
    have hvu : v ⬝ᵥ u = u ⬝ᵥ (B *ᵥ u) := hs
    -- this : 0 ≤ s - 2 * (v ⬝ᵥ u)^2 with s = v ⬝ᵥ u
    have hsnn : 0 ≤ v ⬝ᵥ u := by rw [hvu]; exact hs0
    show 2 * (v ⬝ᵥ u) ≤ 1
    by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg hsnn hsnn]
  · intro h x
    set s := u ⬝ᵥ (B *ᵥ u) with hsdef
    have hvu : v ⬝ᵥ u = s := hs
    rw [hvu] at h
    by_cases hs_pos : 0 < s
    · have := hq x ((v ⬝ᵥ x) / s)
      have h2 : (v ⬝ᵥ x) ^ 2 ≤ s * (x ⬝ᵥ (B *ᵥ x)) := by
        have e : x ⬝ᵥ (B *ᵥ x) - 2 * ((v ⬝ᵥ x) / s) * (v ⬝ᵥ x) + ((v ⬝ᵥ x) / s) ^ 2 * s
            = x ⬝ᵥ (B *ᵥ x) - (v ⬝ᵥ x) ^ 2 / s := by field_simp; ring
        rw [e] at this
        have : (v ⬝ᵥ x) ^ 2 / s ≤ x ⬝ᵥ (B *ᵥ x) := by linarith
        rwa [div_le_iff₀ hs_pos, mul_comm] at this
      have hxx : 0 ≤ x ⬝ᵥ (B *ᵥ x) := by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpd x hx).le
      nlinarith
    · have hs_eq : s = 0 := le_antisymm (not_lt.mp hs_pos) hs0
      have key : ∀ t : ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x) - 2 * t * (v ⬝ᵥ x) := by
        intro t; have := hq x t; rw [hs_eq] at this; linarith
      have hz : v ⬝ᵥ x = 0 := by
        by_contra hne
        have := key ((x ⬝ᵥ (B *ᵥ x) + 1) / (2 * (v ⬝ᵥ x)))
        have e : 2 * ((x ⬝ᵥ (B *ᵥ x) + 1) / (2 * (v ⬝ᵥ x))) * (v ⬝ᵥ x) = x ⬝ᵥ (B *ᵥ x) + 1 := by
          field_simp
        rw [e] at this; linarith
      rw [hz]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        sub_zero]
      by_cases hx : x = 0
      · simp [hx]
      · exact (hpd x hx).le

end Galerkin

/-! ### 2. Exact two-box quantities -/

/-- The normalised box `b_ℓ = ℓ^{-1/2} 1_{[-ℓ/2, ℓ/2]}`. -/
noncomputable def box (ℓ x : ℝ) : ℝ := (Set.Icc (-ℓ / 2) (ℓ / 2)).indicator (fun _ => (Real.sqrt ℓ)⁻¹) x

/-- The two-box vector `f_t = b_ℓ(· + t/2) − b_ℓ(· − t/2)`. -/
noncomputable def twoBox (ℓ t x : ℝ) : ℝ := box ℓ (x + t / 2) - box ℓ (x - t / 2)

/-- The pole functional `v(x) = sinh(x/2)`. -/
noncomputable def poleV (x : ℝ) : ℝ := Real.sinh (x / 2)

lemma integral_poleV (a b : ℝ) :
    ∫ x in a..b, poleV x = 2 * (Real.cosh (b / 2) - Real.cosh (a / 2)) := by
  have : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => 2 * Real.cosh (y / 2)) (poleV x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have h2 := (Real.hasDerivAt_cosh (x / 2)).comp x h1
    have h3 := h2.const_mul 2
    exact h3.congr_deriv (by unfold poleV; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this]
  · ring
  · apply Continuous.intervalIntegrable
    unfold poleV; fun_prop

lemma poleV_mul_box (ℓ s x : ℝ) :
    poleV x * box ℓ (x + s) =
      (Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)).indicator (fun y => (Real.sqrt ℓ)⁻¹ * poleV y) x := by
  unfold box
  by_cases h : x ∈ Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)
  · have h' : x + s ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
      obtain ⟨h1, h2⟩ := h; constructor <;> linarith
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']; ring
  · have h' : x + s ∉ Set.Icc (-ℓ / 2) (ℓ / 2) := by
      intro hh; apply h; obtain ⟨h1, h2⟩ := hh; constructor <;> linarith
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']; ring

lemma poleV_continuous : Continuous poleV := by unfold poleV; fun_prop

lemma integrable_poleV_box (ℓ s : ℝ) :
    Integrable (fun x => poleV x * box ℓ (x + s)) := by
  have : (fun x => poleV x * box ℓ (x + s)) =
      (Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)).indicator (fun y => (Real.sqrt ℓ)⁻¹ * poleV y) := by
    funext x; exact poleV_mul_box ℓ s x
  rw [this]
  exact ((continuous_const.mul poleV_continuous).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

/-- `⟨sinh(·/2), b_ℓ(· + s)⟩ = ℓ^{-1/2} · 2 (cosh((ℓ/2 − s)/2) − cosh((−ℓ/2 − s)/2))`. -/
lemma pair_box (ℓ s : ℝ) (hℓ : 0 ≤ ℓ) :
    ∫ x, poleV x * box ℓ (x + s) =
      (Real.sqrt ℓ)⁻¹ * (2 * (Real.cosh ((ℓ / 2 - s) / 2) - Real.cosh ((-ℓ / 2 - s) / 2))) := by
  have : (fun x => poleV x * box ℓ (x + s)) =
      (Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)).indicator (fun y => (Real.sqrt ℓ)⁻¹ * poleV y) := by
    funext x; exact poleV_mul_box ℓ s x
  rw [this, integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
    integral_poleV]

/-- The exact pairing of the pole functional with the two-box vector:
`⟨sinh(·/2), f_t⟩ = −8 ℓ^{-1/2} sinh(ℓ/4) sinh(t/4)`. -/
theorem box_pairing (ℓ t : ℝ) (hℓ : 0 ≤ ℓ) :
    ∫ x, poleV x * twoBox ℓ t x =
      -8 * (Real.sqrt ℓ)⁻¹ * Real.sinh (ℓ / 4) * Real.sinh (t / 4) := by
  have e' : (fun x => poleV x * twoBox ℓ t x) =
      fun x => poleV x * box ℓ (x + t / 2) - poleV x * box ℓ (x + (-t / 2)) := by
    funext x
    unfold twoBox
    have : x + -t / 2 = x - t / 2 := by ring
    rw [this]; ring
  rw [e', integral_sub (integrable_poleV_box ℓ _) (integrable_poleV_box ℓ _),
    pair_box ℓ _ hℓ, pair_box ℓ _ hℓ]
  have c1 : Real.cosh ((ℓ / 2 - t / 2) / 2) = Real.cosh (ℓ / 4 - t / 4) := by ring_nf
  have c2 : Real.cosh ((-ℓ / 2 - t / 2) / 2) = Real.cosh (ℓ / 4 + t / 4) := by
    rw [← Real.cosh_neg]; ring_nf
  have c3 : Real.cosh ((ℓ / 2 - -t / 2) / 2) = Real.cosh (ℓ / 4 + t / 4) := by ring_nf
  have c4 : Real.cosh ((-ℓ / 2 - -t / 2) / 2) = Real.cosh (ℓ / 4 - t / 4) := by
    rw [← Real.cosh_neg]; ring_nf
  rw [c1, c2, c3, c4, Real.cosh_sub, Real.cosh_add]
  ring

/-- **Pole term of the two-box vector:** `⟨v, f_t⟩² = 4 A_ℓ sinh²(t/4)`, `A_ℓ = H_ℓ(1/2)`. -/
theorem pole_term_two_box (ℓ t : ℝ) (hℓ : 0 < ℓ) :
    (∫ x, poleV x * twoBox ℓ t x) ^ 2 =
      4 * GppFixedWindowCurvature.AA ℓ * Real.sinh (t / 4) ^ 2 := by
  rw [box_pairing ℓ t hℓ.le]
  have hsq : ((Real.sqrt ℓ)⁻¹) ^ 2 = ℓ⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hℓ.le]
  have hc : Real.cosh (ℓ / 2) - 1 = 2 * Real.sinh (ℓ / 4) ^ 2 := by
    have : ℓ / 2 = 2 * (ℓ / 4) := by ring
    rw [this, Real.cosh_two_mul, Real.cosh_sq]; ring
  unfold GppFixedWindowCurvature.AA
  rw [hc]
  have : (-8 * (Real.sqrt ℓ)⁻¹ * Real.sinh (ℓ / 4) * Real.sinh (t / 4)) ^ 2 =
      64 * ((Real.sqrt ℓ)⁻¹) ^ 2 * Real.sinh (ℓ / 4) ^ 2 * Real.sinh (t / 4) ^ 2 := by ring
  rw [this, hsq]
  field_simp
  ring

lemma box_sq_integral (ℓ s : ℝ) (hℓ : 0 < ℓ) : ∫ x, box ℓ (x + s) ^ 2 = 1 := by
  have : (fun x => box ℓ (x + s) ^ 2) =
      (Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)).indicator (fun _ => ℓ⁻¹) := by
    funext x
    unfold box
    by_cases h : x ∈ Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)
    · have h' : x + s ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
        obtain ⟨h1, h2⟩ := h; constructor <;> linarith
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h', inv_pow, Real.sq_sqrt hℓ.le]
    · have h' : x + s ∉ Set.Icc (-ℓ / 2) (ℓ / 2) := by
        intro hh; apply h; obtain ⟨h1, h2⟩ := hh; constructor <;> linarith
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']; simp
  rw [this, integral_indicator_const _ measurableSet_Icc]
  simp only [Real.volume_real_Icc, smul_eq_mul]
  have : ℓ / 2 - s - (-ℓ / 2 - s) = ℓ := by ring
  rw [this, max_eq_left hℓ.le]
  field_simp

lemma box_cross_integral (ℓ t : ℝ) (hℓ : 0 < ℓ) (ht : 0 ≤ t) :
    ∫ x, box ℓ (x + t / 2) * box ℓ (x - t / 2) = ℓ⁻¹ * max (ℓ - t) 0 := by
  have : (fun x => box ℓ (x + t / 2) * box ℓ (x - t / 2)) =
      (Set.Icc (-ℓ / 2 + t / 2) (ℓ / 2 - t / 2)).indicator (fun _ => ℓ⁻¹) := by
    funext x
    unfold box
    have hx : x - t / 2 = x + (-t / 2) := by ring
    by_cases h : x ∈ Set.Icc (-ℓ / 2 + t / 2) (ℓ / 2 - t / 2)
    · have h1 : x + t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
        obtain ⟨h1, h2⟩ := h; constructor <;> linarith
      have h2 : x - t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
        obtain ⟨h1, h2⟩ := h; constructor <;> linarith
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        ← sq, inv_pow, Real.sq_sqrt hℓ.le]
    · rw [Set.indicator_of_notMem h]
      by_cases h1 : x + t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
      · have h2 : x - t / 2 ∉ Set.Icc (-ℓ / 2) (ℓ / 2) := by
          intro hh; apply h; obtain ⟨a1, a2⟩ := hh; obtain ⟨b1, b2⟩ := h1
          constructor <;> linarith
        rw [Set.indicator_of_notMem h2]; simp
      · rw [Set.indicator_of_notMem h1]; simp
  rw [this, integral_indicator_const _ measurableSet_Icc]
  simp only [Real.volume_real_Icc, smul_eq_mul]
  have : ℓ / 2 - t / 2 - (-ℓ / 2 + t / 2) = ℓ - t := by ring
  rw [this, mul_comm]

/-- **Norm of the two-box vector:** `‖f_t‖² = 2 (1 − h_ℓ(t))` with `h_ℓ(t) = max(0, 1 − t/ℓ)`
(for `ℓ > 0`, `t ≥ 0`). -/
theorem norm_sq_two_box (ℓ t : ℝ) (hℓ : 0 < ℓ) (ht : 0 ≤ t) :
    ∫ x, twoBox ℓ t x ^ 2 = 2 * (1 - max 0 (1 - t / ℓ)) := by
  have hint : ∀ s, Integrable (fun x => box ℓ (x + s) ^ 2) := by
    intro s
    have : (fun x => box ℓ (x + s) ^ 2) =
        (Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)).indicator (fun _ => ℓ⁻¹) := by
      funext x
      unfold box
      by_cases h : x ∈ Set.Icc (-ℓ / 2 - s) (ℓ / 2 - s)
      · have h' : x + s ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
          obtain ⟨h1, h2⟩ := h; constructor <;> linarith
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h', inv_pow, Real.sq_sqrt hℓ.le]
      · have h' : x + s ∉ Set.Icc (-ℓ / 2) (ℓ / 2) := by
          intro hh; apply h; obtain ⟨h1, h2⟩ := hh; constructor <;> linarith
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']; simp
    rw [this]
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hcross : Integrable (fun x => box ℓ (x + t / 2) * box ℓ (x - t / 2)) := by
    have : (fun x => box ℓ (x + t / 2) * box ℓ (x - t / 2)) =
        (Set.Icc (-ℓ / 2 + t / 2) (ℓ / 2 - t / 2)).indicator (fun _ => ℓ⁻¹) := by
      funext x
      unfold box
      by_cases h : x ∈ Set.Icc (-ℓ / 2 + t / 2) (ℓ / 2 - t / 2)
      · have h1 : x + t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
          obtain ⟨h1, h2⟩ := h; constructor <;> linarith
        have h2 : x - t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
          obtain ⟨h1, h2⟩ := h; constructor <;> linarith
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          ← sq, inv_pow, Real.sq_sqrt hℓ.le]
      · rw [Set.indicator_of_notMem h]
        by_cases h1 : x + t / 2 ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
        · have h2 : x - t / 2 ∉ Set.Icc (-ℓ / 2) (ℓ / 2) := by
            intro hh; apply h; obtain ⟨a1, a2⟩ := hh; obtain ⟨b1, b2⟩ := h1
            constructor <;> linarith
          rw [Set.indicator_of_notMem h2]; simp
        · rw [Set.indicator_of_notMem h1]; simp
    rw [this]
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have e : (fun x => twoBox ℓ t x ^ 2) =
      fun x => (box ℓ (x + t / 2) ^ 2 + box ℓ (x - t / 2) ^ 2) -
        2 * (box ℓ (x + t / 2) * box ℓ (x - t / 2)) := by
    funext x; unfold twoBox; ring
  have hm : (fun x => box ℓ (x - t / 2) ^ 2) = fun x => box ℓ (x + (-t / 2)) ^ 2 := by
    funext x; congr 3; ring
  have hI2 : Integrable (fun x => box ℓ (x - t / 2) ^ 2) := by rw [hm]; exact hint _
  have h2 : ∫ x, box ℓ (x - t / 2) ^ 2 = 1 := by
    rw [hm]; exact box_sq_integral ℓ _ hℓ
  rw [e, integral_sub (f := fun x => box ℓ (x + t / 2) ^ 2 + box ℓ (x - t / 2) ^ 2)
      (g := fun x => 2 * (box ℓ (x + t / 2) * box ℓ (x - t / 2)))
      ((hint _).add hI2) (hcross.const_mul 2),
    integral_add (hint _) hI2, integral_const_mul,
    box_cross_integral ℓ t hℓ ht, box_sq_integral ℓ _ hℓ, h2]
  have : ℓ⁻¹ * max (ℓ - t) 0 = max 0 (1 - t / ℓ) := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hℓ.le), mul_zero, max_comm]
    congr 1; field_simp
  rw [this]; ring

/-- **Energy defect:** `‖f − g‖² = ‖f‖² + ‖g‖² − 2⟨f, g⟩`; for `g = T_y f` an isometric
translate this is the note's `E_y = 2 (N − h(y))`, `h(y) = ⟨f, T_y f⟩`. -/
theorem energy_defect {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f g : E) :
    ‖f - g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 - 2 * inner ℝ f g := by
  rw [norm_sub_sq_real]; ring

theorem energy_defect_translate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : E) (hiso : ‖g‖ = ‖f‖) :
    ‖f - g‖ ^ 2 = 2 * (‖f‖ ^ 2 - inner ℝ f g) := by
  rw [energy_defect, hiso]; ring

end GppOddCollision
