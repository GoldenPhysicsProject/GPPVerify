import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The four-face Gram determinant and the divided-difference Gram

Let `B` be a symmetric bilinear form on a real vector space `V` with a vector `H` in its radical,
odd classes `Ou, Ov` and even classes `Eu, Ev` with all four cross-parity pairings zero. The four
faces at magnitudes `r, s` (with `u = r^2`, `v = s^2`) are
`H ± r Ou + u Eu` and `H ± s Ov + v Ev` (`face`).

* `B_face`: the pairing of two faces, `B(face r σ, face r' σ') = σ σ' r r' B(O, O') + r² r'² B(E, E')`.
* `four_face_det`: the Gram determinant of the four faces is
  `16 r⁶ s⁶ · (B(Ou,Ou) B(Ov,Ov) - B(Ou,Ov)²) · (B(Eu,Eu) B(Ev,Ev) - B(Eu,Ev)²)`.
* `gram_eq_sq_mul_divdiff`: for `u ≠ v`, the Gram determinant of `P u, P v` is
  `(v - u)² · d_P(u, v)`, with `d_P` the Gram determinant of `P u` and the divided difference
  `(P v - P u)/(v - u)`.
* `four_face_det_divdiff`: the Gram determinant of the four faces is
  `16 r⁶ s⁶ (u - v)⁴ · d_O(u, v) · d_E(u, v)`.
* `divDiffGram`, `differentiable_divDiffGram_right`: for a continuous bilinear form on a complex
  Banach space and an entire packet curve `P : ℂ → E`, the divided-difference Gram
  `d_P(u, v)` (with the diagonal given by `deriv`, via `dslope`) is entire in `v` for each fixed
  `u`; `divDiffGram_of_ne` ties it to the Gram determinant of `P u, P v`;
  `differentiable_dslope_joint` and `differentiable_divDiffGram` give joint holomorphy on `ℂ × ℂ`
  (the divided difference is `∫₀¹ P'(u + t (v - u)) dt`, differentiated under the integral);
  `divDiffGram_symm_all` gives the symmetry `d_P(u, v) = d_P(v, u)` for all `u, v`.
-/

namespace GppFourFace
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def face (H O E : V) (r σ : ℝ) : V := H + (σ * r) • O + (r ^ 2) • E

theorem B_face (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {H O E O' E' : V}
    (hH : ∀ x, B H x = 0) (h1 : B O E' = 0) (h2 : B O' E = 0) (r σ r' σ' : ℝ) :
    B (face H O E r σ) (face H O' E' r' σ') =
      (σ * r) * (σ' * r') * B O O' + (r ^ 2) * (r' ^ 2) * B E E' := by
  have hH' : ∀ x, B x H = 0 := fun x => by rw [hB, hH]
  have h1' : B E' O = 0 := by rw [hB]; exact h1
  have h2' : B E O' = 0 := by rw [hB]; exact h2
  simp only [face, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hH,
    hH', h1, h2']
  ring

theorem four_face_det (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {H Ou Ov Eu Ev : V} (hH : ∀ x, B H x = 0) (h_uu : B Ou Eu = 0) (h_uv : B Ou Ev = 0)
    (h_vu : B Ov Eu = 0) (h_vv : B Ov Ev = 0) (r s : ℝ) :
    (Matrix.of fun i j : Fin 4 => B (![face H Ou Eu r 1, face H Ou Eu r (-1), face H Ov Ev s 1,
        face H Ov Ev s (-1)] i) (![face H Ou Eu r 1, face H Ou Eu r (-1), face H Ov Ev s 1,
        face H Ov Ev s (-1)] j)).det =
      16 * r ^ 6 * s ^ 6 * ((B Ou Ou * B Ov Ov - B Ou Ov ^ 2) * (B Eu Eu * B Ev Ev - B Eu Ev ^ 2)) := by
  have hOvOu : B Ov Ou = B Ou Ov := hB _ _
  have hEvEu : B Ev Eu = B Eu Ev := hB _ _
  have hvuE : B Ev Ou = 0 := by rw [hB]; exact h_uv
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, B_face B hB hH, h_uu, h_uv,
    h_vu, h_vv, hOvOu, hEvEu]
  ring

/-- The Gram quantity of two vectors. -/
def gram (B : LinearMap.BilinForm ℝ V) (x y : V) : ℝ := B x x * B y y - B x y ^ 2

/-- The divided-difference Gram `d_P(u, v)`: Gram of `P u` and `(P v - P u)/(v - u)`. -/
noncomputable def dP (B : LinearMap.BilinForm ℝ V) (Pu Pv : V) (u v : ℝ) : ℝ :=
  gram B Pu ((v - u)⁻¹ • (Pv - Pu))

theorem gram_eq_sq_mul_divdiff (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {Pu Pv : V} {u v : ℝ} (huv : u ≠ v) : gram B Pu Pv = (v - u) ^ 2 * dP B Pu Pv u v := by
  have hc : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hPv : Pv = Pu + (v - u) • ((v - u)⁻¹ • (Pv - Pu)) := by
    rw [smul_inv_smul₀ hc]; abel
  set D := (v - u)⁻¹ • (Pv - Pu) with hD
  unfold dP gram
  rw [← hD]
  have e1 : B Pu Pv = B Pu Pu + (v - u) * B Pu D := by
    conv_lhs => rw [hPv]
    simp only [map_add, map_smul, smul_eq_mul]
  have e2 : B Pv Pv = B Pu Pu + 2 * (v - u) * B Pu D + (v - u) ^ 2 * B D D := by
    conv_lhs => rw [hPv]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB D Pu]; ring
  rw [e1, e2]; ring

/-- The four-face Gram determinant in terms of the divided-difference Gram determinants. -/
theorem four_face_det_divdiff (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {H Ou Ov Eu Ev : V} (hH : ∀ x, B H x = 0) (h_uu : B Ou Eu = 0) (h_uv : B Ou Ev = 0)
    (h_vu : B Ov Eu = 0) (h_vv : B Ov Ev = 0) {r s : ℝ} (hrs : r ^ 2 ≠ s ^ 2) :
    (Matrix.of fun i j : Fin 4 => B (![face H Ou Eu r 1, face H Ou Eu r (-1), face H Ov Ev s 1,
        face H Ov Ev s (-1)] i) (![face H Ou Eu r 1, face H Ou Eu r (-1), face H Ov Ev s 1,
        face H Ov Ev s (-1)] j)).det =
      16 * r ^ 6 * s ^ 6 * (r ^ 2 - s ^ 2) ^ 4 * (dP B Ou Ov (r ^ 2) (s ^ 2) *
        dP B Eu Ev (r ^ 2) (s ^ 2)) := by
  rw [four_face_det B hB hH h_uu h_uv h_vu h_vv r s]
  have hO := gram_eq_sq_mul_divdiff B hB (Pu := Ou) (Pv := Ov) hrs
  have hE := gram_eq_sq_mul_divdiff B hB (Pu := Eu) (Pv := Ev) hrs
  unfold gram at hO hE
  rw [hO, hE]; ring

/-! ### Joint entireness of the divided-difference Gram -/

section Affine

open MeasureTheory Set Metric Filter Topology

/-- The affine evaluation `x ↦ (1 - t) x.1 + t x.2` as a continuous linear map. -/
noncomputable def affEval (t : ℝ) : ℂ × ℂ →L[ℂ] ℂ :=
  (1 - (t : ℂ)) • ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ

lemma affEval_apply (t : ℝ) (x : ℂ × ℂ) : affEval t x = (1 - (t : ℂ)) * x.1 + (t : ℂ) * x.2 := by
  simp [affEval]

lemma continuous_affEval : Continuous fun t : ℝ => affEval t := by
  unfold affEval
  fun_prop

lemma norm_affEval_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ‖affEval t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [affEval_apply, one_mul]
  have a : ‖(1 - (t : ℂ))‖ = 1 - t := by
    rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have b : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg h0]
  calc ‖(1 - (t : ℂ)) * x.1 + (t : ℂ) * x.2‖
      ≤ ‖(1 - (t : ℂ)) * x.1‖ + ‖(t : ℂ) * x.2‖ := norm_add_le _ _
    _ = (1 - t) * ‖x.1‖ + t * ‖x.2‖ := by rw [norm_mul, norm_mul, a, b]
    _ ≤ (1 - t) * ‖x‖ + t * ‖x‖ := by
        gcongr
        · exact norm_fst_le x
        · exact norm_snd_le x
    _ = ‖x‖ := by ring

end Affine


section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divided-difference Gram of an entire curve `P` against a continuous bilinear form `B`,
with the diagonal value given by `dslope`. -/
noncomputable def divDiffGram (B : E →L[ℂ] E →L[ℂ] ℂ) (P : ℂ → E) (u v : ℂ) : ℂ :=
  B (P u) (P u) * B (dslope P u v) (dslope P u v) - B (P u) (dslope P u v) ^ 2

/-- For each `u`, `v ↦ d_P(u, v)` is entire. -/
theorem differentiable_divDiffGram_right (B : E →L[ℂ] E →L[ℂ] ℂ) {P : ℂ → E}
    (hP : Differentiable ℂ P) (u : ℂ) : Differentiable ℂ (divDiffGram B P u) := by
  have hD : Differentiable ℂ (dslope P u) := by
    have := (Complex.differentiableOn_dslope (f := P) (s := Set.univ) (c := u)
      Filter.univ_mem).mpr hP.differentiableOn
    exact differentiableOn_univ.mp this
  have hBD : Differentiable ℂ fun v => B (dslope P u v) := B.differentiable.comp hD
  have h1 : Differentiable ℂ fun v => B (dslope P u v) (dslope P u v) := hBD.clm_apply hD
  have h2 : Differentiable ℂ fun v => B (P u) (dslope P u v) :=
    (B (P u)).differentiable.comp hD
  unfold divDiffGram
  exact (h1.const_mul _).sub (h2.pow 2)

omit [CompleteSpace E] in
/-- Off the diagonal, the Gram determinant of `P u, P v` is `(v - u)² d_P(u, v)`. -/
theorem divDiffGram_of_ne (B : E →L[ℂ] E →L[ℂ] ℂ) (hB : ∀ x y, B x y = B y x) (P : ℂ → E)
    (u v : ℂ) :
    B (P u) (P u) * B (P v) (P v) - B (P u) (P v) ^ 2 = (v - u) ^ 2 * divDiffGram B P u v := by
  have hPv : P v = P u + (v - u) • dslope P u v := by
    have := sub_smul_dslope P u v
    rw [this]; abel
  set D := dslope P u v with hD
  unfold divDiffGram
  rw [← hD]
  have e1 : B (P u) (P v) = B (P u) (P u) + (v - u) * B (P u) D := by
    conv_lhs => rw [hPv]
    simp
  have e2 : B (P v) (P v) = B (P u) (P u) + 2 * (v - u) * B (P u) D + (v - u) ^ 2 * B D D := by
    conv_lhs => rw [hPv]
    simp only [map_add, map_smul, smul_eq_mul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hB D (P u)]; ring
  rw [e1, e2]; ring

omit [CompleteSpace E] in
/-- Symmetry `d_P(u, v) = d_P(v, u)` off the diagonal. -/
theorem divDiffGram_symm (B : E →L[ℂ] E →L[ℂ] ℂ) (hB : ∀ x y, B x y = B y x) (P : ℂ → E)
    {u v : ℂ} (huv : u ≠ v) : divDiffGram B P u v = divDiffGram B P v u := by
  have h1 := divDiffGram_of_ne B hB P u v
  have h2 := divDiffGram_of_ne B hB P v u
  have hne : (v - u) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm huv))
  have hsq : (u - v) ^ 2 = (v - u) ^ 2 := by ring
  rw [hB (P v) (P u), mul_comm (B (P v) (P v))] at h2
  rw [hsq] at h2
  have : (v - u) ^ 2 * divDiffGram B P u v = (v - u) ^ 2 * divDiffGram B P v u := by
    rw [← h1, ← h2]
  exact mul_left_cancel₀ hne this

open MeasureTheory Set Metric Filter Topology in
theorem differentiable_dslope_joint {P : ℂ → E} (hP : Differentiable ℂ P) :
    Differentiable ℂ fun x : ℂ × ℂ => dslope P x.1 x.2 := by
  have hP1 : ∀ z, AnalyticAt ℂ (deriv P) z := fun z => (hP.analyticAt z).deriv
  have hP2 : ∀ z, AnalyticAt ℂ (deriv (deriv P)) z := fun z => (hP1 z).deriv
  have hd1 : Differentiable ℂ (deriv P) := fun z => (hP1 z).differentiableAt
  have hc2 : Continuous (deriv (deriv P)) := continuous_iff_continuousAt.mpr fun z =>
    (hP2 z).continuousAt
  -- the integral representation
  have hrep : ∀ x : ℂ × ℂ, dslope P x.1 x.2 =
      ∫ t in Ioc (0 : ℝ) 1, deriv P (affEval t x) := by
    intro x
    obtain ⟨u, v⟩ := x
    simp only at *
    have haff : ∀ t : ℝ, affEval t (u, v) = u + (t : ℂ) * (v - u) := fun t => by
      rw [affEval_apply]; ring
    simp only [haff]
    have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u + (s : ℂ) * (v - u)) (v - u) t := by
      intro t
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (v - u)).const_add u
    have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => P (u + (s : ℂ) * (v - u)))
        ((v - u) • deriv P (u + (t : ℂ) * (v - u))) t := by
      intro t
      have h1 := ((hP (u + (t : ℂ) * (v - u))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
        (hg t)
      have h2 : (fderiv ℂ P (u + (t : ℂ) * (v - u))) (v - u) =
          (v - u) • deriv P (u + (t : ℂ) * (v - u)) := by
        have := (hP (u + (t : ℂ) * (v - u))).hasDerivAt.hasFDerivAt
        rw [this.fderiv]; simp
      simpa [h2, Function.comp_def] using h1
    have hcont : Continuous fun t : ℝ => (v - u) • deriv P (u + (t : ℂ) * (v - u)) := by
      have : Continuous fun t : ℝ => u + (t : ℂ) * (v - u) := by fun_prop
      exact continuous_const.smul (hd1.continuous.comp this)
    have hftc : ∫ t in (0 : ℝ)..1, (v - u) • deriv P (u + (t : ℂ) * (v - u)) = P v - P u := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
        (f := fun s : ℝ => P (u + (s : ℂ) * (v - u)))
        (f' := fun t : ℝ => (v - u) • deriv P (u + (t : ℂ) * (v - u)))
        (fun t _ => hd t) (hcont.intervalIntegrable _ _)
      simpa using this
    rw [← intervalIntegral.integral_of_le zero_le_one]
    by_cases huv : v = u
    · subst huv
      simp
    · have hne : v - u ≠ 0 := sub_ne_zero.mpr huv
      rw [intervalIntegral.integral_smul] at hftc
      rw [dslope_of_ne P huv, slope_def_module, ← hftc, smul_smul, inv_mul_cancel₀ hne,
        one_smul]
  have hfun : (fun x : ℂ × ℂ => dslope P x.1 x.2) =
      fun x => ∫ t in Ioc (0 : ℝ) 1, deriv P (affEval t x) := funext hrep
  rw [hfun]
  intro x₀
  -- derivative data
  let d2 : ℝ → ℂ × ℂ → E := fun t x => deriv (deriv P) (affEval t x)
  let F' : ℂ × ℂ → ℝ → (ℂ × ℂ →L[ℂ] E) := fun x t =>
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (d2 t x)).comp (affEval t)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (‖x₀‖ + 1)).exists_bound_of_continuousOn
    hc2.continuousOn
  have hFcont : ∀ x : ℂ × ℂ, Continuous fun t : ℝ => deriv P (affEval t x) := fun x =>
    hd1.continuous.comp (by simp only [affEval_apply]; fun_prop)
  have hF'cont : Continuous fun t : ℝ => F' x₀ t := by
    have h1 : Continuous fun t : ℝ => d2 t x₀ :=
      hc2.comp (by simp only [affEval_apply]; fun_prop)
    have h2 : Continuous fun t : ℝ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (d2 t x₀) :=
      (ContinuousLinearMap.smulRightL ℂ ℂ E (1 : ℂ →L[ℂ] ℂ)).continuous.comp h1
    exact h2.clm_comp continuous_affEval
  have key : HasFDerivAt (fun x : ℂ × ℂ => ∫ t in Ioc (0 : ℝ) 1, deriv P (affEval t x))
      (∫ t in Ioc (0 : ℝ) 1, F' x₀ t) x₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (s := ball x₀ 1) (bound := fun _ => C) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (hFcont x).aestronglyMeasurable
    · exact (hFcont x₀).integrableOn_Ioc
    · exact hF'cont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
      have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have := mem_ball_iff_norm.mp hx
        calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
          _ ≤ ‖x₀‖ + 1 := by linarith
      have hpt : ‖affEval t x‖ ≤ ‖x‖ := by
        calc ‖affEval t x‖ ≤ ‖affEval t‖ * ‖x‖ := (affEval t).le_opNorm x
          _ ≤ 1 * ‖x‖ := by
              gcongr
              exact norm_affEval_le ht.1.le ht.2
          _ = ‖x‖ := one_mul _
      have hmem : affEval t x ∈ closedBall (0 : ℂ) (‖x₀‖ + 1) := by
        rw [mem_closedBall, dist_zero_right]; linarith
      calc ‖F' x t‖ ≤ ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (d2 t x)‖ * ‖affEval t‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C := by
            rw [ContinuousLinearMap.norm_smulRight_apply]
            have h1 : ‖(1 : ℂ →L[ℂ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
            have h2 : ‖d2 t x‖ ≤ C := hC _ hmem
            have h3 : ‖affEval t‖ ≤ 1 := norm_affEval_le ht.1.le ht.2
            have h4 : 0 ≤ ‖d2 t x‖ := norm_nonneg _
            have h5 : 0 ≤ ‖affEval t‖ := norm_nonneg _
            have h6 : 0 ≤ C := h4.trans h2
            calc ‖(1 : ℂ →L[ℂ] ℂ)‖ * ‖d2 t x‖ * ‖affEval t‖ ≤ 1 * C * 1 := by gcongr
              _ = C := by ring
    · exact integrable_const C
    · refine Filter.Eventually.of_forall fun t x _ => ?_
      have h1 : HasDerivAt (deriv P) (deriv (deriv P) (affEval t x)) (affEval t x) :=
        (hd1 (affEval t x)).hasDerivAt
      have h2 : HasFDerivAt (fun y : ℂ × ℂ => affEval t y) (affEval t) x := (affEval t).hasFDerivAt
      exact h1.hasFDerivAt.comp x h2
  exact key.differentiableAt


/-- **Joint entireness.** For a continuous bilinear form `B` on a complex Banach space and an
entire curve `P`, the divided-difference Gram `(u, v) ↦ d_P(u, v)` is holomorphic on `ℂ × ℂ`. -/
theorem differentiable_divDiffGram (B : E →L[ℂ] E →L[ℂ] ℂ) {P : ℂ → E}
    (hP : Differentiable ℂ P) : Differentiable ℂ fun p : ℂ × ℂ => divDiffGram B P p.1 p.2 := by
  have hD := differentiable_dslope_joint hP
  have hPu : Differentiable ℂ fun p : ℂ × ℂ => P p.1 := hP.comp differentiable_fst
  have hBPu : Differentiable ℂ fun p : ℂ × ℂ => B (P p.1) := B.differentiable.comp hPu
  have hBD : Differentiable ℂ fun p : ℂ × ℂ => B (dslope P p.1 p.2) := B.differentiable.comp hD
  have h1 : Differentiable ℂ fun p : ℂ × ℂ => B (P p.1) (P p.1) := hBPu.clm_apply hPu
  have h2 : Differentiable ℂ fun p : ℂ × ℂ => B (dslope P p.1 p.2) (dslope P p.1 p.2) :=
    hBD.clm_apply hD
  have h3 : Differentiable ℂ fun p : ℂ × ℂ => B (P p.1) (dslope P p.1 p.2) := hBPu.clm_apply hD
  unfold divDiffGram
  exact (h1.mul h2).sub (h3.pow 2)

omit [CompleteSpace E] in
/-- Full symmetry `d_P(u, v) = d_P(v, u)`, by cases (the diagonal is `rfl`). -/
theorem divDiffGram_symm_all (B : E →L[ℂ] E →L[ℂ] ℂ) (hB : ∀ x y, B x y = B y x) (P : ℂ → E)
    (u v : ℂ) : divDiffGram B P u v = divDiffGram B P v u := by
  by_cases huv : u = v
  · rw [huv]
  · exact divDiffGram_symm B hB P huv

end Complex

#print axioms B_face
#print axioms four_face_det
#print axioms gram_eq_sq_mul_divdiff
#print axioms four_face_det_divdiff
#print axioms differentiable_divDiffGram_right
#print axioms divDiffGram_of_ne
#print axioms divDiffGram_symm
#print axioms differentiable_dslope_joint
#print axioms differentiable_divDiffGram
#print axioms divDiffGram_symm_all

end GppFourFace
