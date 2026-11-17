import GppVerify.RiemannHypothesis.EventParabola
import GppVerify.RiemannHypothesis.GclSeries

/-!
# The first prime-free interval of the box form: `(0, log 2]`

Below the first prime power the prime part of the box form vanishes, so the box form is
`W(L) = 16 (cosh(L/2) − 1) + C L + 2 ∫₀^L Gcl` with `C = C∞` (`BoxArchimedean.archBox_eq`).  This file proves a
**generic positivity criterion** for `Vm C L := 16 (cosh(L/2) − 1) + C L + 2∫₀^L Gcl` on `(0, b]`
(`Vm_pos`), the "first interval" argument in the audit of GPT's certificate:

* `Vm C 0 = 0`, `Vm'' = 2·curv`, and `curv` changes sign exactly once, at `tStar` (the plastic point);
* if at a point `a > tStar` the slope is negative and `(Vm' a)² < 2·(2 curv a)·Vm a`, then `Vm > 0` on `(0, b]`
  for every `b ≥ a`: on `[a, b]` by the event-parabola step (`EventParabola.gap_positive`), on `[tStar, a]`
  because `Vm` is decreasing there (slope increasing, `≤ Vm'(a) < 0`), on `(0, tStar)` because `Vm` is concave
  with `Vm 0 = 0` and `Vm tStar > 0`.

The numerics (the actual `a`, the rational constants) are in `BoxInitialNumerics.lean`.

**Scope.** Nothing here is positivity of the Weil form in general; `Vm` is the explicit pole + archimedean
expression on the prime-free interval.

No `sorry`, no axiom.
-/

open Real Set MeasureTheory Filter Topology
open GppBoxCurvature GppGclSeries GppEventParabola GppPlastic GppBoxArchimedean

noncomputable section

namespace GppBoxInitial

/-- The prime-free box form with archimedean constant `C`. -/
def Vm (C L : ℝ) : ℝ :=
  16 * (Real.cosh (L / 2) - 1) + C * L + 2 * ∫ s in (0 : ℝ)..L, Gcl s

/-- Its derivative. -/
def vslope (C L : ℝ) : ℝ := 8 * Real.sinh (L / 2) + C + 2 * Gcl L

theorem Vm_zero (C : ℝ) : Vm C 0 = 0 := by simp [Vm]

theorem hasDerivAt_Vm (C : ℝ) {L : ℝ} (hL : 0 < L) : HasDerivAt (Vm C) (vslope C L) L := by
  have hFTC : HasDerivAt (fun L => ∫ t in (0 : ℝ)..L, Gcl t) (Gcl L) L :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_Gcl hL)
      (continuousOn_Gcl.stronglyMeasurableAtFilter isOpen_Ioi L hL)
      (hasDerivAt_Gcl hL).continuousAt
  have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2)) (Real.sinh (L / 2) * (1 / 2)) L :=
    ((hasDerivAt_id L).div_const 2).cosh
  have := (((hc.sub_const 1).const_mul 16).add ((hasDerivAt_id L).const_mul C)).add (hFTC.const_mul 2)
  unfold vslope
  refine this.congr_deriv ?_
  simp; ring

theorem hasDerivAt_vslope (C : ℝ) {L : ℝ} (hL : 0 < L) : HasDerivAt (vslope C) (2 * curv L) L := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sinh (y / 2)) (Real.cosh (L / 2) * (1 / 2)) L :=
    ((hasDerivAt_id L).div_const 2).sinh
  have hG := hasDerivAt_Gcl hL
  have := (((h1.const_mul 8).add_const C).add (hG.const_mul 2))
  unfold vslope
  refine this.congr_deriv ?_
  rw [← second_algebra hL]
  ring

theorem continuousOn_Vm (C : ℝ) {b : ℝ} (hb : 0 < b) : ContinuousOn (Vm C) (Icc 0 b) := by
  have hint : IntegrableOn Gcl (uIcc 0 b) := by
    rw [uIcc_of_le hb.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mp (intervalIntegrable_Gcl hb)
  have h1 := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hb.le] at h1
  unfold Vm
  have h2 : ContinuousOn (fun L : ℝ => 16 * (Real.cosh (L / 2) - 1) + C * L) (Icc 0 b) := by fun_prop
  exact h2.add (h1.const_mul 2)

theorem continuousOn_vslope (C : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (vslope C) (Icc a b) :=
  fun _ hy => (hasDerivAt_vslope C (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt

/-- On `[tStar, a]` the slope is increasing, so `vslope C y ≤ vslope C a`. -/
theorem vslope_le {C a : ℝ} (hta : tStar < a) {y : ℝ} (hy : y ∈ Icc tStar a) :
    vslope C y ≤ vslope C a := by
  have hmono : MonotoneOn (vslope C) (Icc tStar a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc tStar a)
    · exact fun z hz => (hasDerivAt_vslope C (lt_of_lt_of_le tStar_pos hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hasDerivAt_vslope C (tStar_pos.trans hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_vslope C (tStar_pos.trans hz.1)).deriv]
      have := curv_pos_of_gt hz.1
      linarith
  exact hmono hy ⟨hta.le, le_rfl⟩ hy.2

/-- **The first-interval criterion.** Suppose `a > tStar`, `vslope C a < 0` and
`(vslope C a)² < 2·(2 curv a)·Vm C a`.  Then `Vm C > 0` on `(0, b]` for every `b ≥ a`. -/
theorem Vm_pos {C a b : ℝ} (hta : tStar < a) (hab : a ≤ b) (hneg : vslope C a < 0)
    (hcert : vslope C a ^ 2 < 2 * (2 * curv a) * Vm C a) {L : ℝ} (hL : L ∈ Ioc 0 b) :
    0 < Vm C L := by
  have ha : 0 < a := tStar_pos.trans hta
  have hca : 0 < curv a := curv_pos_of_gt hta
  have hVa : 0 < Vm C a := by
    have h0 : 0 ≤ vslope C a ^ 2 := sq_nonneg _
    have : 0 < 2 * (2 * curv a) * Vm C a := lt_of_le_of_lt h0 hcert
    by_contra hneg'
    push Not at hneg'
    nlinarith
  -- region [tStar, a]: Vm is decreasing
  have hdec : ∀ x ∈ Icc tStar a, Vm C a ≤ Vm C x := by
    have hanti : AntitoneOn (Vm C) (Icc tStar a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc tStar a)
      · exact fun z hz => (hasDerivAt_Vm C (lt_of_lt_of_le tStar_pos hz.1)).continuousAt.continuousWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        exact (hasDerivAt_Vm C (tStar_pos.trans hz.1)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        rw [(hasDerivAt_Vm C (tStar_pos.trans hz.1)).deriv]
        have := vslope_le (C := C) hta ⟨hz.1.le, hz.2.le⟩
        linarith
    intro x hx
    exact hanti hx ⟨hta.le, le_rfl⟩ hx.2
  have hVt : 0 < Vm C tStar := lt_of_lt_of_le hVa (hdec tStar ⟨le_rfl, hta.le⟩)
  by_cases h1 : a ≤ L
  · -- region [a, b]: the event-parabola step
    refine gap_positive (f := Vm C) (g := vslope C) (h := fun y => 2 * curv y) (a := a) (b := b)
      (k := 2 * curv a) hab (by linarith) (continuousOn_Vm C (ha.trans_le hab) |>.mono
        (Icc_subset_Icc ha.le le_rfl)) (continuousOn_vslope C ha) ?_ ?_ ?_ hcert ⟨h1, hL.2⟩
    · intro x hx; exact hasDerivAt_Vm C (ha.trans hx.1)
    · intro x hx; exact hasDerivAt_vslope C (ha.trans hx.1)
    · intro x hx
      have := curv_monotoneOn (mem_Ioi.mpr ha) (mem_Ioi.mpr (ha.trans hx.1)) hx.1.le
      linarith
  · push Not at h1
    by_cases h2 : tStar ≤ L
    · exact lt_of_lt_of_le hVa (hdec L ⟨h2, h1.le⟩)
    · push Not at h2
      -- region (0, tStar): concavity with Vm 0 = 0
      have hconc : ConcaveOn ℝ (Icc 0 tStar) (Vm C) := by
        have hderiv : ∀ y ∈ Ioo 0 tStar, deriv (Vm C) y = vslope C y := fun y hy =>
          (hasDerivAt_Vm C hy.1).deriv
        apply concaveOn_of_deriv2_nonpos (convex_Icc 0 tStar) (continuousOn_Vm C tStar_pos)
        · intro z hz
          rw [interior_Icc] at hz
          exact (hasDerivAt_Vm C hz.1).differentiableAt.differentiableWithinAt
        · intro z hz
          rw [interior_Icc] at hz
          have hd : DifferentiableAt ℝ (vslope C) z := (hasDerivAt_vslope C hz.1).differentiableAt
          refine (hd.differentiableWithinAt).congr (fun y hy => ?_) (hderiv z hz)
          rw [interior_Icc] at hy
          exact hderiv y hy
        · intro z hz
          rw [interior_Icc] at hz
          have hev : deriv (Vm C) =ᶠ[nhds z] vslope C := by
            filter_upwards [Ioo_mem_nhds hz.1 hz.2] with y hy using hderiv y hy
          simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
          rw [hev.deriv_eq, (hasDerivAt_vslope C hz.1).deriv]
          have := curv_neg_of_lt hz.1 hz.2
          linarith
      have hs : 0 < L / tStar := div_pos hL.1 tStar_pos
      have hs1 : L / tStar ≤ 1 := by rw [div_le_one tStar_pos]; exact h2.le
      have key := hconc.2 (left_mem_Icc.mpr tStar_pos.le) (right_mem_Icc.mpr tStar_pos.le)
        (by linarith : 0 ≤ 1 - L / tStar) hs.le (by ring)
      simp only [smul_eq_mul, mul_zero, zero_add, Vm_zero] at key
      have e : L / tStar * tStar = L := div_mul_cancel₀ L tStar_pos.ne'
      rw [e] at key
      have : 0 < L / tStar * Vm C tStar := mul_pos hs hVt
      linarith

end GppBoxInitial
