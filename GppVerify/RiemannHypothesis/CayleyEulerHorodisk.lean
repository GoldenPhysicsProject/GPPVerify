import GppVerify.RiemannHypothesis.CayleyCircleHarmonic

/-!
# The Euler half-plane is a horodisk inside the Cayley critical disk

Source: Codex, GPP-bridge `work/codex/2026-10-13_arithmetic_seed_euler_horodisk_li_circle_moments.md` §2
(PR #11 comment 6160011886).

In the Cayley coordinate `w = β(s) = (s − 1)/s = 1 − 1/s` (`CayleyCircleHarmonic`):
* `euler_horodisk_iff`: `|w − ½| < ½ ⟺ Re s > 1`. The Euler-product half-plane is the tangent
  horodisk of radius ½ centered at ½.
* `horodisk_sub_disk`: the horodisk lies inside the critical disk `|w| < 1` (`Re s > ½`).
* `horodisk_touches`: the horodisk boundary meets the unit circle only at `w = 1` (`s = ∞`).

So the region where the Euler product converges is a proper, zero-free patch tangent to the
mirror circle at the essential singularity. RH is equivalent to `ξ(1/(1 − w))` having no zeros on
the whole disk (Li's setting), and to its logarithm extending from the horodisk across the disk.
That is a reformulation, **not** an estimate. **No RH claim.**
-/

namespace GppCayleyEulerHorodisk

open GppCayleyCircleHarmonic

theorem beta_eq (s : ℂ) (hs : s ≠ 0) : beta s = 1 - 1 / s := by
  unfold beta; field_simp

theorem norm_sub_two_lt_iff (s : ℂ) : ‖s - 2‖ < ‖s‖ ↔ 1 < s.re := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  norm_num
  constructor <;> intro h <;> nlinarith

/-- **Euler horodisk**: `|β(s) − ½| < ½ ⟺ Re s > 1`. -/
theorem euler_horodisk_iff {s : ℂ} (hs : s ≠ 0) : ‖beta s - 1 / 2‖ < 1 / 2 ↔ 1 < s.re := by
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have h : beta s - 1 / 2 = (s - 2) / (2 * s) := by rw [beta_eq s hs]; field_simp; ring
  rw [h, norm_div, norm_mul, Complex.norm_two, div_lt_iff₀ (by positivity), ← norm_sub_two_lt_iff]
  constructor <;> intro h' <;> linarith

/-- The horodisk sits inside the critical disk. -/
theorem horodisk_sub_disk {w : ℂ} (hw : ‖w - 1 / 2‖ < 1 / 2) : ‖w‖ < 1 := by
  calc ‖w‖ = ‖(w - 1 / 2) + 1 / 2‖ := by ring_nf
    _ ≤ ‖w - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
    _ < 1 / 2 + 1 / 2 := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        linarith
    _ = 1 := by norm_num

/-- The horodisk boundary touches the unit circle only at `w = 1`. -/
theorem horodisk_touches {w : ℂ} (h1 : ‖w - 1 / 2‖ = 1 / 2) (h2 : ‖w‖ = 1) : w = 1 := by
  have e1 := congrArg (· ^ 2) h1
  have e2 := congrArg (· ^ 2) h2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at e1 e2
  norm_num at e1 e2
  have hre : w.re = 1 := by nlinarith
  have him : w.im = 0 := by nlinarith
  exact Complex.ext (by simp [hre]) (by simp [him])

end GppCayleyEulerHorodisk
