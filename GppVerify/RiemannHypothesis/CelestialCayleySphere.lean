import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The Cayley sphere: shadow, conjugation and Hermitian mirror as celestial involutions

Source: Codex, GPP-bridge `work/codex/2026-10-13_spherical_double_cayley_spinor_null_cone_geometry.md`
(PR #11 comment 6159582238).

Stereographic projection of the Cayley coordinate `w = (s − 1)/s` is
`n(w) = (2 Re w, 2 Im w, 1 − |w|²)/(1 + |w|²) ∈ S²`. This file proves:
* `nz_eq_zero_iff`: `n_z = 0 ⟺ |w| = 1`. The critical line is the celestial equator.
* `n_conj`: complex conjugation `C : w ↦ w̄` acts as `(n_x, −n_y, n_z)`.
* `n_inv`: the functional shadow `Q : w ↦ 1/w` acts as `(n_x, −n_y, −n_z)`, a 180° rotation.
* `n_inv_conj`: the Hermitian mirror `D : w ↦ 1/w̄` acts as `(n_x, n_y, −n_z)`, the equator
  reflection, which fixes the critical equator pointwise.
* `spinor_null`: the Hermitian matrix `X = c·λλ†` with `λ = (1, w)` has determinant `0`, a null
  vector. With `c = 2E/(1 + |w|²)` its components are `(T, X, Y, Z) = E·(1, n(w))`
  (`spinor_components`).

This is massless spinor kinematics on the celestial sphere: a 2D doubled surface plus a null cone.
It is not gravity, and not a derivation of a 4D bulk. **No RH claim.**
-/

namespace GppCelestialCayleySphere

open Complex

/-- `n_x(w) = 2 Re w / (1 + |w|²)`. -/
noncomputable def nx (w : ℂ) : ℝ := 2 * w.re / (1 + Complex.normSq w)
/-- `n_y(w) = 2 Im w / (1 + |w|²)`. -/
noncomputable def ny (w : ℂ) : ℝ := 2 * w.im / (1 + Complex.normSq w)
/-- `n_z(w) = (1 − |w|²)/(1 + |w|²)`. -/
noncomputable def nz (w : ℂ) : ℝ := (1 - Complex.normSq w) / (1 + Complex.normSq w)

theorem one_add_normSq_pos (w : ℂ) : 0 < 1 + Complex.normSq w := by
  have := Complex.normSq_nonneg w; linarith

/-- **The critical line is the equator**: `n_z = 0 ⟺ |w| = 1`. -/
theorem nz_eq_zero_iff (w : ℂ) : nz w = 0 ↔ ‖w‖ = 1 := by
  unfold nz
  rw [div_eq_zero_iff, or_iff_left (one_add_normSq_pos w).ne', sub_eq_zero,
    Complex.normSq_eq_norm_sq]
  constructor
  · intro h; have := norm_nonneg w; nlinarith
  · intro h; rw [h]; norm_num

theorem n_conj (w : ℂ) :
    nx (starRingEnd ℂ w) = nx w ∧ ny (starRingEnd ℂ w) = -ny w ∧ nz (starRingEnd ℂ w) = nz w := by
  simp [nx, ny, nz, Complex.normSq_conj, neg_div]

/-- **Functional shadow** `w ↦ 1/w`: `(n_x, −n_y, −n_z)`. -/
theorem n_inv {w : ℂ} (hw : w ≠ 0) : nx w⁻¹ = nx w ∧ ny w⁻¹ = -ny w ∧ nz w⁻¹ = -nz w := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hre : w⁻¹.re = w.re / Complex.normSq w := Complex.inv_re w
  have him : w⁻¹.im = -w.im / Complex.normSq w := Complex.inv_im w
  refine ⟨?_, ?_, ?_⟩ <;> simp only [nx, ny, nz, hre, him, map_inv₀] <;> field_simp <;> ring

/-- **Hermitian mirror** `w ↦ 1/w̄`: `(n_x, n_y, −n_z)`, the equator reflection. -/
theorem n_inv_conj {w : ℂ} (hw : w ≠ 0) :
    nx (starRingEnd ℂ w)⁻¹ = nx w ∧ ny (starRingEnd ℂ w)⁻¹ = ny w ∧
      nz (starRingEnd ℂ w)⁻¹ = -nz w := by
  have hw' : starRingEnd ℂ w ≠ 0 := (map_ne_zero _).mpr hw
  obtain ⟨a1, a2, a3⟩ := n_inv hw'
  obtain ⟨b1, b2, b3⟩ := n_conj w
  exact ⟨a1.trans b1, by rw [a2, b2, neg_neg], by rw [a3, b3]⟩

/-- **Null spinor vector**: `det (c λλ†) = 0` for `λ = (1, w)`. -/
theorem spinor_null (c : ℝ) (w : ℂ) :
    (c : ℂ) * 1 * ((c : ℂ) * (w * starRingEnd ℂ w)) - (c * starRingEnd ℂ w) * (c * w) = 0 := by
  ring

/-- **Components**: with `c = 2E/(1+|w|²)`, `c λλ†` has `T = E`, `Z = E n_z`, `X = E n_x`,
`Y = E n_y`, where `T ± Z` are the diagonal entries and `X + iY` is the lower-left entry. -/
theorem spinor_components (E : ℝ) (w : ℂ) :
    let c := 2 * E / (1 + Complex.normSq w)
    (c * 1 + c * Complex.normSq w) / 2 = E ∧ (c * 1 - c * Complex.normSq w) / 2 = E * nz w ∧
      c * w.re = E * nx w ∧ c * w.im = E * ny w := by
  have hp := (one_add_normSq_pos w).ne'
  intro c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try simp only [c, nx, ny, nz]) <;> field_simp

end GppCelestialCayleySphere
