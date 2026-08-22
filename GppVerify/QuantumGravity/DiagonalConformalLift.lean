import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The diagonal conformal lift `D(s) = (h,hbar) = (s,s)` and `Δ = 2s`

From "Local-field shadow kernels, celestial unitarity, and the adelic principal series"
(Toupin, 2026), §0 and §12. A scalar 1D conformal weight `s` lifts diagonally to a scalar 2D
primary with `h = hbar = s`, hence conformal dimension `Δ := h + hbar = 2s` and spin
`J := h - hbar = 0`. Consequently the 1D shadow involution `s ↦ 1-s` intertwines exactly with
the 2D celestial shadow involution `(h,hbar) ↦ (1-h,1-hbar)` (so `Δ ↦ 2-Δ`), since
`2(1-s) = 2 - Δ`. This is pure algebra — it records the *compatibility* of the two shadow
involutions under the diagonal lift, not any claim that the underlying Hilbert spaces or
physical theories coincide (see `discovery/local_field_shadow/local_shadow_kernel_notes.md`).
-/

namespace GppDiagonalLift

/-- The diagonal conformal lift of a scalar 1D weight `s` to a 2D primary `(h,hbar)`. -/
def D (s : ℝ) : ℝ × ℝ := (s, s)

/-- The 2D conformal dimension `Δ = h + hbar`. -/
def Delta (p : ℝ × ℝ) : ℝ := p.1 + p.2

/-- The 2D spin `J = h - hbar`. -/
def J (p : ℝ × ℝ) : ℝ := p.1 - p.2

/-- The 2D celestial shadow involution `(h,hbar) ↦ (1-h, 1-hbar)`. -/
def Shadow2 (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, 1 - p.2)

/-- The diagonal lift of a scalar weight has `Δ = 2s`. -/
theorem delta_D (s : ℝ) : Delta (D s) = 2 * s := by unfold Delta D; ring

/-- The diagonal lift of a scalar weight has spin `J = 0`. -/
theorem J_D (s : ℝ) : J (D s) = 0 := by unfold J D; ring

/-- **Shadow compatibility**: the 1D shadow `s ↦ 1-s` and the 2D shadow `Shadow2` intertwine
    exactly under the diagonal lift. -/
theorem D_one_sub_eq_shadow2_D (s : ℝ) : D (1 - s) = Shadow2 (D s) := by
  simp [D, Shadow2]

/-- Consequently, on the 2D shadow locus `Δ ↦ 2-Δ`: `Δ (Shadow2 (D s)) = 2 - Δ (D s)`, matching
    `2(1-s) = 2 - 2s`. -/
theorem delta_shadow2_D (s : ℝ) : Delta (Shadow2 (D s)) = 2 - Delta (D s) := by
  rw [← D_one_sub_eq_shadow2_D, delta_D, delta_D]; ring

end GppDiagonalLift
