import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination

/-!
# The golden geodesic: Hecke norm identity and Weyl reflection

Source: Codex, `work/codex/2026-10-13_golden_hecke_toroidal_galois_projection_weyl_boundary.md`
(GPP-bridge PR #11 comment 6140674618). It follows Daniel Toupin's golden Haar-torus route.
Historical credit for the toroidal period goes to Hecke and Zagier.

The closed geodesic of `A = [[2,1],[1,1]]` is the semicircle over `[−1/φ, φ]`, parametrized at unit
speed by `z(t) = ½ + (√5/2)(tanh t + i sech t)`. In real coordinates `gx t + i gy t`:
* `on_circle`: `(gx − ½)² + gy² = 5/4`.
* `norm_identity`: **`|m z(t) + n|² / Im z(t) = (α² eᵗ + α'² e⁻ᵗ)/√5`** with `α = mφ + n`,
  `α' = mφ' + n`. This is the exact algebraic core of Hecke's unfolding
  `∫_0^{4 log φ} E*(z(t), s) dt = Λ_{ℚ(√5)}(s)`. That identity also uses the integral
  `∫(aeᵗ + be⁻ᵗ)^{−s} dt = (ab)^{−s/2}Γ(s/2)²/(2Γ(s))` and the four generators `±φʲ` of each ideal
  modulo `⟨φ²⟩`; neither is formalized here.
* `weyl_reflection`: **`S z(t) = −1/z(t) = z(−t − 2 log φ)`**, so the Weyl element reverses the geodesic.
* `fixed_i`, `fixed_one_add_i`: `z(−log φ) = i` and `z(log φ) = 1 + i`. After `u = t + log φ` these are
  the two fixed points `u = 0` and `u = L/2 = 2 log φ` of the reflection of the Haar circle of length
  `L = 4 log φ`. The quotient is an interval traversed twice by the closed orbit, which doubles the
  heat-trace constant.

The Neumann condition at both endpoints holds for every complex `s`, so it **does not prove RH**. The
orbit measure is unbounded on `L²`: it needs Sobolev order `> 1/2`. **No RH claim.**
-/

namespace GppGoldenGeodesic

open Real

/-- The golden ratio and its conjugate. -/
noncomputable def phi : ℝ := (1 + √5) / 2
noncomputable def phi' : ℝ := (1 - √5) / 2

/-- Real and imaginary parts of the unit-speed golden geodesic. -/
noncomputable def gx (t : ℝ) : ℝ := 1 / 2 + √5 / 2 * (sinh t / cosh t)
noncomputable def gy (t : ℝ) : ℝ := √5 / 2 / cosh t

theorem sqrt5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem phi_pos : 0 < phi := by unfold phi; positivity

theorem phi_inv : phi⁻¹ = phi - 1 := by
  have h : phi * (phi - 1) = 1 := by
    unfold phi
    nlinarith [sqrt5_sq]
  exact inv_eq_of_mul_eq_one_right h

theorem cosh_log_phi : cosh (log phi) = √5 / 2 := by
  rw [cosh_log phi_pos, phi_inv]; unfold phi; ring

theorem sinh_log_phi : sinh (log phi) = 1 / 2 := by
  rw [sinh_log phi_pos, phi_inv]; unfold phi; ring

/-- The parametrization lies on the semicircle of centre `½` and radius `√5/2`. -/
theorem on_circle (t : ℝ) : (gx t - 1 / 2) ^ 2 + gy t ^ 2 = 5 / 4 := by
  have hc : cosh t ≠ 0 := (cosh_pos t).ne'
  unfold gx gy
  field_simp
  have := cosh_sq_sub_sinh_sq t
  nlinarith [sqrt5_sq, this]

/-- **The Hecke norm identity** on the golden geodesic. -/
theorem norm_identity (m n t : ℝ) :
    ((m * gx t + n) ^ 2 + (m * gy t) ^ 2) / gy t
      = ((m * phi + n) ^ 2 * exp t + (m * phi' + n) ^ 2 * exp (-t)) / √5 := by
  have hc : cosh t ≠ 0 := (cosh_pos t).ne'
  have h5 : (√5 : ℝ) ≠ 0 := by positivity
  have he : exp t = cosh t + sinh t := (cosh_add_sinh t).symm
  have he' : exp (-t) = cosh t - sinh t := (cosh_sub_sinh t).symm
  have hcs := cosh_sq_sub_sinh_sq t
  have hs5 := sqrt5_sq
  rw [he, he']
  unfold gx gy phi phi'
  field_simp
  linear_combination (-2 * m ^ 2 * √5 ^ 2) * hcs

theorem cosh_two_log_phi : cosh (2 * log phi) = 3 / 2 := by
  rw [cosh_two_mul, cosh_log_phi, sinh_log_phi]
  nlinarith [sqrt5_sq]

theorem sinh_two_log_phi : sinh (2 * log phi) = √5 / 2 := by
  rw [sinh_two_mul, cosh_log_phi, sinh_log_phi]
  ring

/-- **Weyl reflection**: `S z(t) = −1/z(t) = z(−t − 2 log phi)`, in real coordinates
`−1/z = −z̄/|z|²`. -/
theorem weyl_reflection (t : ℝ) :
    gx (-t - 2 * log phi) = -gx t / (gx t ^ 2 + gy t ^ 2) ∧
      gy (-t - 2 * log phi) = gy t / (gx t ^ 2 + gy t ^ 2) := by
  have hc : cosh t ≠ 0 := (cosh_pos t).ne'
  have hD : cosh (t + 2 * log phi) ≠ 0 := (cosh_pos _).ne'
  have hcs := cosh_sq_sub_sinh_sq t
  have hs5 := sqrt5_sq
  have hneg : -t - 2 * log phi = -(t + 2 * log phi) := by ring
  have hcosh : cosh (t + 2 * log phi) = 3 / 2 * cosh t + √5 / 2 * sinh t := by
    rw [cosh_add, cosh_two_log_phi, sinh_two_log_phi]; ring
  have hsinh : sinh (t + 2 * log phi) = 3 / 2 * sinh t + √5 / 2 * cosh t := by
    rw [sinh_add, cosh_two_log_phi, sinh_two_log_phi]; ring
  have hD' : 3 / 2 * cosh t + √5 / 2 * sinh t ≠ 0 := by rw [← hcosh]; exact hD
  have hN : gx t ^ 2 + gy t ^ 2 = (3 / 2 * cosh t + √5 / 2 * sinh t) / cosh t := by
    unfold gx gy
    field_simp
    linear_combination (-√5 ^ 2) * hcs + cosh t ^ 2 * hs5
  have hD'' : √5 * sinh t + cosh t * 3 ≠ 0 := by
    intro h; apply hD'; linear_combination h / 2
  have h3 : 3 * cosh t + √5 * sinh t ≠ 0 := by
    intro h; apply hD'; linear_combination h / 2
  have h3' : cosh t * 3 + √5 * sinh t ≠ 0 := by
    intro h; apply hD'; linear_combination h / 2
  rw [hN]
  have hgx : gx t = 1 / 2 + √5 / 2 * (sinh t / cosh t) := rfl
  have hgy : gy t = √5 / 2 / cosh t := rfl
  rw [hgx, hgy]
  unfold gx gy
  rw [hneg, cosh_neg, sinh_neg, hcosh, hsinh]
  constructor
  · rw [eq_div_iff (div_ne_zero hD' hc)]
    field_simp [h3, h3']
    linear_combination (-cosh t) * hs5
  · rw [eq_div_iff (div_ne_zero hD' hc)]
    field_simp

/-- `z(−log phi) = i`: the Weyl fixed point. -/
theorem fixed_i : gx (-log phi) = 0 ∧ gy (-log phi) = 1 := by
  unfold gx gy
  rw [cosh_neg, sinh_neg, cosh_log_phi, sinh_log_phi]
  have h5 : (√5 : ℝ) ≠ 0 := by positivity
  constructor <;> (field_simp; try ring)

/-- `z(log phi) = 1 + i`: the second fixed point, at half the Haar period `L/2 = 2 log phi` from `i`. -/
theorem fixed_one_add_i : gx (log phi) = 1 ∧ gy (log phi) = 1 := by
  unfold gx gy
  rw [cosh_log_phi, sinh_log_phi]
  have h5 : (√5 : ℝ) ≠ 0 := by positivity
  constructor <;> (field_simp; try ring)

end GppGoldenGeodesic
