import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The semilocal Weil matrix as a confluent Loewner matrix

Source: Codex, GPPDiscovery2 `research/2026-09-27_semilocal_weil_loewner_normal_form.md`, §§2–4, 6.

Abstract setting: `S(x) = Ψ[sin(xy)]`, `C(x) = Ψ[cos(xy)]`, `D(x) = Ψ[y cos(xy)]` for a linear
functional `Ψ`, support length `L > 0`, lattice `x_n = 2π(n + θ)/L`, and
`b = −(2/L) S`, `f_θ(x) = b(x) + (2/L) sin(Lx − 2πθ) C(x)` (`θ = 0` is the untwisted case).

* `offdiag_loewner`: for `m ≠ n`, `Ψ[q_mn] = (S(x_m) − S(x_n))/(π(n − m))` equals the divided
  difference `(f_θ(x_m) − f_θ(x_n))/(x_m − x_n)`;
* `diag_loewner`: if `S' = D` and `C` is differentiable at `x_n`, then
  `Q_nn = 2C(x_n) − (2/L) D(x_n)` equals `f_θ'(x_n)` — the confluent (derivative) entry;
* `value_on_lattice`: `f_θ(x_n) = b(x_n)`;
* `odd_phase`: if `S` is odd and `C` is even then `f_0` is odd.

## Checks and scope

All claims check. The derivative step `S' = D` (differentiation under the functional `Ψ`) is an
**explicit hypothesis**, not derived: nothing here constructs `Ψ`. **Not formalized:** the completed
Weil distribution `Ψ`, Loewner's theorem and the Pick-class criterion (§5), the screw-function
relation (§6, `Ψ_screw(L) = (L/2) f_L'(0)`, which is stated in the note as an existing relation),
and the proposed attack (§7). Positivity of the matrix is not claimed. No RH claim.
-/

open Real

namespace GppLoewnerNormalForm

/-- Twisted lattice `x_{n,θ} = 2π(n + θ)/L`. -/
noncomputable def node (L θ : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * ((n : ℝ) + θ) / L

/-- The boundary-completed phase `f_θ`. -/
noncomputable def phase (L θ : ℝ) (S C : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(2 / L) * S x + 2 / L * Real.sin (L * x - 2 * Real.pi * θ) * C x

theorem sin_node (L θ : ℝ) (hL : L ≠ 0) (n : ℤ) : Real.sin (L * node L θ n - 2 * Real.pi * θ) = 0 := by
  have : L * node L θ n - 2 * Real.pi * θ = (n : ℝ) * (2 * Real.pi) := by
    unfold node; field_simp; ring
  rw [this]
  have h := Real.sin_int_mul_pi (2 * n)
  rw [show ((2 * n : ℤ) : ℝ) * Real.pi = (n : ℝ) * (2 * Real.pi) by push_cast; ring] at h
  exact h

theorem cos_node (L θ : ℝ) (hL : L ≠ 0) (n : ℤ) : Real.cos (L * node L θ n - 2 * Real.pi * θ) = 1 := by
  have : L * node L θ n - 2 * Real.pi * θ = (n : ℝ) * (2 * Real.pi) := by
    unfold node; field_simp; ring
  rw [this]
  exact Real.cos_int_mul_two_pi n

/-- The phase agrees with `b = −(2/L) S` on the lattice. -/
theorem value_on_lattice (L θ : ℝ) (hL : L ≠ 0) (S C : ℝ → ℝ) (n : ℤ) :
    phase L θ S C (node L θ n) = -(2 / L) * S (node L θ n) := by
  unfold phase
  rw [sin_node L θ hL, mul_zero, zero_mul, add_zero]

/-- **Off-diagonal entries are divided differences of the phase.** -/
theorem offdiag_loewner (L θ : ℝ) (hL : 0 < L) (S C : ℝ → ℝ) (m n : ℤ) (hmn : m ≠ n) :
    (S (node L θ m) - S (node L θ n)) / (Real.pi * ((n : ℝ) - m)) =
      (phase L θ S C (node L θ m) - phase L θ S C (node L θ n)) /
        (node L θ m - node L θ n) := by
  rw [value_on_lattice L θ hL.ne', value_on_lattice L θ hL.ne']
  have hne : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn.symm)
  have hne' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hd : node L θ m - node L θ n = 2 * Real.pi * ((m : ℝ) - n) / L := by
    unfold node; field_simp; ring
  rw [hd]
  have hp := Real.pi_ne_zero
  field_simp
  ring

/-- **The diagonal entry is the derivative of the phase** (confluent Loewner entry). -/
theorem diag_loewner (L θ : ℝ) (hL : 0 < L) (S C : ℝ → ℝ) (D : ℝ → ℝ) (n : ℤ) (c : ℝ)
    (hS : HasDerivAt S (D (node L θ n)) (node L θ n)) (hC : HasDerivAt C c (node L θ n)) :
    HasDerivAt (phase L θ S C) (2 * C (node L θ n) - 2 / L * D (node L θ n)) (node L θ n) := by
  have hs : HasDerivAt (fun x : ℝ => Real.sin (L * x - 2 * Real.pi * θ))
      (Real.cos (L * node L θ n - 2 * Real.pi * θ) * L) (node L θ n) := by
    have h1 : HasDerivAt (fun x : ℝ => L * x - 2 * Real.pi * θ) L (node L θ n) := by
      simpa using ((hasDerivAt_id (node L θ n)).const_mul L).sub_const (2 * Real.pi * θ)
    exact (Real.hasDerivAt_sin _).comp _ h1
  have h := (hS.const_mul (-(2 / L))).add (((hs.const_mul (2 / L))).mul hC)
  refine HasDerivAt.congr_deriv (f := phase L θ S C) h ?_
  rw [sin_node L θ hL.ne', cos_node L θ hL.ne']
  field_simp
  ring

/-- If `S` is odd and `C` is even, the untwisted phase is odd. -/
theorem odd_phase (L : ℝ) (S C : ℝ → ℝ) (hS : ∀ x, S (-x) = -S x) (hC : ∀ x, C (-x) = C x) (x : ℝ) :
    phase L 0 S C (-x) = -phase L 0 S C x := by
  unfold phase
  rw [hS, hC]
  simp only [mul_zero, sub_zero, mul_neg, Real.sin_neg]
  ring

end GppLoewnerNormalForm
