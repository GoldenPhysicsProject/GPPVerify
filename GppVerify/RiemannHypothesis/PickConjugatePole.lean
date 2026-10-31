import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Pick matrix of a conjugate pole pair: pointwise positivity without joint positivity

Source: Astra, `work/2026-10-10_astra_pick_continuation.md` §2 ("Exact adversarial control").
Daniel Toupin / Golden Physics Project, with AI assistance from Astra (statement) and Claude Code
(formalization).

For the Herglotz-type function `m(k) = 1/(γ + ia − k) + 1/(γ − ia − k)` (a conjugate pair of poles at
`γ ± ia`, `a > 0`) and nodes `k_j = γ + i y_j` with `y_j > a`:

* `im_pos`-style fact: `m(γ + iy) = 2iy/(y² − a²)`, so `Im m > 0` at every node (`pickM_eq`).
* `pickEntry`: the Pick kernel `(m(k_i) − conj m(k_j))/(k_i − conj k_j)` equals the real number
  `2(u_i + u_j)/(y_i + y_j)` with `u = y/(y² − a²)` (`pick_kernel_eq`).
* `pick_det`: `det Pick(k₁,k₂) = −4a²(y₁−y₂)² / ((y₁²−a²)²(y₂²−a²)²)`.
* `pick_det_neg`: this is `< 0` for `y₁ ≠ y₂`, both diagonal entries being positive
  (`pick_diag_pos`).

So pointwise correct sign of `Im m` in a region does not imply a jointly positive (Pick) extension.

**Scope.** The finite exact computation only. The note's criterion (RH ⇔ all real-node Pick matrices
are positive semidefinite) rests on Nevanlinna–Pick interpolation and analytic continuation and is
not formalized; neither are the polynomial `G(k) = ((k−14)²+a²)((k+14)²+a²)` control values or the
binary64 arithmetic diagnostics in the note. No claim about RH.
-/

set_option autoImplicit false

namespace GppPickConjugatePole

/-- `m(k) = 1/(γ + ia − k) + 1/(γ − ia − k)`. -/
noncomputable def pickM (γ a : ℝ) (k : ℂ) : ℂ :=
  1 / ((γ : ℂ) + Complex.I * a - k) + 1 / ((γ : ℂ) - Complex.I * a - k)

/-- The real Pick entry `2(u_i + u_j)/(y_i + y_j)`, `u = y/(y² − a²)`. -/
noncomputable def pickEntry (a y₁ y₂ : ℝ) : ℝ :=
  2 * (y₁ / (y₁ ^ 2 - a ^ 2) + y₂ / (y₂ ^ 2 - a ^ 2)) / (y₁ + y₂)

/-- `m(γ + iy) = 2iy/(y² − a²)`. -/
theorem pickM_eq (γ a y : ℝ) (hy : a < y) (ha : 0 < a) :
    pickM γ a ((γ : ℂ) + Complex.I * y) = Complex.I * ((2 * y / (y ^ 2 - a ^ 2) : ℝ) : ℂ) := by
  have h1 : (y : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have : y ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have h2 : (a : ℂ) - y ≠ 0 := by
    have : a - y ≠ 0 := by linarith
    exact_mod_cast this
  have h3 : (a : ℂ) + y ≠ 0 := by
    have : a + y ≠ 0 := by linarith
    exact_mod_cast this
  unfold pickM
  have e1 : (γ : ℂ) + Complex.I * a - ((γ : ℂ) + Complex.I * y) = Complex.I * ((a : ℂ) - y) := by ring
  have e2 : (γ : ℂ) - Complex.I * a - ((γ : ℂ) + Complex.I * y) = -(Complex.I * ((a : ℂ) + y)) := by ring
  rw [e1, e2]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- Every node has `Im m > 0`: the pointwise sign is correct. -/
theorem pickM_im_pos (γ a y : ℝ) (hy : a < y) (ha : 0 < a) :
    0 < (pickM γ a ((γ : ℂ) + Complex.I * y)).im := by
  rw [pickM_eq γ a y hy ha, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  have : 0 < 2 * y / (y ^ 2 - a ^ 2) := by
    apply div_pos (by linarith)
    nlinarith
  simpa using this

/-- The Pick kernel at two nodes `γ + i y_j` is the real number `pickEntry a y₁ y₂`. -/
theorem pick_kernel_eq (γ a y₁ y₂ : ℝ) (ha : 0 < a) (h1 : a < y₁) (h2 : a < y₂) :
    (pickM γ a ((γ : ℂ) + Complex.I * y₁) - (starRingEnd ℂ) (pickM γ a ((γ : ℂ) + Complex.I * y₂))) /
        (((γ : ℂ) + Complex.I * y₁) - (starRingEnd ℂ) ((γ : ℂ) + Complex.I * y₂)) =
      ((pickEntry a y₁ y₂ : ℝ) : ℂ) := by
  rw [pickM_eq γ a y₁ h1 ha, pickM_eq γ a y₂ h2 ha]
  have hs : (y₁ : ℂ) + y₂ ≠ 0 := by
    have : y₁ + y₂ ≠ 0 := by linarith
    exact_mod_cast this
  have hd1 : (y₁ : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have : y₁ ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hd2 : (y₂ : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
    have : y₂ ^ 2 - a ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have e : ((γ : ℂ) + Complex.I * y₁) - (starRingEnd ℂ) ((γ : ℂ) + Complex.I * y₂) =
      Complex.I * ((y₁ : ℂ) + y₂) := by
    simp [map_add, map_mul, Complex.conj_ofReal]; ring
  rw [e]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  unfold pickEntry
  push_cast
  field_simp
  ring_nf

/-- Diagonal entries are positive: `pickEntry a y y = 2/(y² − a²)`. -/
theorem pick_diag_pos (a y : ℝ) (ha : 0 < a) (hy : a < y) : 0 < pickEntry a y y := by
  have hy0 : 0 < y := by linarith
  have hd : 0 < y ^ 2 - a ^ 2 := by nlinarith
  unfold pickEntry
  have : 0 < y / (y ^ 2 - a ^ 2) + y / (y ^ 2 - a ^ 2) := by positivity
  positivity

/-- **Exact two-node Pick determinant of a conjugate pole pair.** -/
theorem pick_det (a y₁ y₂ : ℝ) (ha : 0 < a) (h1 : a < y₁) (h2 : a < y₂) :
    pickEntry a y₁ y₁ * pickEntry a y₂ y₂ - pickEntry a y₁ y₂ ^ 2 =
      -4 * a ^ 2 * (y₁ - y₂) ^ 2 / ((y₁ ^ 2 - a ^ 2) ^ 2 * (y₂ ^ 2 - a ^ 2) ^ 2) := by
  have hy1 : 0 < y₁ := by linarith
  have hy2 : 0 < y₂ := by linarith
  have hd1 : y₁ ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  have hd2 : y₂ ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  have hs : y₁ + y₂ ≠ 0 := by linarith
  unfold pickEntry
  field_simp
  ring

/-- Pointwise `Im m > 0` at both nodes and positive diagonal, yet `det < 0` for `y₁ ≠ y₂`. -/
theorem pick_det_neg (a y₁ y₂ : ℝ) (ha : 0 < a) (h1 : a < y₁) (h2 : a < y₂) (hne : y₁ ≠ y₂) :
    pickEntry a y₁ y₁ * pickEntry a y₂ y₂ - pickEntry a y₁ y₂ ^ 2 < 0 := by
  rw [pick_det a y₁ y₂ ha h1 h2]
  have hd1 : 0 < y₁ ^ 2 - a ^ 2 := by nlinarith
  have hd2 : 0 < y₂ ^ 2 - a ^ 2 := by nlinarith
  have hsq : 0 < (y₁ - y₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  apply div_neg_of_neg_of_pos
  · nlinarith [mul_pos (pow_pos ha 2) hsq]
  · positivity

end GppPickConjugatePole
