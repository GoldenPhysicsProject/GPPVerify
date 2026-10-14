import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The ζ pole pair `{0, 1}` has exact signature `(1+, 1−)` on Mellin windows

Source: Codex, GPP-bridge `work/codex/2026-10-14_two_face_pole_negative_index_multiscale.md`
(commit 54d66560; PR #11 comment 6163656664); diagnostic in GPPDiscovery2
`research/codex/compact_sewing_20261014/two_face_pole_signature.py`.

For a window `g ∈ L²[−h, h]` with `M_g(z) = ∫ g(t) e^{zt} dt`, the pole term is
`P_r(g) = 2 Re[M_g(r) conj M_g(−r)]`, with `M_g(±r) = C ± S`, `C = ⟨g, cosh(rt)⟩` (even part) and
`S = ⟨g, sinh(rt)⟩` (odd part). This file proves:
* `pole_parity`: `2 Re[(C + S) conj(C − S)] = 2|C|² − 2|S|²` (exact parity factorization).
* `signature_pos`/`signature_neg`/`nonpos_on_perp`/`nonneg_on_perp`: on any real inner product
  space, for orthogonal nonzero `u, v` the form `Q(g) = 2⟨g,u⟩² − 2⟨g,v⟩²` is positive at `u`,
  negative at `v`, `≤ 0` on `u^⊥` and `≥ 0` on `v^⊥`. So it has exactly one positive and one negative
  direction. In `L²[−h,h]` the even `cosh(t/2)` and odd `sinh(t/2)` are orthogonal (`cosh_sinh_orth`).
* `norm_cosh_half`, `norm_sinh_half`: `∫_{−h}^{h} cosh²(t/2) = sinh h + h` and
  `∫_{−h}^{h} sinh²(t/2) = sinh h − h`. So the eigenvalues are `+2(sinh h + h)` and `−2(sinh h − h)`.

Pole term only, not the full Weil form. The `F_θ` two-negative-direction asymptotics are checked
numerically in the bridge, not here. **No RH claim.**
-/

namespace GppTwoFacePoleSignature

open Real

/-- **Parity factorization** of the pole cross-term. -/
theorem pole_parity (C S : ℂ) :
    2 * ((C + S) * (starRingEnd ℂ) (C - S)).re = 2 * Complex.normSq C - 2 * Complex.normSq S := by
  simp only [map_sub, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two-face pole form `Q(g) = 2⟨g,u⟩² − 2⟨g,v⟩²`. -/
def Q (u v g : E) : ℝ := 2 * (inner ℝ g u) ^ 2 - 2 * (inner ℝ g v) ^ 2

theorem signature_pos {u v : E} (huv : inner ℝ u v = 0) (hu : u ≠ 0) : 0 < Q u v u := by
  unfold Q
  rw [huv, real_inner_self_eq_norm_sq]
  have : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have : 0 < (‖u‖ ^ 2) ^ 2 := by positivity
  linarith

theorem signature_neg {u v : E} (huv : inner ℝ u v = 0) (hv : v ≠ 0) : Q u v v < 0 := by
  unfold Q
  rw [real_inner_comm, huv, real_inner_self_eq_norm_sq]
  have : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have : 0 < (‖v‖ ^ 2) ^ 2 := by positivity
  linarith

theorem nonpos_on_perp (u v : E) {g : E} (hg : inner ℝ g u = 0) : Q u v g ≤ 0 := by
  unfold Q; rw [hg]; nlinarith [sq_nonneg (inner ℝ g v)]

theorem nonneg_on_perp (u v : E) {g : E} (hg : inner ℝ g v = 0) : 0 ≤ Q u v g := by
  unfold Q; rw [hg]; nlinarith [sq_nonneg (inner ℝ g u)]

end Abstract

theorem cosh_half_sq (t : ℝ) : cosh (t / 2) ^ 2 = (1 + cosh t) / 2 := by
  have h := cosh_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring, sinh_sq] at h
  linarith

theorem sinh_half_sq (t : ℝ) : sinh (t / 2) ^ 2 = (cosh t - 1) / 2 := by
  rw [sinh_sq, cosh_half_sq]; ring

/-- **Even eigenvalue**: `∫_{−h}^{h} cosh²(t/2) dt = sinh h + h`. -/
theorem norm_cosh_half (h : ℝ) : ∫ t in (-h)..h, cosh (t / 2) ^ 2 = sinh h + h := by
  simp_rw [cosh_half_sq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (t + sinh t) / 2)
    (fun x _ => by simpa using ((hasDerivAt_id x).add (hasDerivAt_sinh x)).div_const 2)
    ((by fun_prop : Continuous fun t : ℝ => (1 + cosh t) / 2).intervalIntegrable (-h) h)]
  simp [sinh_neg]; ring

/-- **Odd eigenvalue**: `∫_{−h}^{h} sinh²(t/2) dt = sinh h − h`. -/
theorem norm_sinh_half (h : ℝ) : ∫ t in (-h)..h, sinh (t / 2) ^ 2 = sinh h - h := by
  simp_rw [sinh_half_sq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (sinh t - t) / 2)
    (fun x _ => by simpa using ((hasDerivAt_sinh x).sub (hasDerivAt_id x)).div_const 2)
    ((by fun_prop : Continuous fun t : ℝ => (cosh t - 1) / 2).intervalIntegrable (-h) h)]
  simp [sinh_neg]; ring

/-- **Orthogonality** of the even and odd pole channels: `∫_{−h}^{h} cosh(t/2) sinh(t/2) dt = 0`. -/
theorem cosh_sinh_orth (h : ℝ) : ∫ t in (-h)..h, cosh (t / 2) * sinh (t / 2) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => sinh (t / 2) * sinh (t / 2))
    (fun x _ => by
      have h1 : HasDerivAt (fun t : ℝ => sinh (t / 2)) (cosh (x / 2) * (1 / 2)) x := by
        have := (Real.hasDerivAt_sinh (x / 2)).comp x ((hasDerivAt_id' x).div_const 2)
        simpa [Function.comp_def] using this
      refine (h1.mul h1).congr_deriv ?_
      ring)
    ((by fun_prop : Continuous fun t : ℝ => cosh (t / 2) * sinh (t / 2)).intervalIntegrable (-h) h)]
  simp [neg_div, sinh_neg]

end GppTwoFacePoleSignature
