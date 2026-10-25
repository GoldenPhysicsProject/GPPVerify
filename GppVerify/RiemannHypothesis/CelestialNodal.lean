import GppVerify.RiemannHypothesis.CompletedZetaReality
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree

/-!
# Celestial nodal picture: what is exact, and two falsifiers

Source: Codex, GPP-bridge PR #11 comment 6393727134 (Discovery2 PR #24), answering Daniel's
"show zeros are intersecting circles". It builds on `GppConformalShadowPrincipalSeries` (the
shadow/principal-axis dictionary in every `d`) and `GppP1Mirror`. Daniel Toupin / Golden Physics
Project, with AI assistance from Codex (statement) and Claude Code (formalization).

* `dimension_circles_coincide`: with `Δ_d = d s` and `w_d(Δ) = (Δ − d)/Δ`, `w_d(d s) = (s − 1)/s`
  for every `d ≠ 0` and every `s`. So the normalized "dimension circles" for `d = 1, 2, 3, 4, …`
  are one and the same curve. Their geometric intersections cannot pick out discrete zeros.
* `xi_conj`: `ξ(s̄) = conj ξ(s)` for **every** `s`. On `Re s > 0` this comes from
  `GppCompletedZetaReality.completedRiemannZeta_conj`; elsewhere from `ξ(1 − s) = ξ(s)`.
* `G_reflect`: on the celestial sphere `w = (s − 1)/s`, `G(w) = ξ(1/(1 − w))` satisfies
  `G(1/w̄) = conj G(w)` for `w ≠ 0, 1`.
* `G_im_eq_zero_of_norm_one`: hence `Im G = 0` on the equator `|w| = 1`. So equatorial zeros of `G`
  are exactly the crossings of the single nodal curve `{Re G = 0}` with the equator.
* `Ftheta`, `Ftheta_one_sub`, `Ftheta_conj`, `Ftheta_zeros_off_line` (the **adversary**):
  `F_θ(s) = ξ(s − 1/4) ξ(s + 1/4)` has the same two symmetries `s ↦ 1 − s` and `s ↦ s̄`. Yet every
  critical-line zero `ρ` of `ξ` gives zeros of `F_θ` at `ρ ± 1/4`, on `Re s = 1/4` and `3/4`.
  Reflection and reality symmetry alone do not force zeros onto the equator.

**Scope.** Writing zeros as nodal crossings is a coordinate pullback; "all zeros are equatorial
crossings" is RH and is not proved. The orthogonal crossing of simple nodal arcs, the η-phase
picture, the theta-integral form of `ξ(½ + it)` (see `GppThetaSplit`, `GppThetaHalfWave`) and the
numerical latitudes are not formalized here. Existence of critical-line zeros (Hardy) is a
hypothesis in `Ftheta_zeros_off_line`. No claim about RH or BSD.
-/

set_option autoImplicit false

open Complex
open scoped ComplexConjugate

namespace GppCelestialNodal

open GppLogDerivZeroFree

/-- The normalized celestial coordinate `w_d(Δ) = (Δ − d)/Δ`. -/
noncomputable def wd (d : ℝ) (Δ : ℂ) : ℂ := (Δ - d) / Δ

/-- **Dimension circles coincide.** `w_d(d s) = (s − 1)/s` for every `d ≠ 0`. -/
theorem dimension_circles_coincide {d : ℝ} (hd : d ≠ 0) (s : ℂ) :
    wd d (d * s) = (s - 1) / s := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  unfold wd
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · rw [show (d : ℂ) * s - d = d * (s - 1) by ring, mul_div_mul_left _ _ hd']

lemma xi_eq_of_ne {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [xi, completedRiemannZeta_eq]
  field_simp
  ring

lemma xi_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) : xi (conj s) = conj (xi s) := by
  rcases eq_or_ne s 1 with rfl | h1
  · simp [xi, map_ofNat]
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have hc0 : conj s ≠ 0 := by simpa using h0
  have hc1 : conj s ≠ 1 := by
    intro h; apply h1; simpa using congrArg conj h
  rw [xi_eq_of_ne hc0 hc1, xi_eq_of_ne h0 h1,
    GppCompletedZetaReality.completedRiemannZeta_conj hs]
  simp [map_div₀, map_mul, map_sub, map_ofNat]

/-- **Reality of `ξ`.** `ξ(s̄) = conj ξ(s)` for every `s`. -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  rcases lt_or_ge 0 s.re with hs | hs
  · exact xi_conj_of_re_pos hs
  · have hpos : 0 < (1 - s).re := by simp; linarith
    calc xi (conj s) = xi (1 - conj s) := (xi_one_sub _).symm
      _ = xi (conj (1 - s)) := by simp
      _ = conj (xi (1 - s)) := xi_conj_of_re_pos hpos
      _ = conj (xi s) := by rw [xi_one_sub]

/-- The celestial pullback `G(w) = ξ(1/(1 − w))`, i.e. `s = 1/(1 − w)`, `w = (s − 1)/s`. -/
noncomputable def G (w : ℂ) : ℂ := xi (1 / (1 - w))

/-- **Celestial reflection.** `G(1/w̄) = conj G(w)` for `w ≠ 0, 1`. -/
theorem G_reflect {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) : G (1 / conj w) = conj (G w) := by
  have hc0 : conj w ≠ 0 := by simpa using h0
  have hc1 : conj w - 1 ≠ 0 := by
    intro h; apply h1
    have : conj w = 1 := sub_eq_zero.mp h
    simpa using congrArg conj this
  have hw1 : 1 - conj w ≠ 0 := by
    intro h; apply hc1; linear_combination -h
  have key : 1 / (1 - 1 / conj w) = 1 - conj (1 / (1 - w)) := by
    simp only [map_div₀, map_one, map_sub]
    field_simp
    ring
  rw [G, G, key, xi_one_sub, xi_conj]

/-- **The equator is a real locus.** `Im G(w) = 0` whenever `|w| = 1`, `w ≠ 1`. -/
theorem G_im_eq_zero_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) : (G w).im = 0 := by
  have h0 : w ≠ 0 := by rintro rfl; simp at hw
  have hinv : 1 / conj w = w := by
    have hmul : w * conj w = 1 := by
      rw [mul_conj, normSq_eq_norm_sq, hw]; simp
    have hc0 : conj w ≠ 0 := by simpa using h0
    field_simp
    linear_combination -hmul
  have h := G_reflect h0 h1
  rw [hinv] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The adversary `F_θ(s) = ξ(s − 1/4) ξ(s + 1/4)`. -/
noncomputable def Ftheta (s : ℂ) : ℂ := xi (s - 1 / 4) * xi (s + 1 / 4)

theorem Ftheta_one_sub (s : ℂ) : Ftheta (1 - s) = Ftheta s := by
  unfold Ftheta
  rw [show 1 - s - 1 / 4 = 1 - (s + 1 / 4) by ring, show 1 - s + 1 / 4 = 1 - (s - 1 / 4) by ring,
    xi_one_sub, xi_one_sub, mul_comm]

theorem Ftheta_conj (s : ℂ) : Ftheta (conj s) = conj (Ftheta s) := by
  unfold Ftheta
  have h4 : conj ((1 : ℂ) / 4) = 1 / 4 := by simp [map_ofNat]
  rw [map_mul, ← xi_conj, ← xi_conj, map_sub, map_add, h4]

/-- **The adversary has zeros off the line.** Every critical-line zero `ρ` of `ξ` gives zeros
of `F_θ` at `ρ + 1/4` and `ρ − 1/4`, with real parts `3/4` and `1/4`. -/
theorem Ftheta_zeros_off_line {ρ : ℂ} (hρ : xi ρ = 0) (hre : ρ.re = 1 / 2) :
    Ftheta (ρ + 1 / 4) = 0 ∧ Ftheta (ρ - 1 / 4) = 0 ∧
      (ρ + 1 / 4).re = 3 / 4 ∧ (ρ - 1 / 4).re = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Ftheta, hρ]
  · simp [Ftheta, hρ]
  · simp [hre]; norm_num
  · simp [hre]; norm_num

end GppCelestialNodal
