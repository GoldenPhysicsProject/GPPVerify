import GppVerify.CelestialHolography.ConformalShadowPrincipalSeries
import Mathlib.Tactic

/-!
# The u-twisted bridge between the two Riemann spheres

The symmetric bridge `Δ ↦ 2 - Δ̄` is the `d = 2` anti-linear shadow
(`GppConformalShadowPrincipalSeries.antiLinearShadow`), whose pointwise fixed
locus is the principal-series axis `Re Δ = 1`.  Here we deform it by a relative
twist parameter `u : ℂ` between the two spheres:

  B_u(Δ) = 2 - u * Δ̄.

In the number-Higgs reading, `u` is the inter-sphere phase (the VEV living on the
bridge); `u = 1` is the symmetric/unbroken bridge.  Main results, all elementary:

* `twistedBridge_involutive_iff`: `B_u` is an involution iff `u = 1`.
* `twistedBridge_fixed_u_one`: at `u = 1` the fixed locus is `Re Δ = 1`
  (cites `celestial_antiLinearShadow_fixed_iff`, not duplicated).
* `twistedBridge_fixed_iff_abs_ne_one`: for `‖u‖ ≠ 1` there is exactly one fixed
  point, `Δ⋆ = 2(1-u)/(1-‖u‖²)`.
* `twistedBridge_no_fixed_of_unit_ne_one`: for `‖u‖ = 1`, `u ≠ 1`, no fixed points.
* `twistedBridge_principal_locus_iff`: the fixed locus is the principal line
  `Re Δ = 1` iff `u = 1` — rigidity of the unitary interface.
* `twistedBridge_intertwines`: the scale dictionary `Δ = 2s` intertwines the
  twisted arithmetic and celestial bridges.

No zeta-zero statement is used; this is the representation-theoretic skeleton on
which the number-Higgs bridge deformation is formulated.
-/

namespace GppTwistedBridge

open Complex
open GppConformalShadowPrincipalSeries
open GppScaleShadow

/-- The u-twisted anti-linear bridge between the two spheres. -/
noncomputable def twistedBridge (u Δ : ℂ) : ℂ := 2 - u * (starRingEnd ℂ) Δ

/-- At `u = 1` we recover the symmetric anti-linear shadow. -/
theorem twistedBridge_one (Δ : ℂ) :
    twistedBridge 1 Δ = antiLinearShadow 2 Δ := by
  simp [twistedBridge, antiLinearShadow]

/-- Conjugation passes through the twisted bridge. -/
theorem conj_twistedBridge (u Δ : ℂ) :
    (starRingEnd ℂ) (twistedBridge u Δ) = 2 - (starRingEnd ℂ) u * Δ := by
  apply Complex.ext <;> simp [twistedBridge, Complex.mul_re, Complex.mul_im]

/-- Conjugation fixes the literals `1` and `2`. -/
theorem conj_one_two :
    (starRingEnd ℂ) (1 : ℂ) = 1 ∧ (starRingEnd ℂ) (2 : ℂ) = 2 := by
  constructor <;> (apply Complex.ext <;> simp)

/-- `Δ̄ * Δ = ‖Δ‖²` as a complex number. -/
theorem conj_mul_self (u : ℂ) :
    (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ) u * u = (Complex.normSq u : ℂ) := by
    have hre : ((starRingEnd ℂ) u * u).re = (Complex.normSq u : ℂ).re := by
      simp [Complex.mul_re, Complex.normSq_apply]
    have him : ((starRingEnd ℂ) u * u).im = (Complex.normSq u : ℂ).im := by
      simp [Complex.mul_im, Complex.normSq_apply]
      ring
    exact Complex.ext hre him
  rw [h1]
  have h2 : Complex.normSq u = ‖u‖ ^ 2 := RCLike.normSq_eq_def' u
  rw [h2]

/-- Conjugation fixes real casts. -/
theorem conj_real_cast (r : ℝ) :
    (starRingEnd ℂ) ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

/-- A fixed point satisfies the complex-linear equation `Δ(1 - ūu) = 2(1-u)`. -/
theorem twistedBridge_fixed_implies (u Δ : ℂ)
    (h : twistedBridge u Δ = Δ) :
    Δ * (1 - (starRingEnd ℂ) u * u) = 2 * (1 - u) := by
  have h2 : (starRingEnd ℂ) Δ = 2 - (starRingEnd ℂ) u * Δ := by
    have hc := congrArg (starRingEnd ℂ) h
    rw [conj_twistedBridge] at hc
    exact hc.symm
  have h1 : Δ = 2 - u * (starRingEnd ℂ) Δ := h.symm
  rw [h2] at h1
  linear_combination h1

/-- The twisted bridge is an involution iff the twist is trivial. -/
theorem twistedBridge_involutive_iff (u : ℂ) :
    (∀ Δ, twistedBridge u (twistedBridge u Δ) = Δ) ↔ u = 1 := by
  constructor
  · intro h
    have h0 := h 0
    have e1 : twistedBridge u 0 = 2 := by simp [twistedBridge]
    rw [e1] at h0
    simp only [twistedBridge, conj_one_two.2] at h0
    linear_combination (-1 / 2) * h0
  · intro h Δ
    subst h
    rw [twistedBridge_one, twistedBridge_one]
    exact antiLinearShadow_involutive 2 Δ

/-- At `u = 1` the fixed locus is exactly the principal-series axis. -/
theorem twistedBridge_fixed_u_one (Δ : ℂ) :
    twistedBridge 1 Δ = Δ ↔ Δ.re = 1 := by
  rw [twistedBridge_one]
  exact celestial_antiLinearShadow_fixed_iff Δ

/-- Away from the unit circle the fixed-point equation in closed form. -/
theorem twistedBridge_fixed_iff_abs_ne_one (u Δ : ℂ) (h : ‖u‖ ≠ 1) :
    twistedBridge u Δ = Δ ↔
      Δ * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) = 2 * (1 - u) := by
  have hc : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hr : (1 - ‖u‖ ^ 2 : ℝ) ≠ 0 := by
      intro hz
      apply h
      have hsq : ‖u‖ ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp hsq with h1 | h1
      · exact h1
      · have hnn := norm_nonneg u
        linarith
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact hr
  have huu : (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := conj_mul_self u
  constructor
  · intro hΔ
    have hfi := twistedBridge_fixed_implies u Δ hΔ
    rw [huu] at hfi
    have hcast : (1 - ((‖u‖ ^ 2 : ℝ) : ℂ)) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at hfi
    exact hfi
  · intro hΔ
    have hΔc : (starRingEnd ℂ) Δ * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ)
        = 2 * (1 - (starRingEnd ℂ) u) := by
      have hcc := congrArg (starRingEnd ℂ) hΔ
      rw [map_mul, conj_real_cast, map_mul, map_sub, map_one,
        conj_one_two.2] at hcc
      exact hcc
    have key : (2 - u * (starRingEnd ℂ) Δ) * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ)
        = Δ * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast at hΔ hΔc huu ⊢
      linear_combination -u * hΔc - hΔ + 2 * huu
    have hcancel := mul_right_cancel₀ hc key
    show 2 - u * (starRingEnd ℂ) Δ = Δ
    exact hcancel

/-- On the unit circle with nontrivial twist there are no fixed points at all. -/
theorem twistedBridge_no_fixed_of_unit_ne_one (u : ℂ)
    (h1 : ‖u‖ = 1) (h2 : u ≠ 1) :
    ¬ ∃ Δ, twistedBridge u Δ = Δ := by
  rintro ⟨Δ, hΔ⟩
  have hfi := twistedBridge_fixed_implies u Δ hΔ
  have huu : (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := conj_mul_self u
  rw [h1] at huu
  simp only [one_pow, Complex.ofReal_one] at huu
  rw [huu] at hfi
  simp only [sub_self, mul_zero] at hfi
  -- hfi : 0 = 2 * (1 - u)
  have h3 : (1 : ℂ) - u = 0 := by
    have h4 : (2 : ℂ) * (1 - u) = 0 := hfi.symm
    rcases mul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  have hu : u = 1 := by linear_combination -h3
  exact h2 hu

/-- Rigidity: the fixed locus is the principal line `Re Δ = 1` iff untwisted. -/
theorem twistedBridge_principal_locus_iff (u : ℂ) :
    (∀ Δ, twistedBridge u Δ = Δ ↔ Δ.re = 1) ↔ u = 1 := by
  constructor
  · intro h
    have h1 := (h 1).mpr (by norm_num)
    simp only [twistedBridge, conj_one_two.1, mul_one] at h1
    linear_combination -h1
  · intro h Δ
    subst h
    exact twistedBridge_fixed_u_one Δ

/-- The scale dictionary intertwines the twisted bridges on both sides. -/
theorem twistedBridge_intertwines (u s : ℂ) :
    celestialDelta (1 - u * (starRingEnd ℂ) s)
      = twistedBridge u (celestialDelta s) := by
  apply Complex.ext <;>
    simp [twistedBridge, celestialDelta, Complex.mul_re, Complex.mul_im] <;> ring

end GppTwistedBridge

#print axioms GppTwistedBridge.twistedBridge_one
#print axioms GppTwistedBridge.conj_twistedBridge
#print axioms GppTwistedBridge.conj_one_two
#print axioms GppTwistedBridge.conj_mul_self
#print axioms GppTwistedBridge.conj_real_cast
#print axioms GppTwistedBridge.twistedBridge_fixed_implies
#print axioms GppTwistedBridge.twistedBridge_involutive_iff
#print axioms GppTwistedBridge.twistedBridge_fixed_u_one
#print axioms GppTwistedBridge.twistedBridge_fixed_iff_abs_ne_one
#print axioms GppTwistedBridge.twistedBridge_no_fixed_of_unit_ne_one
#print axioms GppTwistedBridge.twistedBridge_principal_locus_iff
#print axioms GppTwistedBridge.twistedBridge_intertwines
