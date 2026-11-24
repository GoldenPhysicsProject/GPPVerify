import GppVerify.CelestialHolography.PSSNormalizability
import GppVerify.CelestialHolography.PSSShadowTransform
import GppVerify.CelestialHolography.ConformalShadowPrincipalSeries
import GppVerify.RiemannHypothesis.PasterskiShaoNormalizability

/-!
# PSS File 7: the dictionary between the physics package and the `d = 1` arithmetic side

This is the only file of the Pasterski–Shao(–Strominger) package that imports both trees. The
physics files (`CelestialHolography/ConformalPrimaryWavefunction`, `KleinGordonPairing`,
`PSSRadialPairing`, `PSSNormalizability`, `PSSShadowTransform`, `Analysis/MellinPlancherel*`)
never reach `GppVerify/RiemannHypothesis/` (checked transitively by `scripts/check_pss_wall.py`).
Spec: GPP-bridge `MuseResearch/turbo-pss-inventory-spec-2026-11-13.md`, File 7.

Every statement here is in one of two categories, and there is no third:

* **a specialisation of a physics-file theorem**, stated next to the existing radial results.
  * `radialDeltaNormalisable_one_iff_kg_radial`: at `d = 1`, File 4's delta-normalisability is
    exactly the in-tree radial scale invariance `masslessKgLogRadialWeight 1 (Re Δ) u = 1`
    (`massless_kg_radial_scale_invariant_iff_principal`).
  * `radialDeltaNormalisable_one_iff_eq_conjShadow`: and exactly self-conjugacy under the shadow.
  * `shadowDim_eq_conformalShadow` and `shadowDim_eq_shadow`: the label action of File 6's
    operator is the in-tree label map `Δ ↦ d − Δ`. This is the label-consistency corollary that
    the import wall kept out of File 6.
  * `s_eq_delta_label`: the character identity `s = Δ₁`, restated. It is an equality of
    dilation characters, **not** an identification of `ξ` with a celestial two-point function,
    a Plancherel density, or a conformal primary wavefunction.
* **the named OPEN premise, unchanged**: `XiZeroIsNormalizable1dState`
  (`= AllXiZerosKGNormalized`), with `rh_of_xi_zero_is_normalizable_1d_state` re-exported as a
  conditional.

The regression control is carried by reference: `ftheta_off_axis_zero_fails_1d_normalizability`
and `ftheta_has_shadow_but_zeros_not_all_principal` show that shadow symmetry plus this
normalisability criterion do not force zeros onto the line for a shadow-symmetric adversary. The
package therefore does not, and cannot, discharge the premise. PSS prove "normalisable ⇒
principal"; the premise is the converse, applied to `ξ`.
-/

namespace GppPasterskiShaoDictionary

open Complex
open scoped ComplexConjugate

/-- **(a) File 4 at `d = 1` is the in-tree radial criterion.** For any nontrivial log-rescaling
`u`, delta-normalisability in File 4's radial sense is equivalent to scale invariance of the
in-tree massless KG radial weight. -/
theorem radialDeltaNormalisable_one_iff_kg_radial (Δ : ℂ) {u : ℝ} (hu : u ≠ 0) :
    GppPSSNormalizability.RadialDeltaNormalisable 1 Δ ↔
      GppOneDimensionalMellinWeight.masslessKgLogRadialWeight 1 Δ.re u = 1 := by
  rw [GppPSSNormalizability.radialDeltaNormalisable_iff,
    GppOneDimensionalMellinWeight.massless_kg_radial_scale_invariant_iff_principal 1 Δ.re hu]
  norm_num

/-- **(a′)** The same criterion, in conjugate-shadow form: `Δ = 1 − conj Δ`. -/
theorem radialDeltaNormalisable_one_iff_eq_conjShadow (Δ : ℂ) :
    GppPSSNormalizability.RadialDeltaNormalisable 1 Δ ↔ Δ = (1 : ℂ) - conj Δ := by
  rw [GppPSSNormalizability.radialDeltaNormalisable_iff]
  have h := (GppPasterskiShao.eq_conjShadow_iff_principal 1 Δ)
  unfold GppPasterskiShao.conjShadow at h
  push_cast at h ⊢
  constructor
  · intro hre; exact h.mpr (by simpa using hre)
  · intro heq; have := h.mp heq; simpa using this

/-- **(b) Label consistency.** The weight action of File 6's shadow operator is the in-tree
`conformalShadow` map. -/
theorem shadowDim_eq_conformalShadow (d : ℕ) (Δ : ℂ) :
    GppPSSShadowTransform.shadowDim d Δ =
      GppConformalShadowPrincipalSeries.conformalShadow d Δ := by
  unfold GppPSSShadowTransform.shadowDim GppConformalShadowPrincipalSeries.conformalShadow
  push_cast; rfl

/-- **(b′)** and the `GppPasterskiShao.shadow` label map. -/
theorem shadowDim_eq_shadow (d : ℕ) (Δ : ℂ) :
    GppPSSShadowTransform.shadowDim d Δ = GppPasterskiShao.shadow d Δ := by
  unfold GppPSSShadowTransform.shadowDim GppPasterskiShao.shadow
  push_cast; rfl

/-- **(c) The character identity `s = Δ₁`, restated.** An equality of dilation characters at
every complex label, including off-axis ones. Not an identification of `ξ` with any physical
object. -/
theorem s_eq_delta_label (s : ℂ) (x : ℝ) :
    GppArithmeticConformalKinematics.logScaleCharacter s x * Complex.exp ((x : ℂ) / 2) =
      GppOneDimensionalMellinWeight.conformalDilation s x :=
  GppPasterskiShao.s_eq_delta_1d_holds_for_every_label s x

/-- **(d) The premise, unchanged and OPEN.** Re-exported by name. Nothing in the PSS package
proves it. -/
abbrev XiZeroIsNormalizable1dState : Prop := GppPasterskiShao.XiZeroIsNormalizable1dState

/-- **(d′)** The conditional, re-exported: it does not assert its hypothesis. -/
theorem rh_of_xi_zero_is_normalizable_1d_state (h : XiZeroIsNormalizable1dState) :
    RiemannHypothesis :=
  GppPasterskiShao.rh_of_xi_zero_is_normalizable_1d_state h

end GppPasterskiShaoDictionary

#print axioms GppPasterskiShaoDictionary.radialDeltaNormalisable_one_iff_kg_radial
#print axioms GppPasterskiShaoDictionary.radialDeltaNormalisable_one_iff_eq_conjShadow
#print axioms GppPasterskiShaoDictionary.shadowDim_eq_conformalShadow
#print axioms GppPasterskiShaoDictionary.shadowDim_eq_shadow
#print axioms GppPasterskiShaoDictionary.s_eq_delta_label
#print axioms GppPasterskiShaoDictionary.rh_of_xi_zero_is_normalizable_1d_state
