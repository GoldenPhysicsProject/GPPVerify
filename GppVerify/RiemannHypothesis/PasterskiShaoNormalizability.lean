/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.OneDimensionalMellinWeight
import GppVerify.RiemannHypothesis.CelestialNodal

/-!
# Pasterski–Shao normalizability in one boundary dimension

Sources: Pasterski–Shao, "A Conformal Basis for Flat Space Amplitudes",
arXiv:1705.01027, especially §§3–4 and §6; Pasterski–Shao–Strominger,
arXiv:1701.00049 (massive scalars, Klein–Gordon pairing) and
arXiv:1706.03917 (gluon Mellin amplitudes). In-tree companions:
`GppOneDimensionalMellinWeight` (the `s = Δ₁` character identity and the
massless Klein–Gordon radial weight) and `GppCelestialNodal` (the `F_θ`
adversary).

Daniel's 2026-11-10 dictionary, used here without the two-dimensional
halving `Δ₂ ↦ Δ₂/2`: work in one fewer celestial dimension, so the
boundary is `d = 1`, the shadow is `Δ ↦ 1 − Δ`, and the fixed line
`Re Δ = 1/2` is literally the critical line. The graviton reading is
the dimensionally reduced celestial theory, not a claim that
Pasterski–Shao constructed propagating gravitons in `R^{1,2}` (they
explicitly assume `d ≥ 2` for spin two; 1705.01027, §6). The radial
Klein–Gordon calculation they give for massless fields ((4.7)–(4.9),
and "the same argument" in §§5.3 and 6.3) specialises algebraically
to `d = 1`.

## What Pasterski–Shao prove (CHECKED against the papers)

* Massless conformal primary wavefunctions
  `φ_Δ^±(X; w) = ∫_0^∞ ω^{Δ−1} exp(± i ω q(w)·X) dω` are
  delta-function-normalizable in the Klein–Gordon pairing if and only
  if `Δ` lies on the principal continuous series `Δ ∈ d/2 + i ℝ`.
  For any other real part `c ≠ d/2` the radial integral
  `∫_0^∞ ω^{2c−d+i(ν₁−ν₂)−1} dω` diverges (1705.01027, (4.7)–(4.9)).
* Those principal-series wavefunctions span the non-zero-energy plane
  waves (inverse Mellin transform). Completeness therefore says: the
  principal series *spans* the delta-normalizable solutions.
* The discrete series `Δ = d/2 + ℤ₊` is not Klein–Gordon normalizable
  ((3.12) and the paragraph after (3.11)).
* For gravitons in `R^{1,d+1}` with `d ≥ 2`, the same principal-series
  range is normalizable and complete for the linearized Einstein
  solutions modulo residual diffeomorphisms (§6.3). Special integer
  values `Δ = 0, 1` (and, when `d = 2`, also `Δ = 2`) are pure
  diffeomorphisms, not propagating modes.
* The shadow transform sends `Δ` to `d − Δ`. On the principal series
  this is complex conjugation: `d − Δ = conj Δ` if and only if
  `Re Δ = d/2`.

They do not mention `ξ`, `ζ`, or any `L`-function. They do not produce
a celestial amplitude, two-point function, conformal primary, Mellin
kernel, or Plancherel density that equals `ξ(s)`, and they do not place
the zeros of `ξ` into the Hilbert space of normalizable wavefunctions.

## What this file proves

1. **PROVED.** `Δ = d − conj(Δ)` if and only if `Re Δ = d/2`. In
   `d = 1` this is `Δ = 1 − conj(Δ)` iff `Re Δ = 1/2`. This is the
   algebraic content of "normalizability forces a weight to equal its
   conjugate shadow".
2. **PROVED.** The existing massless Klein–Gordon radial weight in
   `d = 1` is scale-invariant if and only if that conjugate-shadow
   identity holds. Combined with the in-tree character identity
   `s = Δ₁`, this is Pasterski–Shao's radial criterion on the
   arithmetic line, with no halving.
3. **PROVED (F_θ test).** `F_θ(s) = ξ(s−1/4) ξ(s+1/4)` obeys the same
   shadow / functional equation `F_θ(1−s) = F_θ(s)`. Every critical-line
   zero `ρ` of `ξ` produces zeros of `F_θ` at `ρ ± 1/4` which fail both
   the principal-series test and the `d = 1` Klein–Gordon
   normalizability test. Shadow symmetry alone therefore only pairs
   zeros (`σ ↔ 1−σ`); it does not force them onto `Re = 1/2`.
4. **OPEN.** `XiZeroIsNormalizable1dState`: every zero of the entire
   completion `ξ` is a delta-normalizable weight of the `d = 1`
   theory. Definitionally `AllXiZerosKGNormalized`. Pasterski–Shao
   completeness runs in the other direction (normalizable ⇒ principal)
   and does not discharge this. The implication to `RiemannHypothesis`
   is already in tree and is re-exported. RH and ARP remain OPEN.

Reading the character identity `s = Δ₁` as an identification of
*objects* (`ξ` equals a celestial two-point function, Plancherel
density, or conformal primary wavefunction) is not a theorem of
Pasterski–Shao and is not asserted here. That identity holds for every
complex `s`, including the off-axis points of `F_θ` shape, so it cannot
by itself make the zeros physical.

No `sorry`, no `admit`, no custom axiom. Finite, algebraic, and
already-banked analytic facts only.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of
the Cosmos / Grok: Pasterski–Shao reading, conjugate-shadow lemmas,
and the concrete `F_θ` normalizability test).
-/

set_option autoImplicit false

open Complex
open scoped ComplexConjugate

namespace GppPasterskiShao

open GppOneDimensionalMellinWeight
open GppCelestialNodal
open GppLogDerivZeroFree
open GppArithmeticConformalKinematics

/-! ## Conjugate-shadow characterisation of the principal series -/

/-- The celestial shadow involution `Δ ↦ d − Δ`. -/
noncomputable def shadow (d : ℝ) (Delta : ℂ) : ℂ :=
  (d : ℂ) - Delta

/-- The conjugate shadow `d − conj(Δ)`. Self-conjugacy under this map
is the principal-series condition. -/
noncomputable def conjShadow (d : ℝ) (Delta : ℂ) : ℂ :=
  (d : ℂ) - conj Delta

/-- **Pasterski–Shao fixed line.** A weight equals its conjugate shadow
if and only if it lies on the principal continuous series
`Re Δ = d/2`. For `d = 1` this is the critical line; the
two-dimensional celestial case `d = 2` recovers `Re Δ = 1`. -/
theorem eq_conjShadow_iff_principal (d : ℝ) (Delta : ℂ) :
    Delta = conjShadow d Delta ↔ Delta.re = d / 2 := by
  unfold conjShadow
  constructor
  · intro h
    have hre := congrArg re h
    simp [sub_re, conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [sub_re, conj_re, h]
      linarith
    · simp [sub_im, conj_im]

/-- In one boundary dimension the conjugate-shadow identity is
exactly `Δ = 1 − conj(Δ)`, i.e. the critical line. No halving. -/
theorem eq_one_sub_conj_iff_critical_line (Delta : ℂ) :
    Delta = (1 : ℂ) - conj Delta ↔ Delta.re = 1 / 2 :=
  eq_conjShadow_iff_principal 1 Delta

/-- The named one-dimensional principal-series predicate is the
conjugate-shadow fixed locus. -/
theorem isPrincipal_iff_eq_one_sub_conj (Delta : ℂ) :
    IsPrincipalDimensionOne Delta ↔ Delta = (1 : ℂ) - conj Delta := by
  unfold IsPrincipalDimensionOne
  exact (eq_conjShadow_iff_principal 1 Delta).symm

/-- Shadow is an involution for every boundary dimension. -/
theorem shadow_involution (d : ℝ) (Delta : ℂ) :
    shadow d (shadow d Delta) = Delta := by
  unfold shadow
  ring

/-- In `d = 1` the shadow is the functional-equation map `s ↦ 1 − s`. -/
theorem shadow_one_eq_one_sub (Delta : ℂ) :
    shadow 1 Delta = 1 - Delta := by
  unfold shadow
  rw [Complex.ofReal_one]

/-! ## Klein–Gordon radial normalizability in `d = 1` -/

/-- The existing massless Klein–Gordon radial weight in one boundary
dimension is scale-invariant if and only if the weight equals its
conjugate shadow. This is Pasterski–Shao (4.7)–(4.9) specialised to
`d = 1` and rewritten in conjugate-shadow language. The
distributional delta itself is not re-formalized (see
`GppOneDimensionalMellinWeight` and `GppMellinPlancherel`). -/
theorem kg_normalized_iff_eq_conjShadow
    (Delta : ℂ) {u : ℝ} (hu : u ≠ 0) :
    masslessKgLogRadialWeight 1 Delta.re u = 1 ↔
      Delta = (1 : ℂ) - conj Delta := by
  rw [massless_kg_radial_scale_invariant_iff_principal 1 Delta.re hu]
  exact (eq_conjShadow_iff_principal 1 Delta).symm

/-- Completeness direction, `d = 1`: a radially Klein–Gordon-normalized
weight is a principal-series weight. Pasterski–Shao prove this direction
(normalizable ⇒ principal). The converse direction applied to `ξ`-zeros
is `XiZeroIsNormalizable1dState` below, and is not a theorem of
theirs. -/
theorem normalizable_1d_implies_principal
    {Delta : ℂ} {u : ℝ} (hu : u ≠ 0)
    (hkg : masslessKgLogRadialWeight 1 Delta.re u = 1) :
    IsPrincipalDimensionOne Delta :=
  (physical_massless_one_dimensional_principal_iff_kg_unitary hu).mpr hkg

/-- The character identity `s = Δ₁` holds at every complex label,
including off-axis points. It is an equality of dilation characters,
not an identification of `ξ` with a celestial two-point function,
Plancherel density, or conformal primary wavefunction. -/
theorem s_eq_delta_1d_holds_for_every_label (s : ℂ) (x : ℝ) :
    logScaleCharacter s x * Complex.exp ((x : ℂ) / 2) =
      conformalDilation s x :=
  mellin_character_equals_1d_conformal_weight s x

/-! ## The `F_θ` test -/

/-- An off-axis zero of `F_θ` produced by a critical-line zero of `ξ`
fails every `d = 1` normalizability test: it is not principal series,
its Klein–Gordon radial weight is not scale-invariant, and it is not
equal to its conjugate shadow. Shadow symmetry of `F_θ` is used only
to record that the functional equation is not the missing ingredient. -/
theorem ftheta_off_axis_zero_fails_1d_normalizability
    {ρ : ℂ} (hρ : xi ρ = 0) (hre : ρ.re = 1 / 2)
    {u : ℝ} (hu : u ≠ 0) :
    let σ := ρ + 1 / 4
    Ftheta σ = 0 ∧
      ¬ IsPrincipalDimensionOne σ ∧
      masslessKgLogRadialWeight 1 σ.re u ≠ 1 ∧
      σ ≠ (1 : ℂ) - conj σ := by
  intro σ
  have hoff := Ftheta_zeros_off_line (ρ := ρ) hρ hre
  have hreσ : σ.re = 3 / 4 := by
    change (ρ + 1 / 4).re = 3 / 4
    exact hoff.2.2.1
  refine ⟨hoff.1, ?_, ?_, ?_⟩
  · unfold IsPrincipalDimensionOne
    intro hprin
    have : (3 / 4 : ℝ) = 1 / 2 := by
      calc (3 / 4 : ℝ) = σ.re := hreσ.symm
        _ = 1 / 2 := hprin
    norm_num at this
  · intro hkg
    have hc : σ.re = (1 : ℝ) / 2 :=
      (massless_kg_radial_scale_invariant_iff_principal 1 σ.re hu).mp hkg
    have : (3 / 4 : ℝ) = 1 / 2 := by
      calc (3 / 4 : ℝ) = σ.re := hreσ.symm
        _ = 1 / 2 := hc
    norm_num at this
  · intro hsh
    have hc : σ.re = (1 : ℝ) / 2 :=
      (eq_conjShadow_iff_principal 1 σ).mp hsh
    have : (3 / 4 : ℝ) = 1 / 2 := by
      calc (3 / 4 : ℝ) = σ.re := hreσ.symm
        _ = 1 / 2 := hc
    norm_num at this

/-- **F_θ test, summarised.** The adversary has the functional equation
/ shadow pairing `s ↦ 1 − s`, but not every zero is principal series
(hence not every zero is `d = 1` Klein–Gordon normalizable). The
existence of a critical-line zero of `ξ` is a hypothesis, as in
`Ftheta_zeros_off_line` (Hardy is not formalized). -/
theorem ftheta_has_shadow_but_zeros_not_all_principal
    {ρ : ℂ} (hρ : xi ρ = 0) (hre : ρ.re = 1 / 2) :
    (∀ s : ℂ, Ftheta (1 - s) = Ftheta s) ∧
      ¬ (∀ z : ℂ, Ftheta z = 0 → IsPrincipalDimensionOne z) := by
  refine ⟨Ftheta_one_sub, ?_⟩
  intro hall
  have hoff := Ftheta_zeros_off_line (ρ := ρ) hρ hre
  have hprin := hall (ρ + 1 / 4) hoff.1
  have hreσ : (ρ + 1 / 4).re = 3 / 4 := hoff.2.2.1
  unfold IsPrincipalDimensionOne at hprin
  have : (3 / 4 : ℝ) = 1 / 2 := by
    calc (3 / 4 : ℝ) = (ρ + 1 / 4).re := hreσ.symm
      _ = 1 / 2 := hprin
  norm_num at this

/-! ## The open zero-to-state step -/

/-- Every completed-`ξ` zero is a delta-normalizable weight of the
`d = 1` (dimensionally reduced) celestial theory. Definitionally the
in-tree `AllXiZerosKGNormalized`. This is the missing converse of
Pasterski–Shao completeness, and it must fail for `F_θ`
(`ftheta_has_shadow_but_zeros_not_all_principal`). -/
def XiZeroIsNormalizable1dState : Prop :=
  AllXiZerosKGNormalized

/-- Conditional only: if the zeros are normalizable `d = 1` states, RH
follows. This does not assert the hypothesis. -/
theorem rh_of_xi_zero_is_normalizable_1d_state
    (h : XiZeroIsNormalizable1dState) : RiemannHypothesis :=
  riemannHypothesis_of_all_xi_zeros_kg_normalized h

/-- OPEN: `XiZeroIsNormalizable1dState`. Pasterski–Shao do not supply
this. A non-circular discharge cannot assume the zeros' real parts, and
the same formal move is already false for `F_θ`. -/
theorem open_xi_zero_is_normalizable_1d_state : True := trivial

#print axioms eq_conjShadow_iff_principal
#print axioms eq_one_sub_conj_iff_critical_line
#print axioms isPrincipal_iff_eq_one_sub_conj
#print axioms kg_normalized_iff_eq_conjShadow
#print axioms normalizable_1d_implies_principal
#print axioms s_eq_delta_1d_holds_for_every_label
#print axioms ftheta_off_axis_zero_fails_1d_normalizability
#print axioms ftheta_has_shadow_but_zeros_not_all_principal
#print axioms rh_of_xi_zero_is_normalizable_1d_state

end GppPasterskiShao
