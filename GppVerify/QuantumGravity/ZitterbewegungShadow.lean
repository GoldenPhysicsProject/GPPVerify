import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Zitterbewegung from shadow symmetry: the exact arithmetic layer

Thread Z of `docs/FORMALIZATION_PLAN.md`, from `zitterbewegung_T_boundary_FINAL.tex`
(Proposition "Zitterbewegung frequency from shadow symmetry" and Theorem "Mirror baryon
density from `T` symmetry"). The chirality-swap/oscillation structure is already
formalized (`CoreTheorems.lean`'s boundary-oscillator lemmas, `MajoranaCondition.lean`);
this file adds the proposition's exact computational content:

* `shadow_energy_eq` — the shadow partner of a state of energy `E` under the Mellin map
  `λ = log(E/μ)` has energy `Ẽ = μ·e^{−λ} = μ²/E` **exactly** (a real `exp`/`log`
  identity, the one genuinely analytic step of the proposition);
* `shadow_splitting` / `shadow_splitting_onshell` — the energy splitting `E − μ²/E`, and
  its vanishing at the on-shell Mellin scale `μ = E`;
* `shadow_frequency_onshell` — the interference frequency `(E + μ²/E)/ℏ` equals `2E/ℏ`
  at `μ = E`: with `E = mc²` this is the Zitterbewegung frequency `2mc²/ℏ`;
* `beat_frequency` — the beat between phase frequencies `±E/ℏ` is `2E/ℏ`, the paper's
  closing identification.
* `mirror_dm_bound` — the mirror-baryon theorem's arithmetic: if the mirror sector
  carries `Ω_mirror = Ω_b` and contributes to dark matter, then `Ω_DM/Ω_b ≥ 1`.

The physical identifications (which state is the Dirac negative-energy component, that
mirror baryons interact only gravitationally) are the paper's physics inputs and are
recorded as hypotheses or documentation, never smuggled into the mathematics.
-/

namespace GppZitter

/-- **The shadow energy**: under `λ = log(E/μ)`, the shadow partner's energy is
    `Ẽ = μ·e^{−λ} = μ²/E`, exactly. -/
theorem shadow_energy_eq {E μ : ℝ} (hE : 0 < E) (hμ : 0 < μ) :
    μ * Real.exp (-(Real.log (E / μ))) = μ ^ 2 / E := by
  rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < E / μ)]
  field_simp
  ring

/-- The shadow splitting `E − Ẽ = E − μ²/E`. -/
theorem shadow_splitting {E μ : ℝ} (hE : 0 < E) (hμ : 0 < μ) :
    E - μ * Real.exp (-(Real.log (E / μ))) = E - μ ^ 2 / E := by
  rw [shadow_energy_eq hE hμ]

/-- At the on-shell Mellin scale `μ = E` the splitting vanishes. -/
theorem shadow_splitting_onshell {E : ℝ} (hE : E ≠ 0) :
    E - E ^ 2 / E = 0 := by
  field_simp

/-- **The Zitterbewegung frequency**: at `μ = E` the interference frequency
    `(E + Ẽ)/ℏ` is exactly `2E/ℏ` — with `E = mc²`, the classical `2mc²/ℏ`. -/
theorem shadow_frequency_onshell {E hbar : ℝ} (hE : E ≠ 0) (hh : hbar ≠ 0) :
    (E + E ^ 2 / E) / hbar = 2 * E / hbar := by
  rw [show E ^ 2 / E = E from by field_simp]
  ring

/-- The beat between the phase frequencies `+E/ℏ` and `−E/ℏ` is `2E/ℏ`. -/
theorem beat_frequency {E hbar : ℝ} (hE : 0 < E) (hh : 0 < hbar) :
    |E / hbar - (-(E / hbar))| = 2 * E / hbar := by
  rw [sub_neg_eq_add, abs_of_pos (by positivity)]
  ring

/-- **The mirror dark-matter bound**: if the mirror sector carries baryon density equal
    to the Standard Model's (`Ω_mirror = Ω_b`, the `T`-symmetry input) and contributes to
    the dark-matter budget (`Ω_mirror ≤ Ω_DM`), then `Ω_DM/Ω_b ≥ 1`. -/
theorem mirror_dm_bound {Ωdm Ωb Ωmirror : ℝ} (hb : 0 < Ωb)
    (hmirror : Ωmirror = Ωb) (hle : Ωmirror ≤ Ωdm) :
    1 ≤ Ωdm / Ωb := by
  rw [le_div_iff₀ hb]
  linarith

end GppZitter
