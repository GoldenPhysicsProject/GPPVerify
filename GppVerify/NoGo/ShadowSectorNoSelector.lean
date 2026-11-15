import Mathlib.Analysis.Complex.Basic

/-!
# No sector of a prime-side involution removes the negative square of an off-line quartet

Heart's PR #11 filings 6888342648 / 6888360390 (GPP-bridge `GROK_RESEARCH_NOTES.md` @ 27691cf),
audited by Turbo (bridge CONVERSATION.md, 2026-11-14 ~22:35 EST: "clean kill"). This file is the
block-level linear algebra, in Lean.

**Setting.** The spectral face of the Weil form is `W(f) = Σ_ρ m_ρ f̂(ρ) · conj f̂(1 - ρ̄)`. An off-line
zero `ρ` comes in a quartet `ρ, 1 - ρ̄, ρ̄, 1 - ρ`; write `v = (a, b, c, d)` for the values of `f̂` there.
The quartet's contribution (per unit multiplicity) is

  `quartetForm v = 2 Re(a · conj b) + 2 Re(c · conj d)`

(the pairs `ρ ↔ 1 - ρ̄` and `ρ̄ ↔ 1 - ρ`). The three prime-side involutions on test functions act on
`v` by (`f̂ ↦ f̂(1 - s)`, `f̂ ↦ conj f̂(s̄)`, and their composite):

* `K v = (d, c, b, a)`;
* `C v = (conj c, conj d, conj a, conj b)`;
* `J v = C (K v) = (conj b, conj a, conj d, conj c)` (`J_eq`).

**Theorem (`exists_neg_in_every_sector`).** For each `τ ∈ {K, C, J}` and each sign `ε = ±1` there is a
quartet vector with `τ v = ε v` and `quartetForm v < 0`. So restricting the Weil form to the even or
odd sector of any of these involutions never removes an off-line quartet's negative direction: a
sector is a block, not a selector. This is the "restrict the sector" door, closed at block level.

**Scope.** Finite linear algebra only. The passage from test functions to the quartet coordinates
(that a concentration family realises an arbitrary sector vector, modulo Flint's TailLemma) is not
formalised; `W`'s explicit formula is not formalised here. Nothing here proves or refutes RH:
`WeilIsGram`, `HPsi`, RH stay OPEN. No `sorry`, no axioms.
-/

namespace GppShadowSector

open Complex ComplexConjugate

/-- Values of `f̂` at `ρ, 1 - ρ̄, ρ̄, 1 - ρ`. -/
abbrev Q4 := ℂ × ℂ × ℂ × ℂ

/-- The off-line quartet's contribution to the Weil form, per unit multiplicity. -/
def quartetForm (v : Q4) : ℝ :=
  2 * (v.1 * conj v.2.1).re + 2 * (v.2.2.1 * conj v.2.2.2).re

/-- `f ↦ x⁻¹ f(1/x)`, i.e. `f̂ ↦ f̂(1 - s)`. -/
def K (v : Q4) : Q4 := (v.2.2.2, v.2.2.1, v.2.1, v.1)

/-- Complex conjugation of `f`, i.e. `f̂ ↦ conj f̂(s̄)`. -/
def C (v : Q4) : Q4 := (conj v.2.2.1, conj v.2.2.2, conj v.1, conj v.2.1)

/-- The shadow involution `J = C ∘ K`, i.e. `f̂ ↦ conj f̂(1 - s̄)`. -/
def J (v : Q4) : Q4 := C (K v)

theorem J_eq (v : Q4) : J v = (conj v.2.1, conj v.1, conj v.2.2.2, conj v.2.2.1) := rfl

theorem K_invol (v : Q4) : K (K v) = v := rfl

theorem C_invol (v : Q4) : C (C v) = v := by
  obtain ⟨a, b, c, d⟩ := v; simp [C]

theorem J_invol (v : Q4) : J (J v) = v := by
  obtain ⟨a, b, c, d⟩ := v; simp [J, C, K]

/-- **No sector of `K`, `C` or `J` removes the negative square.** -/
theorem exists_neg_in_every_sector :
    (∃ v : Q4, K v = v ∧ quartetForm v < 0) ∧ (∃ v : Q4, K v = -v ∧ quartetForm v < 0) ∧
    (∃ v : Q4, C v = v ∧ quartetForm v < 0) ∧ (∃ v : Q4, C v = -v ∧ quartetForm v < 0) ∧
    (∃ v : Q4, J v = v ∧ quartetForm v < 0) ∧ (∃ v : Q4, J v = -v ∧ quartetForm v < 0) := by
  refine ⟨⟨(1, -1, -1, 1), ?_, ?_⟩, ⟨(1, -1, 1, -1), ?_, ?_⟩, ⟨(1, -1, 1, -1), ?_, ?_⟩,
    ⟨(I, -I, I, -I), ?_, ?_⟩, ⟨(I, -I, 0, 0), ?_, ?_⟩, ⟨(1, -1, 0, 0), ?_, ?_⟩⟩ <;>
    simp [K, C, J, quartetForm]

/-- On the critical line the pair collapses (`1 - ρ̄ = ρ`): the contribution `a · conj a` is `≥ 0`. -/
theorem online_nonneg (a : ℂ) : 0 ≤ (a * conj a).re := by
  rw [mul_conj]; simp [Complex.normSq_nonneg]

end GppShadowSector

#print axioms GppShadowSector.exists_neg_in_every_sector
