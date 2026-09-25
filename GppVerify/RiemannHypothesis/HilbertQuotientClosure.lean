import GppVerify.RiemannHypothesis.TwoPointCriterion
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Honest Hilbert-quotient closure of the two-point Weil criterion

The zero-side criterion is already formalized: RH is equivalent to nonnegativity of the
Weil/Yakaboylu form on each reflection pair {rho, 1-conj rho}.

This module isolates the exact geometric endpoint of the current Hodge/Rosati program.
If a completed arithmetic quotient realizes every such two-point form as the squared norm
of an honest vector in a positive complex Hilbert space, positivity is automatic and the
existing two-point theorem gives RH.

The theorem is intentionally hypothesis-explicit.  Constructing this realization from the
prime occupation Hodge bulk plus the global co-Poisson/BPY boundary is the analytic
problem; it is not assumed to have been solved elsewhere.
-/

namespace GppWeilCriterion

open Finset

/-- An honest Hilbert-space realization of every two-point Weil form forces every
nontrivial zero onto the critical line. -/
theorem rh_of_honest_twoPoint_hilbert_realization
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (hrealize :
      ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
        ∃ v : V,
          pairedForm zetaInvolution
              ({ρ, zetaInvolution ρ} : Finset ℂ) c
            = inner ℂ v v) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_iff_two_point_pairedForm_nonneg.mpr
  intro ρ hρ c
  obtain ⟨v, hv⟩ := hrealize ρ hρ c
  rw [hv]
  exact inner_self_nonneg

/-- Pointwise conditional-RH form of the same closure theorem. -/
theorem critical_line_of_honest_twoPoint_hilbert_realization
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (hrealize :
      ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
        ∃ v : V,
          pairedForm zetaInvolution
              ({ρ, zetaInvolution ρ} : Finset ℂ) c
            = inner ℂ v v)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.re = 1 / 2 := by
  exact rh_of_honest_twoPoint_hilbert_realization hrealize ρ ⟨hzero, h0, h1⟩

end GppWeilCriterion
