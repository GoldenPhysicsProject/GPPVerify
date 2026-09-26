import GppVerify.RiemannHypothesis.TwoPointCriterion
import Mathlib.Tactic

/-!
# Krein graph closure of the two-point Weil criterion

The doubled BPY / Hodge boundary program naturally produces an indefinite form with one
positive and one negative Hilbert sector.  A subspace presented as the graph of a transfer
map C has Krein energy

  q(x) = ||x||^2 - ||C x||^2.

Hence positivity on the graph is exactly contractivity of C.  This file formalizes that
last algebraic step and connects it directly to the already-certified two-point Weil
criterion.

No contractivity of the arithmetic transfer is assumed to have been proved here.  That is
the remaining analytic statement.
-/

namespace GppWeilCriterion

/-- A contractive transfer has nonnegative graph/Krein energy. -/
theorem kreinGraph_nonneg_of_contract
    {Hplus Hminus : Type*}
    [NormedAddCommGroup Hplus] [NormedAddCommGroup Hminus]
    (C : Hplus → Hminus)
    (hC : ∀ x, ‖C x‖ ≤ ‖x‖) :
    ∀ x, 0 ≤ ‖x‖ ^ 2 - ‖C x‖ ^ 2 := by
  intro x
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hCx : 0 ≤ ‖C x‖ := norm_nonneg (C x)
  have hle := hC x
  nlinarith

/-- Conversely, nonnegative graph energy forces the transfer to be contractive. -/
theorem contract_of_kreinGraph_nonneg
    {Hplus Hminus : Type*}
    [NormedAddCommGroup Hplus] [NormedAddCommGroup Hminus]
    (C : Hplus → Hminus)
    (hQ : ∀ x, 0 ≤ ‖x‖ ^ 2 - ‖C x‖ ^ 2) :
    ∀ x, ‖C x‖ ≤ ‖x‖ := by
  intro x
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hCx : 0 ≤ ‖C x‖ := norm_nonneg (C x)
  have h := hQ x
  nlinarith

/-- Graph positivity is exactly transfer contractivity. -/
theorem kreinGraph_nonneg_iff_contract
    {Hplus Hminus : Type*}
    [NormedAddCommGroup Hplus] [NormedAddCommGroup Hminus]
    (C : Hplus → Hminus) :
    (∀ x, 0 ≤ ‖x‖ ^ 2 - ‖C x‖ ^ 2) ↔
      (∀ x, ‖C x‖ ≤ ‖x‖) := by
  constructor
  · exact contract_of_kreinGraph_nonneg C
  · exact kreinGraph_nonneg_of_contract C

/--
**Krein-graph closure to RH.**

Suppose every reflection-pair Weil form is realized as the graph energy of a transfer
operator C_rho, and that each such transfer is contractive.  Then the two-point Weil form
is nonnegative, so the existing two-point criterion forces every nontrivial zeta zero
onto the critical line.

This is the exact formal endpoint of the doubled BPY statement
"odd transfer is contractive".
-/
theorem rh_of_twoPoint_kreinGraph_contraction
    {Hplus Hminus : Type*}
    [NormedAddCommGroup Hplus] [NormedAddCommGroup Hminus]
    (C : ℂ → Hplus → Hminus)
    (hcontract :
      ∀ ρ ∈ nontrivialZeros, ∀ x, ‖C ρ x‖ ≤ ‖x‖)
    (hrealize :
      ∀ ρ ∈ nontrivialZeros, ∀ c : ℂ → ℂ,
        ∃ x : Hplus,
          (pairedForm zetaInvolution
              ({ρ, zetaInvolution ρ} : Finset ℂ) c).re
            = ‖x‖ ^ 2 - ‖C ρ x‖ ^ 2) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_iff_two_point_pairedForm_nonneg.mpr
  intro ρ hρ c
  obtain ⟨x, hx⟩ := hrealize ρ hρ c
  rw [hx]
  exact kreinGraph_nonneg_of_contract (C ρ) (hcontract ρ hρ) x

end GppWeilCriterion
