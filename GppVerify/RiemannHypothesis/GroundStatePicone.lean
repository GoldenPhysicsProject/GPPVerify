import Mathlib.Tactic

/-!
# Picone / Doob ground-state edge identity: finite algebraic nucleus

Daniel Toupin / Golden Physics Project, 2026-10-15.
Research source: GPP-bridge/work/codex/
2026-10-15_chi4_positive_ground_state_first_prime_window.md.

The exact elementary two-vertex identity underlies the symmetric-jump
ground-state representation used to obtain an interval-assisted positive
lower bound for the primitive Dirichlet chi_4 first-prime window.

This module formalizes ONLY the exact finite edge identity and weighted
inequality; the Archimedean integral realization, interval enclosures,
and full chi_4 Weil inequality are not proved in Lean here.
No RH or GRH claim.
-/

namespace GppGroundStatePicone

/-- Exact edge identity with positive comparison weights a,b. -/
theorem edge_identity (a b u v : ℝ) :
    (a*u-b*v)^2 - (a-b)*(a*u^2-b*v^2)
      = a*b*(u-v)^2 := by
  ring

/-- A positive comparison profile bounds the edge energy below by
its ground-state potential, without requiring the test values to have a sign. -/
theorem edge_lower (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a-b)*(a*u^2-b*v^2) ≤ (a*u-b*v)^2 := by
  have hp : 0 ≤ a*b*(u-v)^2 := by positivity
  have he := edge_identity a b u v
  linarith

/-- Weighted edge identity for an arbitrary finite network. -/
theorem finite_edge_identity {ι : Type*} (s : Finset ι)
    (w a b u v : ι → ℝ) :
    (∑ i ∈ s, w i * ((a i*u i-b i*v i)^2 -
        (a i-b i)*(a i*(u i)^2-b i*(v i)^2))) =
      ∑ i ∈ s, w i*a i*b i*(u i-v i)^2 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [edge_identity]
  ring

/-- Every nonnegative symmetric edge weight preserves the comparison
lower bound after summing the local Picone identities. -/
theorem finite_edge_lower {ι : Type*} (s : Finset ι)
    (w a b u v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, w i * ((a i-b i) *
       (a i*(u i)^2-b i*(v i)^2))) ≤
      ∑ i ∈ s, w i * (a i*u i-b i*v i)^2 := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left
  · exact edge_lower (a i) (b i) (u i) (v i) (ha i hi) (hb i hi)
  · exact hw i hi

end GppGroundStatePicone
