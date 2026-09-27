import Mathlib.Tactic
import GppVerify.CelestialHolography.SturmSchwarzianProjectiveBridge

/-!
# Schwarzian chain rule at the level of finite jets

For composable one-variable maps `g` and `f`, write the first three derivatives at a point as

    f1, f2, f3,
    g1, g2, g3.

The chain rule gives the jets of `h = g ∘ f`

    h1 = g1 f1,
    h2 = g2 f1^2 + g1 f2,
    h3 = g3 f1^3 + 3 g2 f1 f2 + g1 f3.

The Schwarzian derivative obeys

    S(g ∘ f) = f1^2 S(g) + S(f).

This module proves that identity purely algebraically from the jets.  No differentiability
or composition theorem is hidden here: when applying it to actual functions, one supplies the
ordinary calculus statement that these are their derivative jets.

For the GPP googly programme this is the missing local coordinate-change term.  If a target
Sturm/projective connection has potential `U(z)`, then after a general coordinate change
`z=f(r)` its pulled-back potential is

    U_pull(r) = f'(r)^2 U(f(r)) + 1/2 S(f)(r).

The Schwarzian correction vanishes only for Möbius reparametrizations.
-/

namespace GppSchwarzianChainRuleJets

open GppSturmSchwarzianProjectiveBridge

/-- First derivative jet of a composite. -/
def composeJet1 (f1 g1 : ℝ) : ℝ := g1 * f1

/-- Second derivative jet of a composite. -/
def composeJet2 (f1 f2 g1 g2 : ℝ) : ℝ := g2 * f1^2 + g1 * f2

/-- Third derivative jet of a composite. -/
def composeJet3 (f1 f2 f3 g1 g2 g3 : ℝ) : ℝ :=
  g3 * f1^3 + 3 * g2 * f1 * f2 + g1 * f3

/-- Exact finite-jet Schwarzian chain rule. -/
theorem schwarzian_chain_rule_jets
    (f1 f2 f3 g1 g2 g3 : ℝ)
    (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0) :
    schwarzianFromJets
        (composeJet1 f1 g1)
        (composeJet2 f1 f2 g1 g2)
        (composeJet3 f1 f2 f3 g1 g2 g3)
      =
    f1^2 * schwarzianFromJets g1 g2 g3
      + schwarzianFromJets f1 f2 f3 := by
  unfold schwarzianFromJets composeJet1 composeJet2 composeJet3
  field_simp [hf1, hg1]
  ring

/-- Projective-potential form of the chain rule.  If `g` has Schwarzian `2U`, then
`g ∘ f` has Schwarzian `2(f1^2 U + S(f)/2)`. -/
theorem pulledBack_potential_from_chain_rule
    (f1 f2 f3 g1 g2 g3 U : ℝ)
    (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0)
    (hg : schwarzianFromJets g1 g2 g3 = 2 * U) :
    schwarzianFromJets
        (composeJet1 f1 g1)
        (composeJet2 f1 f2 g1 g2)
        (composeJet3 f1 f2 f3 g1 g2 g3)
      =
    2 * (f1^2 * U + (1/2 : ℝ) * schwarzianFromJets f1 f2 f3) := by
  rw [schwarzian_chain_rule_jets f1 f2 f3 g1 g2 g3 hf1 hg1, hg]
  ring

/-- Equality to another projective connection `2P` is equivalent to the standard
coordinate-pullback equation

    P = f1^2 U + 1/2 S(f).
-/
theorem target_schwarzian_eq_composite_iff_pulledBack_potential
    (P f1 f2 f3 g1 g2 g3 U : ℝ)
    (hf1 : f1 ≠ 0) (hg1 : g1 ≠ 0)
    (hg : schwarzianFromJets g1 g2 g3 = 2 * U) :
    2 * P =
      schwarzianFromJets
        (composeJet1 f1 g1)
        (composeJet2 f1 f2 g1 g2)
        (composeJet3 f1 f2 f3 g1 g2 g3)
      ↔
    P = f1^2 * U + (1/2 : ℝ) * schwarzianFromJets f1 f2 f3 := by
  rw [pulledBack_potential_from_chain_rule f1 f2 f3 g1 g2 g3 U hf1 hg1 hg]
  constructor <;> intro h <;> linarith

end GppSchwarzianChainRuleJets
