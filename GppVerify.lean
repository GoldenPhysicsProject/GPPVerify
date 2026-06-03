-- GPPVerify: Golden Physics Project Lean 4 Formalization
-- Root module — imports all verified files
-- Author: Daniel Toupin | goldenphysics.org

-- ── Foundation ──────────────────────────────────────────────
-- Haar self-duality on compact groups (zero sorries, zero axioms)
import GppVerify.HaarSelfDuality

-- Shadow involution, T-symmetry, googly resolution (zero sorries, one standard axiom)
import GppVerify.CoreTheorems

-- ── RH Pathway 2: Spectral / Meyer ──────────────────────────
-- Adèlic Haar measure infrastructure
import GppVerify.RiemannHypothesis.HaarMeasure

-- Functional equation ξ(s) = ξ(1-s) from Haar self-duality
import GppVerify.RiemannHypothesis.FunctionalEquation

-- Shadow = time reversal (thm:shadow-cpt, most-cited result)
-- NOTE: three_generations_from_c0_and_link6 carries
--       "depends on thm:link6 — open problem"
import GppVerify.RiemannHypothesis.ShadowSymmetry

-- Spectral multiplicity argument + riemann_hypothesis theorem
-- (2 sorries in temperedness, 1 axiom: arithmetic_admissibility)
import GppVerify.RHSpectralMultiplicity

-- ── L² Constraint ────────────────────────────────────────────
-- L²(K¹) forces Re(s) = 1/2  (thm:l2-constraint, cited 12×)
import GppVerify.RiemannHypothesis.L2Constraint

-- ── Standard Model ───────────────────────────────────────────
-- Three generations from Cayley-Dickson tower (cor:three-generations-anomaly)
-- NOTE: three_generations + anomaly_cancellation carry
--       "depends on thm:link6 — open problem"
import GppVerify.StandardModel.ThreeGenerations

-- ── Celestial Holography ─────────────────────────────────────
-- c_{2D} = κ₀ × c_{4D}^Weyl  (thm:link6, formalized via physics axioms)
import GppVerify.CelestialHolography.Link6

-- Shadow operator discontinuity across the critical line
import GppVerify.CelestialHolography.ShadowDiscontinuity

-- ── RH Spectral Infrastructure ───────────────────────────────
-- Adèlic L² regularization on K¹ (lem:adelic-l2-regularization)
import GppVerify.RiemannHypothesis.AdelicL2

-- Spectral Weil explicit formula closes arithmetic admissibility
import GppVerify.RiemannHypothesis.SpectralWeil

-- ── Standard Model — Dark Matter ─────────────────────────────
-- DM abundance from shadow unitarity (thm:dm-abundance)
import GppVerify.StandardModel.DMAbundance

-- ── Quantum Gravity ──────────────────────────────────────────
-- Born rule from Haar measure on K¹ (lem:born-rule-haar)
import GppVerify.QuantumGravity.BornRuleHaar

-- ── General Relativity ───────────────────────────────────────
-- Einstein gravity uniqueness from shadow + c_{4D}^Weyl = 0 (thm:rigidity)
import GppVerify.GeneralRelativity.Rigidity
