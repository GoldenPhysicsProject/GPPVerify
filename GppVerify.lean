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
