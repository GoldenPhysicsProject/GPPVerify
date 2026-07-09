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

-- ── Number Theory (New) ──────────────────────────────────────
-- Shadow Euler Identity and Hadamard product stubs
import GppVerify.NumberTheory.ShadowEulerIdentity

-- Weyl vector Casimir ⟨ρ_G,ρ_G⟩ = 5 for U(4) (proved clean)
import GppVerify.NumberTheory.WeylCasimir

-- Zeta function properties from Mathlib 4.19.0 (critical line, trivial zeros, RH)
import GppVerify.NumberTheory.ZetaProperties

-- ── RH Proof Structure (New) ─────────────────────────────────
-- Spectral-multiplicity / temperedness / BRST proof architecture
import GppVerify.RiemannHypothesis.RHProofStructure

-- Haar positivity = Weil positivity = Wightman positivity (unified)
import GppVerify.RiemannHypothesis.HaarPositivityWeil

-- ── Standard Model — Majorana (New) ─────────────────────────
-- Majorana neutrinos from T-boundary condition
import GppVerify.StandardModel.MajoranaCondition

-- ── Celestial Holography — Twistor (New) ────────────────────
-- Googly problem resolution via Haar self-duality on Gr(2,4)
import GppVerify.CelestialHolography.TwistorGoogly

-- ── Yang-Mills (New) ─────────────────────────────────────────
-- Mass gap existence and Sugawara formula M = 2N/(k+N)·Λ_QCD
import GppVerify.YangMills.MassGap

-- ── Quantum Gravity — Wightman (New) ────────────────────────
-- All 6 Wightman axioms derived from Gr(2,4) + Penrose + Peter-Weyl
import GppVerify.QuantumGravity.WightmanAxioms

-- ── String Theory / Division Algebras (New) ──────────────────
-- Why string theory works: Hurwitz, critical dims, 3 generations
import GppVerify.StringTheory.DivisionAlgebras

-- ── Holographic Chain (New) ───────────────────────────────────
-- Division algebra tower R→C→H→O terminating at Gr(2,4)
import GppVerify.CelestialHolography.HolographicChain

-- ── Decoding Reality (New) ───────────────────────────────────
-- Standard Model parameters as L-function values
import GppVerify.NumberTheory.DecodingReality

-- ── Dark Energy (New) ─────────────────────────────────────────
-- Dark energy w(a) from T-boundary conformal self-lensing
import GppVerify.Cosmology.DarkEnergy

-- ── Unified Dipole (New) ──────────────────────────────────────
-- Number-count dipole anomaly from Haar shadow deficit
import GppVerify.Cosmology.UnifiedDipole

-- ── Grassmannian Chart Transition (New) ───────────────────────
-- Chart transition map on Gr(2,4): tau o tau = -id (Zitterbewegung
-- as period-4 chart oscillation)
import GppVerify.GrassmannianMass

-- ── Mass as Orientation Coupling (New) ────────────────────────
-- Theorem 3.3(i): the orientation map tau(A) = A eps / det(A)
-- satisfies tau^2 = -id, tau^4 = id
import GppVerify.StandardModel.MassOrientationCoupling

-- ── The Half-Flip Proposition (New) ───────────────────────────
-- Lemma 2.1: antiunitary conjugation = unitary o transpose on
-- Hermitian inputs; Wigner time reversal T^2 = -1
import GppVerify.StandardModel.HalfFlipProposition

-- ── The Half-Flip Obstruction, finite matrix core (New) ───────
-- SWAP has eigenvalue -1, witnessed exactly by the antisymmetric
-- singlet vector (Choi(transpose) = SWAP is not positive semidefinite)
import GppVerify.QuantumInformation.HalfFlipMatrix
