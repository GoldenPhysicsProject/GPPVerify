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

-- Spectral multiplicity argument (two_zeros_at_ordinate, riemannZeta_conj).
-- riemann_hypothesis alias + arithmetic_admissibility axiom RETIRED 2026-07-17;
-- flagship conditional: GppWeilCriterion.rh_of_weil_pairedForm_nonneg
import GppVerify.RHSpectralMultiplicity

-- ── L² Constraint ────────────────────────────────────────────
-- L²(K¹) forces Re(s) = 1/2  (thm:l2-constraint, cited 12×)
import GppVerify.RiemannHypothesis.L2Constraint

-- ── Momentum generator has no point spectrum ────────────────
-- Pins down exactly why ONON's thm:no-ghosts-onon Step 1 needs the Cesàro
-- regularization rather than the ordinary L² inner product.
import GppVerify.RiemannHypothesis.MomentumGeneratorNoPointSpectrum

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

-- Tree-to-loop topology behind the shadow-discontinuity program (New). From Toupin
-- "Loop Integrands Hidden in Trees" (Aug 2026): a (4+2L)-point cubic tree, with L
-- disjoint leaf-pair sewings, is a connected 4-point graph of cycle rank exactly L
-- (pairSewing_cycleRank, proved for all L; sixPoint_onePair_oneLoop_counts specializes
-- to the one-loop box). Pure graph-theoretic combinatorics, unconditional. The genuinely
-- analytic celestial-sewing identity (inverse-Mellin of the pair shadow discontinuity =
-- momentum-space pair closure) is isolated as a LOCAL hypothesis,
-- ShadowPairSewing.sewing_identity, not proved here and not a global axiom -- it does
-- NOT discharge the existing celestial_amplitude_has_cut / disc_equals_loop_integrand /
-- shadow_disc_mellin_density stubs above, which are untouched. No axiom, no sorry.
import GppVerify.CelestialHolography.TreeLoopSewing

-- Dispersion reconstruction: proves the general (physics-convention-independent)
-- Sokhotski-Plemelj mechanism -- the exact finite-eps Lorentzian jump identity and
-- pointwise off-pole vanishing of the regulated kernel -- that TreeLoopSewing's
-- ShadowPairSewing.sewing_identity would need specialized to the actual six-point
-- celestial tree (three named hypotheses H1-H3, none proved here) to be DERIVED
-- rather than assumed. Does not discharge sewing_identity or any GppShadowDisc stub.
import GppVerify.CelestialHolography.DispersionReconstruction

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

-- Thread T: S-truncated transport — group-level positive-type, pullback along
-- the weighted-log chart; faithfulness of the prime chart (Z-linear independence
-- of {log p}, via Nat.factorization comparison) fully proved, no sorry
import GppVerify.RiemannHypothesis.TruncatedTransport

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

-- ── Spin-Statistics Eta (New, 2026-08-19, from ONON5213.tex) ─────
-- η(2n)/ζ(2n) = 1 - 2^{1-2n} for all n ≥ 1, and η(4)/ζ(4) = 7/8
import GppVerify.NumberTheory.SpinStatisticsEta

-- ── Squarefree Density Euler Product (New, 2026-08-19, ONON5213.tex) ──
-- ∏_p (1 - p⁻²) = 6/π² = 1/ζ(2), the arithmetic content of thm:squarefree
import GppVerify.NumberTheory.SquarefreeDensityZeta

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

-- ── General Choi matrix / complete positivity (New) ───────────
-- CompletelyPositive Phi => Choi(Phi) PosSemidef, general n; Choi's
-- theorem forward direction, no dependence on any specific map.
import GppVerify.QuantumInformation.ChoiMatrix

-- ── Proposition 2.2, complete (New) ────────────────────────────
-- Choi(transpose) = SWAP exactly, hence transpose map on M_2(C) is
-- not completely positive: no_enactment fully retired for d=2.
import GppVerify.QuantumInformation.TransposeNotCompletelyPositive

-- ── CHSH Bell violation + CKW monogamy (New, 2026-08-19, ONON5213.tex) ─
-- S = -1-√2 at the source's optimal angles, |S|>2, and the CKW
-- monogamy consequence 1+x²≤y²≤1 ⟹ x=0
import GppVerify.QuantumInformation.CHSHViolation

-- ── Grassmannian Jacobian, exact matrix identity (New) ────────
-- N^2 = D*K, K^2 = D^2*1, hence N^4 = D^4*1 for the chart
-- transition's Jacobian numerator matrix N (D = ad - bc)
import GppVerify.GrassmannianJacobian

-- ── BSD Point Counts (New) ────────────────────────────────────
-- Trace of Frobenius a_p for E: y^2 = x^3 - x over F_p, computed as
-- an actual Finset cardinality, at each small prime of good reduction;
-- Hasse bound a_p^2 <= 4p verified at each. BSD rank formula and
-- parity conjecture recorded as honest gaps (deep automorphic theory).
import GppVerify.NumberTheory.BSDPointCounts

-- ── Fubini-Study Antipodal Invariance, corrected (New) ────────
-- qg_foundations.tex's antipodal lemma compares bare densities and is
-- false except at |z|=1; the actual Jacobian-inclusive area-form
-- identity is proved here instead, plus an explicit counterexample to
-- the bare-density claim as literally stated in the source.
import GppVerify.CelestialHolography.FubiniStudyAntipodal

-- ── Zagier MZV Growth Recurrence, corrected (New) ─────────────
-- ONON5213.tex's Zagier recurrence d_w = d_{w-2}+d_{w-3} is formalized
-- with corrected initial conditions (the source's stated d_0=1,d_1=d_2=0
-- contradicts its own listed sequence); reproduces the listed sequence
-- exactly. Brown's deep theorem that this equals the true MZV dimension
-- is left untouched.
import GppVerify.NumberTheory.ZagierMZVGrowth

-- ── Dark Matter Gamma-Function Ratio (New) ────────────────────
-- The Grassmannian Spinor Bundle chapter's shadow kernel normalization
-- ratio N(1/2)/N(3/2) = Gamma(1/2)^2/Gamma(3/2)^2 = 4, formalized via
-- Mathlib's real Gamma function and its functional equation; feeds the
-- "factor of 5" leading term of Omega_DM/Omega_b.
import GppVerify.Cosmology.DarkMatterGammaRatio

-- ── Koide Relation Phase Sum (New) ─────────────────────────────
-- The SU(3)_F Weyl-orbit phase sum Sum_g cos(2*pi*g/3 - delta) = 0
-- for all delta, proved as an actual real-analysis theorem; combined
-- with the empirical Koide ratio Q=2/3 to derive epsilon = sqrt 2,
-- the source's boxed conclusion.
import GppVerify.StandardModel.KoideRelation

-- ── Complementary Pairs, exactly three (New) ──────────────────
-- An independent combinatorial route to "exactly three generations":
-- the fixed-point-free involutions on Fin 4 (partitions of {0,1,2,3}
-- into two complementary pairs) number exactly 3, decided over all
-- 4^4 candidate maps.
import GppVerify.StandardModel.ComplementaryPairs

-- ── Kappa Shadow-3 Sum Rule and Triality Angle (New) ───────────
-- The Fubini-Study Yukawa curvature kappa(x)=1+3x satisfies
-- kappa(x)+kappa(1-x)=5 for ANY x (shadow-3 sum rule), and the SM
-- sector angles satisfy arccos(sqrt(3/8))+arccos(sqrt(5/8))=pi/2
-- (triality complementary angle). The fitted numerical kappa values
-- (17/8, 5/2, 23/8) and their 5-12% agreement with experiment are
-- numerology, not formalized here.
import GppVerify.StandardModel.KappaShadow3

-- ── sl(2) Casimir / Riemann Quadratic-Form Identity (New) ──────
-- h(h-1) = -s(1-s) exactly for h=(1+i*lam)/2, s=1/2+i*lam/2: a pure
-- complex-algebra identity linking the principal-series Casimir to
-- the Riemann critical-line quadratic form, with no continuous
-- analysis needed.
import GppVerify.RiemannHypothesis.CasimirIdentity

-- ── E8 Theta Coefficients and 496 as a Perfect Number (New) ────
-- 240*sigma_3(n) matches the E8 theta series (weight-4 Eisenstein
-- series) at n=1..5, and 496=dim(E8) is the third perfect number,
-- 2^4*31 with 31=2^5-1 Mersenne prime -- finite Nat.sigma facts.
import GppVerify.NumberTheory.PerfectNumbersE8

-- ── zeta(-3), corrected (New) ───────────────────────────────────
-- decoding_reality_v43221.tex asserts zeta(-3) = -1/120; the correct
-- value, via Mathlib's riemannZeta_neg_nat_eq_bernoulli' and
-- bernoulli'_four, is +1/120. A fully clean, no-gap correction.
import GppVerify.NumberTheory.ZetaNegativeIntegers

-- ── Twin-prime singlets and doublets (Codex) ──────────────────
-- The prime gap-2 graph consists of isolated singlets and disjoint
-- doublets above 5; 3-5-7 is the unique overlapping triplet.
import GppVerify.NumberTheory.TwinPrimeDoublets

-- ── Character Orthogonality (New) ────────────────────────────────
-- Genuine harmonic-analysis infrastructure (not sourced from a specific
-- paper): for a left-invariant measure on a group and a nontrivial
-- multiplicative character chi, integral of chi vanishes. Built from
-- Mathlib's existing Haar/left-invariant integral theory, as a real
-- building block toward the adelic/spectral gaps in AdelicL2.lean and
-- L2Constraint.lean.
import GppVerify.RiemannHypothesis.CharacterOrthogonality

-- ── Gauss Sum Modulus Formula (New) ──────────────────────────────
-- The classical |gaussSum| = sqrt(card R) fact for a nontrivial
-- quadratic character, underlying epsilon-factor algebra in Tate's
-- thesis. Derived from Mathlib's existing gaussSum_sq -- real
-- infrastructure, not sourced from a specific paper.
import GppVerify.NumberTheory.GaussSumModulus

-- ── Haar Measure of a Finite-Index Subgroup (New) ────────────────
-- H.index * mu(H) = mu(univ) for a left-invariant measure and a
-- measurable finite-index subgroup H, built from first principles
-- (coset partition, coset disjointness via quotient-map fibers,
-- translation invariance). Real infrastructure toward the p-adic/
-- adelic integral computations Tate's thesis relies on, not sourced
-- from a specific paper.
import GppVerify.RiemannHypothesis.HaarSubgroupIndex

-- ── Haar Probability Measure on Z_p (New) ────────────────────────
-- Z_p (PadicInt p) is a compact topological additive group, so it
-- carries a canonical normalized Haar probability measure via
-- Mathlib's generic addHaarMeasure construction: mu(Z_p) = 1. Real
-- infrastructure toward the p-adic zeta integral, not paper-sourced.
import GppVerify.RiemannHypothesis.PadicHaarMeasure

-- ── Index of p^n Z_p in Z_p (New) ─────────────────────────────────
-- Nat.card (Z_p / p^n Z_p) = p^n, proved via surjectivity of
-- PadicInt.toZModPow n (a map whose restriction to N -> Z_p is
-- already surjective onto ZMod(p^n)) combined with the first
-- isomorphism theorem. Real infrastructure toward the p-adic zeta
-- integral, not paper-sourced.
import GppVerify.RiemannHypothesis.PadicIndexPn

-- ── Haar Measure of p^n Z_p (New) ─────────────────────────────────
-- The payoff: mu(p^n * Z_p) = p^{-n}, combining HaarSubgroupIndex,
-- PadicHaarMeasure, and PadicIndexPn. The p-adic integral formula
-- from Tate's-thesis lecture notes. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicZetaIntegral

-- ── p-adic Shell Measure (New) ────────────────────────────────────
-- The Haar measure of the "shell" p^n Z_p \ p^{n+1} Z_p (where
-- ||x|| = p^{-n} exactly) is p^{-n} - p^{-(n+1)}, the term-by-term
-- building block for the geometric-series zeta integral. Not
-- paper-sourced.
import GppVerify.RiemannHypothesis.PadicShellMeasure

-- ── Origin has Haar Measure Zero in Z_p (New) ────────────────────
-- mu({0}) = 0, needed to drop the origin when decomposing Z_p into
-- shells for the full zeta integral. Proved via a geometric-bound
-- squeeze (ENNReal.eq_zero_of_le_mul_pow), no limit machinery
-- needed. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicOriginMeasure

-- ── Exact Norm on a p-adic Shell (New) ────────────────────────────
-- Every x in the shell p^n Z_p \ p^{n+1} Z_p has ||x|| = p^{-n}
-- exactly (via PadicInt.mem_span_pow_iff_le_valuation pinning down
-- the valuation to exactly n), the last ingredient needed to
-- evaluate the full zeta integral as a geometric series. Not
-- paper-sourced.
import GppVerify.RiemannHypothesis.PadicShellNorm

-- ── p-adic Shell Partition (New) ──────────────────────────────────
-- Every nonzero x lies in exactly one shell p^n Z_p \ p^{n+1} Z_p
-- (n = x.valuation), giving a disjoint measurable countable
-- partition Z_p \ {0} = union of shells -- the decomposition needed
-- for the full zeta integral via lintegral_iUnion. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicFullZetaIntegral

-- ── The Full p-adic Zeta Integral: Closed Form (New) ──────────────
-- The capstone: integral over Z_p of ||x||^s dmu = (1 - 1/p) *
-- (1 - p^{-(s+1)})^{-1}, for every real s (Tate's-thesis lecture
-- notes, Example 4.10). Assembled from the shell partition, exact
-- shell measure, exact shell norm, and origin-measure-zero facts via
-- lintegral_iUnion and ENNReal.tsum_geometric. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicZetaIntegralClosedForm

-- ── Bridge to Mathlib's Euler Product (New) ───────────────────────
-- Mathlib already proves the Euler product for zeta
-- (riemannZeta_eulerProduct_tprod, Mathlib.NumberTheory.EulerProduct.
-- DirichletLSeries). This file bridges our local p-adic zeta integral
-- down to exactly that local factor (1 - p^{-s})^{-1}, cast correctly
-- through ENNReal -> Real -> Complex. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicEulerFactorBridge

-- ── Additive Haar Measure on the Full Field Q_p (New) ─────────────
-- First brick toward a genuine multiplicative Haar measure on Q_p^x:
-- the canonical additive Haar measure on all of Q_p (not just the
-- compact subring Z_p), normalized via the closed unit ball (= Z_p)
-- as the positive-compacts witness, matching Tate's own convention.
-- Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicFieldHaarMeasure

-- ── Multiplicative Haar Measure on Q_p, via withDensity (New) ─────
-- The multiplicative measure d^xx := dx/||x||, defined directly on
-- Q_p via Measure.withDensity rather than building Q_p^x as its own
-- topological group. Multiplicative invariance is NOT proved here
-- (needs a from-scratch Haar-measure scaling law for Q_p acting on
-- itself); this file only establishes the definition and the density
-- function's measurability. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicMultiplicativeMeasure

-- ── The Archimedean Local Zeta Integral (New) ─────────────────────
-- Tate's-thesis local factor at the real place: integral over R of
-- e^{-pi x^2} * |x|^{s-1} dx = pi^{-s/2} * Gamma(s/2), for real s>0.
-- Independent of the p-adic thread's open scaling-law question --
-- proved from Mathlib's half-line Gaussian-Gamma integral plus the
-- even-function doubling identity integral_comp_abs. Not paper-sourced.
import GppVerify.RiemannHypothesis.ArchimedeanZetaIntegral

-- ── Scaling Pushforward is Haar (New) ─────────────────────────────
-- First concrete brick of the Q_p^x scaling-law plan: multiplication
-- by a nonzero field element is a continuous additive automorphism
-- of Q_p, so pushing fieldHaarMeasure forward along it is again Haar
-- (ContinuousAddEquiv.isAddHaarMeasure_map), and that pushforward is
-- exactly S -> mu(a . S). Pinning down the exact scalar (||a||) via
-- Haar uniqueness is still open. Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicScalingHaar

-- ── Transferring haarMeasure_span_pow to Q_p (New) ────────────────
-- Step 5 of the scaling-law plan, executed: transfers the already-
-- proven mu(p^n Z_p) = p^-n fact from PadicInt p to Padic p, via
-- Measure.comap (pullback, not pushforward -- pushforward failed the
-- uniqueness theorem's own invariance hypothesis) along the open
-- embedding Z_p -> Q_p, using isAddHaarMeasure_eq_of_isProbabilityMeasure
-- to identify two probability Haar measures on the compact group Z_p.
-- Not paper-sourced.
import GppVerify.RiemannHypothesis.PadicHaarTransfer

-- ── Cesàro-mean divergence away from sigma = 1/2 (New) ────────────
-- Formalizes the divergence half of Lemma 3.1 of Toupin's "Riemann
-- Hypothesis as Haar Self-Duality" paper: for sigma != 1/2 the
-- symmetric Cesaro mean of r^(2sigma-1) diverges to +infinity, built
-- from scratch against Mathlib's "polynomial beats log" asymptotic
-- comparison. Combined with the pre-existing born_rule_cesaro
-- (RHProofStructure.lean, sigma = 1/2 gives exactly 1), this closes
-- the gap that file's own doc comment had explicitly flagged as not
-- formalized. Not derived from ONON52.tex.
import GppVerify.RiemannHypothesis.CesaroMeanDivergence

-- ── Abel regularization of the Cesàro mean (New) ──────────────────
-- Formalizes Theorem 3.2 of Toupin's Abel-Cesaro paper
-- (rh_cesaro_v2.tex): positivity of the regularized state omega_eps,
-- the character formula omega_eps(t^alpha) = eps^2/(eps^2 - alpha^2)
-- computed via two convergent exponential integrals in the log
-- variable, omega_eps(1) = 1 exactly, and the delta-selection limit
-- eps^2/(eps^2 + gamma^2) -> 0 (gamma != 0) driving the paper's
-- delta_{rho', 1-rho-bar} matrix-element limit. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.AbelCesaroRegularization

-- ── Periodic zeros of the eta factor 1 - 2^(1-s) (New) ────────────
-- Formalizes the elementary content of Yakaboylu (arXiv:2408.15135)
-- Definition 2.1: the periodic Dirichlet eta zeros sit exactly at
-- s = 1 - 2*pi*i*k/log 2 (via Complex.exp_eq_one_iff), all on the
-- line Re s = 1 -- outside the open critical strip, so the completed
-- eta function's zero set decomposes cleanly as Z_D union Z_R. Plus
-- the weight identity t e^t/(1+e^t)^2 = t/(4 cosh^2(t/2)) bridging
-- the Yakaboylu and Abel-Cesaro papers' conventions. Not from ONON52.
import GppVerify.RiemannHypothesis.CompletedEtaZeros

-- ── Yakaboylu's regularized matrix element, eq. (49) (New) ────────
-- The central calculation of Yakaboylu Lemma 4.3 in real-exponent
-- form: (eps/2)(int_0^1 t^(sigma-2+eps) + int_1^inf t^(sigma-2-eps))
-- = eps^2/(eps^2-(sigma-1)^2) on the strip 1-eps < sigma < 1+eps,
-- plus the two limit facts making it the Kronecker delta of eq. (47):
-- exactly 1 at sigma = 1, tends to 0 for sigma != 1. This is the
-- multiplicative-variable twin of AbelCesaroRegularization.lean's
-- log-variable character formula. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.YakaboyluMatrixElement

-- ── Arithmetic kernel of the positivity argument (New) ────────────
-- The finite linear algebra inside Yakaboylu Theorem 5.1 / eq. (67):
-- the two-point test vector pairing to exactly -2 when a zero is off
-- the critical line (the contradiction against W >= 0), and the
-- diagonal form being a nonnegative sum of |c|^2 when every zero is
-- self-dual. The operator-theoretic content (W well-defined and PSD
-- via oblique-projection compression) is deep unbounded-operator
-- theory, deliberately not formalized. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.YakaboyluPositivityKernel

-- ── Finite Weil-positivity criterion iff RH (New) ─────────────────
-- Thread D of docs/FORMALIZATION_PLAN.md: the rigorous
-- finitely-supported content of Yakaboylu Thm 5.1 + Prop 5.3
-- (Bombieri's refinement of Weil positivity). RH holds iff the
-- paired form sum conj(c(1-conj rho)) c(rho) is PSD on every finite
-- subset of the nontrivial zero set -- with the zero-set closure
-- under rho -> 1 - conj(rho) carried as a real theorem (functional
-- equation + proved conjugation symmetry), not an assumption. A
-- rigorous reduction, NOT a proof of RH: the analytic input that
-- would discharge the positivity hypothesis is not claimed.
import GppVerify.RiemannHypothesis.WeilPositivityCriterion

-- Thread D2: the two-point criterion — RH iff pair positivity;
-- the zero side of the Weil criterion carries no analytic content
import GppVerify.RiemannHypothesis.TwoPointCriterion

-- ── int_0^inf u/cosh^2(u) du = log 2 (New) ────────────────────────
-- Thread C2 of docs/FORMALIZATION_PLAN.md: eta(1) = log 2 in its
-- Mellin disguise -- the normalization constant of Yakaboylu's
-- biorthogonality relation (eq. 50) and the base case of the sech^2
-- Mellin transform behind N_{1/2} (rh_cesaro_v2 Prop 5.2). Proved
-- with NO series interchange: explicit antiderivative
-- F(u) = u tanh u - log cosh u with F' = u/cosh^2 and F -> log 2,
-- fed to integral_Ioi_of_hasDerivAt_of_nonneg (nonneg integrand =>
-- integrability and value in one step). Includes hasDerivAt_tanh,
-- absent from the pinned Mathlib. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.SechSquaredIntegral

-- ── N_{1/2} = log2/6 - 1/24 exactly (New) ─────────────────────────
-- Thread A2 of docs/FORMALIZATION_PLAN.md: the eigenstate norm at the
-- critical point (rh_cesaro_v2 Prop 5.2), with no series interchange:
-- the sech^4 antiderivative in tanh-polynomial form (tanh' = 1-tanh^2
-- via the once-proved Pythagorean bridge 1/cosh^2 = 1 - tanh^2), its
-- limit (2/3)log 2 reusing the sech^2 thread, the u-form integral
-- (2/3)log2 - 1/6, the t-variable form via G(t) = 4 F4(t/2) (no
-- change-of-variables lemma), and eigenstate_norm_half. Not from
-- ONON52.tex.
import GppVerify.RiemannHypothesis.SechFourthIntegral

-- ── N_sigma finite and positive across the strip (New) ────────────
-- Thread A1 of docs/FORMALIZATION_PLAN.md: for every sigma > 0 the
-- eigenstate norm N_sigma = (1/16) int_0^inf t^(2sigma)/cosh^4(t/2)
-- is a convergent integral (dominated by 16x the Euler Gamma
-- integrand at s = 2sigma+1) with strictly positive value (positive
-- integrand on a set of infinite measure). Consistency corollary:
-- eigenstateNorm (1/2) = log2/6 - 1/24, tying threads A1 and A2
-- together on the nose. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.EigenstateNormStrip

-- ── Alternating harmonic series = log 2 (New) ─────────────────────
-- Thread C1 of docs/FORMALIZATION_PLAN.md: eta(1) = log 2 in series
-- form, absent from the pinned Mathlib (whose log power series stops
-- strictly inside |x| < 1). Elementary integral-remainder proof: the
-- finite geometric sum integrated over [0,1] gives log 2 minus the
-- partial sum as an explicit remainder integral, sandwiched by
-- +-1/(n+1). With SechSquaredIntegral.lean this puts eta(1) = log 2
-- in the repo in both its Mellin and series incarnations. Not from
-- ONON52.tex.
import GppVerify.RiemannHypothesis.AlternatingHarmonicLog2

-- ── The Planck integral = pi^4/15 (New) ───────────────────────────
-- Phase 2 Thread P (blackbody_law_qg_v1.tex): the Stefan-Boltzmann
-- quartic int_0^inf x^3/(e^x - 1) dx = pi^4/15, executed classically
-- and in full: geometric expansion of 1/(e^x - 1) pointwise for x>0,
-- sum-integral interchange justified by summability of the term
-- norms (integral_tsum_of_summable_integral_norm), term integrals
-- Gamma(4)/(n+1)^4 = 6/(n+1)^4, and zeta(4) = pi^4/90 via Mathlib's
-- Bernoulli machinery. No step assumed. Not from ONON52.tex.
import GppVerify.QuantumGravity.PlanckIntegral

-- ── Mellin kinematics elementary layer (New) ──────────────────────
-- Phase 2 Thread M (mellin_kinematics.tex): power laws are THE
-- continuous homomorphisms of (R+, x) — proved via log/exp
-- conjugation to AddMonoidHom.toRealLinearMap, with unique alpha : R
-- (correcting the paper's alpha > 0 slip: the constant map and
-- inversion are homs too); the half-density scale shadow
-- (Sf)(x) = f(1/x)/x is involutive and preserves L^2 mass (the
-- u = 1/x substitution via integral_comp_rpow_Ioi at p = -1); and
-- the Mellin kernel transport Delta = alpha*s with the unitary-axis
-- match forcing alpha = 2 — the origin of the Delta = 2s dictionary.
import GppVerify.CelestialHolography.MellinKinematics

-- ── Convolution squares are positive-type (New) ───────────────────
-- Thread B of docs/FORMALIZATION_PLAN.md: closes the gap PR #45
-- honestly stubbed in HaarPositivityWeil.lean. For integrable bounded
-- f : R -> R and Lebesgue (= Haar) measure, P(x) = int f(y) f(y-x) dy
-- is positive-type: pairwise-translated products are integrable
-- (Integrable.comp_add_right + Integrable.bdd_mul), the translation
-- identity P(a-b) = int f(y+a) f(y+b) holds by right-invariance, the
-- finite sum interchanges with the integral, and the pointwise sum is
-- a Gram square. Plugs directly into HaarPositivityWeil's
-- PositiveType framework. Not from ONON52.tex.
import GppVerify.RiemannHypothesis.ConvolutionSquarePositive

-- Thread S2: Schur product for the Weil class — positive-type times convolution
-- square, with the composed epsilon-regularized datum as corollary
import GppVerify.RiemannHypothesis.SchurWeilClass

-- ── The Cauchy kernel is positive-type (New) ──────────────────────
-- Phase 2 Thread K (companion to the form-domain note on Yakaboylu
-- arXiv:2408.15135 Thm 5.1): on the critical line the regularized
-- matrix element eps^2/(eps^2 - (conj s + s' - 1)^2) IS the Cauchy
-- kernel eps^2/(eps^2 + (gamma' - gamma)^2), proved positive-type in
-- HaarPositivityWeil's exact PSD sense via the Bochner representation
-- eps^2/(eps^2+x^2) = eps * int_0^inf e^{-eps t} cos(xt) dt (damped-
-- cosine integral by explicit antiderivative) and a two-Gram-square
-- decomposition. Off the line: the note's Prop 2.1 (diagonal element
-- eps^2/(eps^2-4delta^2) < 0 for eps < 2delta) and eq. (7) (limiting
-- eigenvalue -> -1) as exact algebra/limits. The eps -> 0 uniformity
-- over infinite zero sets is NOT claimed: by rh_iff_weil_pairedForm_
-- nonneg it is equivalent to RH, and it stays open here.
import GppVerify.RiemannHypothesis.CauchyKernelPositive

-- ── Zitterbewegung from shadow symmetry, exact arithmetic (New) ───
-- Phase 2 Thread Z (zitterbewegung_T_boundary_FINAL.tex): the exact
-- computational content of the Zitterbewegung proposition — the
-- shadow partner's energy mu*e^{-log(E/mu)} = mu^2/E EXACTLY (a real
-- exp/log identity), the splitting E - mu^2/E vanishing on-shell at
-- mu = E, the interference frequency (E + E)/hbar = 2E/hbar (with
-- E = mc^2 the classical 2mc^2/hbar), the +-E/hbar beat frequency,
-- and the mirror-baryon bound Omega_DM/Omega_b >= 1 from the
-- T-symmetry hypotheses. The physics identifications (which state is
-- the Dirac negative-energy component, mirror baryons interacting
-- only gravitationally) are recorded as hypotheses or documentation,
-- never smuggled into the mathematics.
import GppVerify.QuantumGravity.ZitterbewegungShadow

-- ── The zeta bridge: int_0^inf t^{s-1}/sinh t = 2(1-2^{-s})Gamma(s)zeta(s) (New)
-- Phase 2 Thread S (kinematic_block_v11 Prop. zetabridge +
-- haar_qg_paper_v2151 first Plancherel moment M_1 = 1/8): the Riemann
-- zeta function is the Mellin transform of the 1/sinh thermal kernel,
-- through the odd Dirichlet factor (1-2^{-s}) -- kernel-checked for
-- every real s > 1 with zeta in Dirichlet-series form, replacing the
-- papers' 29-digit numerics. PlanckIntegral's argument one level of
-- generality up: residue expansion, real-exponent Gamma term
-- integrals, odd/even Dirichlet split (tsum_even_add_odd), summable
-- interchange. Exact corollaries: int t/sinh t = pi^2/4 (= M_1 = 1/8
-- in pi-free form) and int t^3/sinh t = pi^4/8.
import GppVerify.QuantumGravity.SinhZetaBridge

-- ── The Weil support ladder (New) ─────────────────────────────────
-- Thread L (Connes-Consani arXiv:2106.01715 sec 2.2): the prime side
-- of the Weil functional, built on Mathlib's von Mangoldt function,
-- truncates EXACTLY on supported test classes -- support doubling for
-- convolution squares (triangle inequality), term vanishing beyond
-- log n > L, full = finite truncation for L < log(N+1), and rung 0:
-- below log 2 the entire prime side vanishes and the Weil form IS its
-- archimedean part. Rung-0 archimedean positivity (Connes-Consani's
-- analytic theorem) is carried as a NAMED HYPOTHESIS, never proved.
-- Plus the eps-dictionary: int e^{-eps|u|} cos(xu) du = 2eps/(eps^2+x^2)
-- (integral_comp_abs + Thread K's damped cosine) -- the Yakaboylu
-- cutoff and the Cauchy kernel are Fourier duals; the eps -> 0 and
-- L -> infty uniformity questions are one open question (= RH via
-- rh_iff_weil_pairedForm_nonneg), not claimed.
import GppVerify.RiemannHypothesis.WeilSupportLadder

-- ── The prime-Archimedean heat trace: elementary layer (New)
-- Thread HT, from arithmetic_principal_series_RH_program34.tex (the BPY
-- prime-Archimedean spectral program). That paper reformulates RH as
-- "the completed heat trace K(t) is completely monotone on (0,inf)".
-- Formalized here: CompletelyMonotone (absent from Mathlib at the pin),
-- the single heat mode e^{-at} is completely monotone, the Laplace
-- bookkeeping 1/(u+1+gamma^2) = int_0^inf e^{-(1+u)t}e^{-gamma^2 t} dt
-- used in the paper's proof, subordination at x = 0, and the bridge
-- primeSide_heatGaussian showing the paper's arithmetic sum IS Thread L's
-- prime side at an even test function (so the ladder truncation lemmas
-- apply verbatim). NOT claimed: general-x subordination (a K_{1/2} Bessel
-- evaluation absent from Mathlib), Bernstein's theorem, or the criterion
-- itself. Nothing here proves or assumes RH.
import GppVerify.RiemannHypothesis.HeatTraceCriterion

-- ── The off-line quartet: exact contribution + transport seed (New)
-- Thread Q (entanglement/shadow-positivity memo secs 3, 4.3, 6.1):
-- the functional-equation quartet of a hypothetical off-line zero
-- rho = 1/2 + delta + i gamma contributes EXACTLY
-- 4 e^{-C(gamma^2-delta^2)} cos(2 C gamma delta) to the Gaussian-paired
-- explicit formula -- an identity in C, vanishing imaginary part
-- included -- with the sign flip provably in the oscillatory cross-
-- term (negative iff cos < 0) and the envelope amplified by
-- e^{+C delta^2} >= 1. Plus: positivity transports along ANY additive
-- group hom (the R-factor seed of the memo's idele transport question
-- -- the idele-level statement stays open: not in Mathlib), and the
-- Cesaro/Abel state is shadow-positive in finite-Gram form (wrapper
-- over PR #61's proved positivity). NOT claimed: anything about the
-- (now-retired) arithmetic_admissibility axiom or the positivity hypothesis.
import GppVerify.RiemannHypothesis.QuartetPerturbation

-- ── The pseudo-isothermal halo pair (New) ─────────────────────────
-- Thread H (ONON5213 Dark Matter chapter): the boxed halo profile
-- rho_DM(r) = rho_0/(1+(r/r_c)^2) and the holographic surface density
-- Sigma(b) = pi rho_0 r_c^2/sqrt(b^2+r_c^2) are an exact Abel-transform
-- pair, both directions kernel-checked as improper integrals via
-- explicit antiderivatives (arctan for the forward projection -- the
-- Cauchy-kernel soul again -- and an algebraic one for the inversion).
-- The rotation-curve profile is a theorem pair, not a calculation.
-- NOT claimed: the general Abel inversion/uniqueness theorem (Hankel
-- duality) and the chapter's Haar/physics normalization inputs.
import GppVerify.Cosmology.AbelHaloPair

-- ── Thread E: the Euler-sum capstone (New) ────────────────────────
-- M2 = zeta(4)/pi^4 = 1/90 (haar_qg_paper_v2151.tex base case L=2), via
-- the symmetric double-sum decomposition 2*sum_{m<=n} 1/(m^2 n^2) =
-- zeta(2)^2 + zeta(4) -- pure NxN tsum bookkeeping (product tsum,
-- Equiv-based reflection symmetry sum_{m<n}=sum_{m>n}, disjoint-union
-- splitting). Euler's second sum (sum H_n/n^3 = (5/4)zeta(4)) is NOT
-- formalized: the summand isn't symmetric under swap, so the same
-- reflection trick doesn't apply and Mathlib has no multiple-zeta-value
-- library -- named honestly as an open gap, not faked.
import GppVerify.NumberTheory.EulerSumCapstone

-- ── The idele group of Q, first steps (New) ───────────────────────
-- Not paper-sourced. Builds on Mathlib's NumberField.AdeleRing (added
-- since the many "idele class groups not in Mathlib" notes elsewhere in
-- this repo were written): Units of the adele ring gives the idele
-- group for free, the diagonal embedding Q^x -> (adele ring)^x is
-- proved injective via Units.map_injective + the adele ring's own
-- algebraMap_injective, and it is a topological group for free via
-- Mathlib's generic Units-of-a-topological-monoid instances. Honest
-- current wall for the next step (local compactness): needs
-- compactness of the local unit groups, and no bridge was found in
-- this session between Mathlib's proven CompactSpace (PadicInt p) and
-- the general adicCompletionIntegers used by FiniteAdeleRing -- named
-- explicitly in the file rather than glossed over. Discreteness,
-- class-number finiteness, Haar measure, and Meyer's construction
-- remain open beyond that.
import GppVerify.RiemannHypothesis.IdeleGroup

-- ── Li's criterion: entire Xi function and its first coefficient (New) ─
-- Task #75. Defines the entire completed Riemann Xi function riemannXi
-- via Mathlib's already-entire completedRiemannZeta0 (avoiding pole
-- bookkeeping around Lambda's poles at s=0,1), proves it entire, and
-- computes xi'(1) in exact closed form: the double zero of s(s-1) at
-- s=1 annihilates every product-rule term involving the unknown
-- derivative completedRiemannZeta0'(1), leaving xi'(1) =
-- (1/2)*completedRiemannZeta0(1). Combined with xi(1)=1/2 and Mathlib's
-- completedRiemannZeta0_one, this gives Li's lambda_1 in exact closed
-- form, matching the classical value ~0.0230957 (Li 1997). Also proves
-- (New) the unconditional positivity of lambda_1: gamma > log(4*pi)-2,
-- via a tangent-line bound log(pi) <= pi/e combined with Mathlib's
-- decimal bounds on pi, e, log 2, and the exact rational value of the
-- 63rd harmonic number (n+1=64=2^6 chosen so the subtracted log term is
-- an exact multiple of log 2), transported to gamma via
-- eulerMascheroniSeq_lt_eulerMascheroniConstant. NOT proved: the full
-- Li <=> RH equivalence for all n (needs Hadamard factorization of xi,
-- not in Mathlib) -- named explicitly as the remaining open gap.
import GppVerify.RiemannHypothesis.LiCriterion

-- ── The Mellin transform of the Planck kernel is Gamma(s)*zeta(s) (New) ─
-- Prompted by re-reading blackbody_law_qg_dtoupin_v1.tex, which claims the
-- Riemann zeta function is the Mellin transform of a thermal (Planck-law)
-- kernel. Confirmed this is the classical, true fact (Riemann's own 1859
-- derivation route via the Jacobi theta function / Bose-Einstein kernel).
-- planckKernel(t) := 1/(e^t-1), the single-oscillator excited-state
-- partition function; proves mellin planckKernel s = Gamma(s)*zeta(s) for
-- Re(s)>1, via Mathlib's already-general hasSum_mellin machinery (sum of
-- decaying exponentials -> Gamma(s) times the associated Dirichlet
-- series), applied with the exponential rates p_i = i+1 giving exactly
-- the zeta Dirichlet series. Also proves (New) the odd-frequency variant
-- matching the black-body paper's own kernel exactly: mellin
-- oddPlanckKernel s = (1-2^{-s})*Gamma(s)*zeta(s), via an even/odd split
-- of the geometric series (HasSum.even_add_odd) applied twice. No axiom,
-- no sorry.
import GppVerify.RiemannHypothesis.BlackbodyMellinZeta

-- ONON5213.tex, Chapter 7 ("The Isomorphism"), Theorem "Perfect self-duality of
-- Gr(k,n)": the orthogonal-complement map Λ ↦ Λ^⊥ on a finite-dimensional inner
-- product space sends Gr(k,n) into Gr(n-k,n) (grassmannian_orthogonal_dim), is an
-- involution (grassmannian_orthogonal_involutive), and restricts to a self-map of
-- Gr(k,n) itself iff n = 2k (grassmannian_self_dual_iff), specialized to the
-- paper's own Gr(2,4) case (gr_two_four_self_dual). Also proves the algebraic
-- identity behind the paper's Gaussian-binomial point count of Gr(2,4) over F_q
-- (grassmannian_gaussian_binomial_two_four). No axiom, no sorry.
import GppVerify.CelestialHolography.GrassmannianSelfDuality

-- ── Thread S, Step 1: abstract Hermitian inertia core (New) ──
-- From the Anthropic/Claude Aug 2026 paper "More than two thirds of the zeros
-- of the Riemann zeta function are simple and on the critical line": its
-- unconditional mechanism replaces RH (which read the zero side termwise as a
-- positive sum) with Sylvester's law of inertia on a finite compression of
-- Weil's Hermitian form + a rank-trace inequality. This file is the abstract,
-- finite-dimensional, zero-free, analysis-free base layer only: nPos/nNeg/nZero
-- eigenvalue counts for a Hermitian matrix and the inertia_sum identity
-- nPos+nNeg+nZero = card n. Independent GPPVerify-native development against
-- this repo's OWN pin (c44e0c8), not a port of Anthropic's zeta-23-lean repo
-- (different, newer Mathlib pin). See GppVerify/ThreadS/SOURCES.md and
-- MATHLIB_RECON.md. NOT done: the subspace-dimension bounds, congruence
-- invariance, and the actual rank-trace inequality (the load-bearing lemma) --
-- this file is the foundation only, not the payload. No axiom, no sorry.
import GppVerify.ThreadS.SignatureInertia

-- ── Thread Weil-Parity: exact Archimedean renormalization tail (New) ────
-- From arithmetic_principal_series_RH_program34.tex, "The exact semilocal Weil form"
-- (~line 6414): the finite prime-Archimedean Gram matrix Q_{lambda,N} construction.
-- A numerical checkpoint this session (lean_results 02a84cc3.../079ca52f...) found and
-- fixed a truncation bug in W_R^sharp's integral (omitted tail beyond the support
-- cutoff), used but never proved in closed form. archimedean_diagonal_tail below IS
-- that closed form: -2*int_c^infty du/(u^2-1) = -log((c+1)/(c-1)), proved from
-- Mathlib's elementary calculus + FTC-2-on-(a,infty) machinery. Says nothing about the
-- actual eigenvalues of Q_{lambda,N} or any Weil-positivity/parity-ratio claim --
-- those depend on an operator-comparison theorem that does not yet exist even on
-- paper (see the checkpoint for the precise gap). No axiom, no sorry, no RH claim.
import GppVerify.ThreadWeilParity.ArchimedeanTail

-- ── Thread Weil-Parity: cross-resolvent determinant identity + parity crossing (New) ──
-- From public.formalization_queue (Supabase), section "A. WEIL-PARITY CORE". Two abstract,
-- fully unconditional finite-dimensional theorems: cross_resolvent_det_identity (queue item
-- 3ebed50a, the flagship "start here" item -- coordinate/Schur-complement form of the
-- parity displacement determinant identity) and parity_crossing_obstruction (queue item
-- 0cf9aebf -- rank-one Sylvester displacement forces disjoint parity spectra unless a
-- cross-overlap vanishes). Both proved directly, no pre-verification shortcut, iterating
-- against the Lean compiler; both kernel-clean, no axiom, no sorry.
-- IMPORTANT: research_notes 35a9efdc records a stress-test counterexample showing the
-- actual arithmetic CCM matrix does NOT have a universally positive commuting metric --
-- so the positivity hypotheses these theorems need are not established for the real
-- object. These are real, unconditional abstract implications; they are NOT steps toward
-- RH by themselves, and nothing here claims otherwise.
import GppVerify.ThreadWeilParity.CrossResolvent

-- ── Thread Weil-Parity: odd eigenpair canonical lift (New) ──────────────────────────
-- formalization_queue item c0c96bbc: "Odd eigenpair canonical lift and Schur-Rayleigh
-- defect identity". Builds directly on CrossResolvent.lean's block structure. Three
-- theorems, all PROVED, kernel-clean, no axiom, no sorry:
--   - odd_eigenpair_defect_step1: (E-lamI)x1 = s*b from the Sylvester relation applied
--     at an Aminus-eigenvector.
--   - odd_eigenpair_defect_step2: x1 = s*(E-lamI)^-1 b when E-lamI is invertible.
--   - odd_eigenpair_canonical_lift: the canonical lift x=s*(-1,(E-lamI)^-1 b) satisfies
--     eta*x=0 and (Aplus-lamI)x=-s*phi(lam)*e0. IMPORTANT: this theorem's hw1 hypothesis
--     (eta1*(E-lamI)^-1 b = 1) is not a free assumption -- it is a solvability condition
--     that steps 1+2 force whenever s != 0, documented in the file header rather than
--     silently smuggled in.
-- Same standing warning as CrossResolvent.lean: abstract, unconditional facts about any
-- operator pencil satisfying the stated relations; no claim about the real CCM matrix.
import GppVerify.ThreadWeilParity.OddEigenpairLift

-- ── Thread QG-Blackbody: Stefan-Boltzmann family, Gamma-modulus, all-loop finiteness (New) ──
-- From haar_qg_paper_v215.tex, kinematic_block_v1.tex and blackbody_law_qg_dtoupin_v1.tex
-- (companions: verify_qg_measure.py, verify_qg_kinematics.py, verify_blackbody_capstone.py).
-- Generalizes the pre-existing SinhZetaBridge.lean/PlanckIntegral.lean threads (which already
-- covered M_1=1/8 and M_2=1/90 from earlier drafts of these same papers) to three new results:
--   - stefan_boltzmann_family: m_s = pi^-(s+1)(1-2^-(s+1))Gamma(s+1)zeta(s+1) for ALL real
--     s > 0 (T7 of verify_blackbody_capstone.py), not just the sampled s=1,2,3.
--   - gamma_one_add_mul_gamma_one_sub: Gamma(1+i*lam)*Gamma(1-i*lam) = pi*lam/sinh(pi*lam)
--     exactly, via Euler's reflection formula (T2/T4 of the capstone script).
--   - GppAllLoopFiniteness.finiteness: 0 < M_L <= (1/8)^L for EVERY loop order L (paper's
--     thm:finiteness, its central new claim) -- proved by induction on a recursively-defined
--     chain kernel (Fubini's own iterated-integral expansion of the paper's R_{>0}^L integral,
--     peeling off one loop variable at a time) carried entirely in ENNReal/lintegral so Tonelli
--     and monotonicity are unconditional, with no integrability side-conditions threaded by
--     hand anywhere in the induction.
-- All three kernel-clean, no axiom, no sorry. Remaining unformalized from this upload: the
-- rationality/PSLQ program beyond M_1,M_2 (M_3=1/16 etc.), the entire kinematic-block/conical-
-- Legendre-function program, and most of the blackbody capstone's structural theorems
-- (T1,T3,T5,T6,T13,T14) -- honestly scoped as future work, not claimed here.
import GppVerify.QuantumGravity.StefanBoltzmannFamily
import GppVerify.QuantumGravity.GammaModulusIdentity
import GppVerify.QuantumGravity.AllLoopFiniteness

-- ── Thread QG-Blackbody, round 2: kinematic-block zeta bridge + Weierstrass product (New) ──
-- From kinematic_block_v1.tex Proposition prop:zetabridge(a) and blackbody_law_qg_dtoupin_v1.tex
-- Test T4 (verify_blackbody_capstone.py). Both kernel-clean, no axiom, no sorry:
--   - GppKinematicBlock.zeta_bridge_kappa: restates SinhZetaBridge.sinh_mellin_zeta at the
--     kinematic-block paper's own kernel normalization kappa(t)=(2 sinh t)^-1, giving
--     (1-2^-s)Gamma(s)zeta(s) directly (the leading factor of 2 cancels the 1/2).
--   - GppSinhWeierstrass.tendsto_prod_one_add_sq_div: the Weierstrass product
--     sinh(pi*lam) = pi*lam * prod_n(1+lam^2/n^2), proved as a genuine infinite product
--     (Tendsto of partial products, for every real lam) rather than the paper's own
--     truncated-at-N=2000-with-Hurwitz-remainder numerical bound -- derived from Mathlib's
--     Complex.tendsto_euler_sin_prod (Euler's product for sin) via the substitution z=i*lam.
-- Proposition 7.1(b)'s analytic continuation to Re s > -1, and Theorem 6.1 (First Moment,
-- needs a digamma function -- Mathlib v4.19.0 has NONE, grepped, zero hits for
-- digamma/polygamma anywhere in the tree) and Theorems 2.1/3.1/4.1/4.4 (conical reduction,
-- shadow=Legendre-degree symmetry, Mehler-Fock, Temperedness -- need Legendre/conical
-- special functions, also entirely absent from Mathlib) remain open; see
-- docs/FORMALIZATION_PLAN.md for the precise boundary of each gap.
import GppVerify.QuantumGravity.KinematicZetaBridge
import GppVerify.QuantumGravity.SinhWeierstrassProduct

-- ── Thread Loops-from-Cuts, Planck form (New) ──
-- Daniel has designated `Loops_from_Cuts_in_Celestial_Holography.tex`,
-- `Principal_Series_Kinematic_Blocks.tex`, `Spectral_Weight_from_Principal_Series.tex`, and
-- `Modular_Thermality_of_the_Celestial_Spectral_Weight.tex` as the canonical replacements for
-- the earlier haar_qg/kinematic_block/blackbody paper series (the "loop", "measure", "block",
-- and "blackbody" papers). Formalizes the Planck-form theorem stated identically in the last
-- two of these: P(lambda) = 2*pi*lambda*(n_B(pi*lambda) - n_B(2*pi*lambda)), the Bose-
-- difference representation of the Plancherel weight. Pure elementary hyperbolic-function
-- algebra, no Mathlib gaps.
import GppVerify.QuantumGravity.PlanckForm

-- ── Thread Loops-from-Cuts, Matsubara pole residues (New) ──
-- Modular_Thermality_of_the_Celestial_Spectral_Weight.tex, Proposition "Equivalent
-- descriptions" item (iv): the complex continuation of P(lambda) has simple poles at
-- lambda=in, n a nonzero integer, with residue i*(-1)^n*n. Formalized as the operational
-- limit lim_{eps->0} eps*P(in+eps) (Res is not a named Mathlib operator; no general
-- residue-calculus API exists at this pinned commit), matching the paper's own script.
import GppVerify.QuantumGravity.MatsubaraPoles

-- ── Thread Loops-from-Cuts, log of the sinh Weierstrass product (New) ──
-- The first half of the cumulant-law chain FORMALIZATION_PLAN.md flagged as the natural
-- next target once SinhWeierstrassProduct.lean landed: HasSum (fun n => log(1+lambda^2/
-- (n+1)^2)) (log(sinh(pi*lambda)/(pi*lambda))), an unconditional infinite sum of logs (not
-- a numerical truncation), from continuity of log at the (proved positive) Weierstrass-
-- product limit. The second half -- expanding each log(1+x) into its own power series and
-- swapping the resulting double sum to land on the paper's zeta(2k) closed form -- is not
-- attempted here, per the file's own scoped honest boundary. NOTE: the completion of this
-- chain (the cumulant law itself and its single-index closed form) landed independently on
-- main via a different, more direct route -- see the CumulantLaw import below rather than a
-- separate CumulantLawClosedForm.lean, which this branch's own version of turned out to be
-- fully redundant with main's GppCumulantLaw.cumulant_law and was dropped at merge time.
import GppVerify.QuantumGravity.SinhLogSeries

-- ── Thread Loops-from-Cuts, weight-shift relations (New) ──
-- Principal_Series_Kinematic_Blocks.tex, Theorem "Weight-shift relations and the resulting
-- differential equation" -- the digamma-free first half: P(z-i)=[(1+iz)/(-iz)]P(z) and
-- P(z+i)=[(1-iz)/(iz)]P(z) for the complex-analytic Gamma-product continuation of P, pure
-- consequences of Gamma(s+1)=s*Gamma(s) applied to each factor. The theorem's second half
-- (the resulting first-order ODE for P's Fourier partner, needed for thm:resolved's
-- digamma-moment identification) remains blocked on Mathlib's missing digamma function.
import GppVerify.QuantumGravity.WeightShiftRelations

-- ── Thread Loops-from-Cuts, antipodal-pairing algebraic core (New) ──
-- Loops_from_Cuts_in_Celestial_Holography.tex, Theorem "Cut geometry: antipodal pairing
-- and uniform measure" (thm:measure) -- the most important/novel link of the whole new
-- canonical loop paper. Verifies by direct vector computation (no measure theory) that the
-- paper's claimed antipodal solution z6=-z5/|z5|^2, omega5=M/(2(1+|z5|^2)),
-- omega6=M|z5|^2/(2(1+|z5|^2)) genuinely satisfies P=l5+l6 for every z5!=0, plus that the
-- null-vector parametrization q(x,y) is always null. Uniqueness of the solution and the
-- phase-space MEASURE reduction itself (needing genuine delta^4-constrained-pushforward
-- Jacobian machinery this repo has never built) remain open, precisely scoped.
import GppVerify.CelestialHolography.AntipodalPairingSolution

-- ── Thread Tree-Loop-Sewing, discovery follow-on: sign opposition (New) ──
-- From discovery/shadow_ope/sign_opposition_sweep.py's found-and-explained fact that the
-- s-channel and t-channel tied-leg sewing discontinuities Sewn_s, Sewn_t always carry
-- opposite-sign imaginary parts (39/39 structured points, 666/666 random points, zero
-- exceptions, then explained analytically). Promotes the algebraic explanation to a real
-- theorem: A(x,y)=2q(x,y).p1=-4E is an exact z-independent constant, A'(x,y)=2q(x,y).p2=
-- -4E|z|^2 is manifestly <=0, C(x,y)=2q(x,y).p4 clears to an exact sum of two squares
-- (kappa*|z-z4|^2, kappa=2E(1-cos theta)>0 for t<0), and B(x,y)=2q(x,y).(p1+p2)=
-- -4E(1+|z|^2) is unconditionally negative -- all four proved by direct `ring`/`nlinarith`
-- computation from the bare kinematics, not assumed. sign_opposition combines them into
-- the exact algebraic content of Im(Sewn_s)<0<Im(Sewn_t) on the physical branch (B''>0
-- taken as a hypothesis, since it genuinely changes sign over the sphere and is not
-- pinned down by E,theta alone). Pure real algebra and elementary geometry -- no Mellin
-- transforms, no complex analysis, no Legendre functions (still absent from Mathlib
-- v4.19.0, see the note above) -- does NOT touch or discharge ShadowPairSewing.sewing_identity.
import GppVerify.CelestialHolography.ShadowSignOpposition

-- ── Thread Loops-from-Cuts, dispersion-kernel Mellin identity, item 2/3 (New) ──
-- Loops_from_Cuts_in_Celestial_Holography.tex's dispersion-relation reconstruction
-- (thm:disp, thm:celdisp) rests on the Mellin kernel identity int_0^infty S^(sigma-1)/(s'+S)
-- dS = s'^(sigma-1)*pi/sin(pi*sigma); substituting S=s'u reduces this to the base case
-- int_0^infty u^(sigma-1)/(1+u) du = pi/sin(pi*sigma), a "second Euler Beta integral" on
-- (0,infty) confirmed absent from Mathlib v4.19.0 by direct grep (only the (0,1) form,
-- Complex.betaIntegral, exists). Proves the Beta-reflection integral this ultimately rests
-- on, in real intervalIntegral form: int x in (0:R)..1, x^(s-1)*(1-x)^(-s) = pi/sin(pi*s)
-- for 0<s<1 -- obtained by unfolding Complex.betaIntegral s (1-s), evaluating it via
-- Complex.Gamma_mul_Gamma_eq_betaIntegral (Gamma(u)Gamma(v)=Gamma(u+v)*B(u,v), u+v=1 so
-- Gamma(u+v)=Gamma(1)=1) combined with the reflection formula
-- Complex.Gamma_mul_Gamma_one_sub, then casting the complex identity down to a real one via
-- Complex.ofReal_cpow (valid uniformly on x in [0,1], both endpoints included, since
-- Mathlib's 0^y convention for rpow/cpow already agree there) and
-- intervalIntegral.integral_ofReal. Does NOT carry the substitution x=t/(1+t) (mapping
-- (0,1)<->(0,infty)) needed to reach the paper's actual (0,infty) dispersion kernel -- that
-- needs MeasureTheory.integral_image_eq_integral_abs_deriv_smul with a fresh Ioo-0-1-to-Ioi-0
-- diffeomorphism, genuinely new infrastructure this repo has never built (algebra checked by
-- hand, not yet coded), left open as the well-scoped next step.
import GppVerify.CelestialHolography.DispersionKernelMellin

-- ── Thread Loops-from-Cuts, logistic Fourier pair, item 3/3 (New) ──
-- Modular_Thermality_of_the_Celestial_Spectral_Weight.tex /
-- Spectral_Weight_from_Principal_Series.tex: P(lambda) = int e^(i*lambda*x)/(4cosh^2(x/2)) dx,
-- the Fourier-transform characterization of the already-proved closed hyperbolic form
-- pi*lambda/sinh(pi*lambda) (PlanckForm.lean, MatsubaraPoles.lean). The third and lowest-
-- ranked of the three items Daniel asked to be attempted "in order of importance or
-- novelty." Genuinely attempted: re-confirmed by direct grep that Mathlib v4.19.0 has zero
-- sech/cosh-family closed-form Fourier transforms (only the Gaussian), no Poisson-kernel
-- 1/(1+x^2) closed form, and no residue-calculus API (the textbook proof needs a residue sum
-- over sech^2's double poles at x=i*pi*(2k+1)). Parked as a True-stub per this repo's own
-- documented convention, naming the precise gap -- not an axiom, not a sorry.
import GppVerify.QuantumGravity.LogisticFourierPair

-- ── Thread QG-Blackbody, round 3: the cumulant law (New) ──────────────────────────────────
-- From blackbody_law_qg_dtoupin_v1.tex Test T5 ("cumulants are even zeta values"). Unlocked
-- by round 2's Weierstrass product: taking log of sinh(pi*lam)=pi*lam*prod(1+lam^2/n^2) turns
-- the product into a sum of logs (log_prod + Summable.hasSum_iff_tendsto_nat), each log(1+x)
-- expands via Mathlib's hasSum_pow_div_log_of_abs_lt_one, and the resulting double series in
-- (loop index j, Taylor order k) is swapped via Summable.tsum_comm after establishing joint
-- summability from an explicit product majorant (Summable.mul_of_nonneg). Result:
-- GppCumulantLaw.cumulant_law: -log(P(lam)) = sum_k (-1)^k * zeta(2(k+1)) * lam^(2(k+1))/(k+1)
-- for |lam|<1, matching the paper's log P(lam) = -sum_{k>=1}(-1)^(k+1)zeta(2k)lam^(2k)/k
-- exactly (k zero-indexed here as k+1 >= 1). Kernel-clean, no axiom, no sorry.
import GppVerify.QuantumGravity.CumulantLaw

-- ── Thread QG-Blackbody, round 4: Planck form and the reciprocal Weierstrass product ──────
-- From updated companion papers ("The Spectral Weight pi*lam/sinh(pi*lam)" and "Modular
-- Thermality of the Celestial Spectral Weight"). GppSpectralWeight.planck_form: for lam>0,
-- P(lam) = 2*pi*lam*(bose(pi*lam) - bose(2*pi*lam)), a genuine Planck-form identity with the
-- two Bose zero-point terms cancelling exactly. GppSpectralWeight.one_div_P_tendsto_tprod:
-- 1/P(lam) is the Weierstrass product prod(1+lam^2/n^2), an immediate corollary of round 2's
-- Weierstrass product for sinh. Also corrected this round: P was mislabeled "the Plancherel
-- spectral weight" and M_L a "Plancherel loop measure" in this file's earlier comments and
-- the blueprint -- both wrong (the SL(2,C) Plancherel density for the scalar principal
-- series grows like lam^2, not P). P is the two-particle massless phase-space weight of a
-- celestial unitarity cut; no Lean statement or proof changed, only prose. Kernel-clean, no
-- axiom, no sorry.
import GppVerify.QuantumGravity.SpectralWeightIdentities

-- ── Digamma via Mathlib's Gamma calculus (task #9) ─────────────────────────────────────────
-- Earlier rounds' grep for the NAME digamma/polygamma in Mathlib v4.19.0 (zero hits) was the
-- wrong question: Mathlib.NumberTheory.Harmonic.GammaDeriv already computes deriv Real.Gamma
-- in closed form at 1 and 1/2 (Bohr-Mollerup convexity, Legendre duplication formula).
-- GppDigamma.digamma := deriv Gamma / Gamma makes psi(1)=-gamma, psi(1/2)=-gamma-2log2, the
-- values at all positive integers, and the functional equation psi(x+1)=psi(x)+1/x immediate
-- corollaries. Real-argument only -- the complex digamma along Re(s)=1/2 that
-- kinematic_block_v1.tex's First Moment Theorem needs is a further, separate extension, not
-- attempted here. Kernel-clean, no axiom, no sorry.
import GppVerify.QuantumGravity.Digamma

-- ── Positive Gamma--Plancherel defect (v34, Theorem 62.1) ────────────────────────────────
-- Exact identity between the real-place density and the existing celestial weight
-- P(lam)=pi*lam/sinh(pi*lam); pointwise and integrated finite-Gram positivity; automatic
-- positivity for compact truncations.  On the infinite lattice a=2m, b=2n, q>0, the
-- digamma recurrence plus a finite geometric sum proves the FULL equality between the
-- four-term Gamma defect, the (0,infinity) integral, and a positive finite resolvent sum,
-- including strict scalar positivity and finite Gram positivity.  The arbitrary-real
-- digamma integral representation remains open and is not claimed.  No RH implication.
import GppVerify.RiemannHypothesis.GammaPlancherelDefect

-- ── Local-field shadow kernels (new research front, 2026-08-20) ────────────────────────────
-- From "Local-field shadow kernels, celestial unitarity, and the adelic principal series"
-- (Toupin, 2026). Two unconditional structural facts about the Archimedean shadow kernel
-- K_{infty,d}(a)=Gamma(a)Gamma(d-a)/Gamma(d) that do not depend on any claim about RH, the
-- celestial/automorphic bridge, or the paper's open research program: shadow reflection
-- K(a)=K(d-a), and positivity on the principal series a=d/2+it (Hermitian conjugation via
-- Complex.Gamma_conj). Plus the diagonal conformal lift D(s)=(s,s), Delta(D(s))=2s, and its
-- exact compatibility with the 1D/2D shadow involutions. See
-- discovery/local_field_shadow/local_shadow_kernel_notes.md for the full honest boundary --
-- the non-Archimedean kernel, the Knapp-Stein local factorization problem, the Eisenstein
-- scattering coefficient, and the Cutkosky/Rankin-Selberg bridge are NOT formalized: genuine
-- open research targets, not bookkeeping. Both files kernel-clean, no axiom, no sorry.
import GppVerify.QuantumGravity.LocalShadowKernel
import GppVerify.QuantumGravity.DiagonalConformalLift

-- ── §9 resolution (2026-08-22): the naive common-local-factor conjecture fails, informatively ──
-- The physical positive kernel and the standard Weyl/Gindikin-Karpelevich intertwiner are
-- distinct canonical objects on the same rank-one principal series, not a single factor
-- a_v(s) split two ways. GammaR/GammaC/archWeylCoeff added to LocalShadowKernel.lean:
-- GammaC_eq_GammaR_mul_GammaR_succ (Legendre duplication for the Archimedean factors),
-- archKernel_two_eq_GammaC_product and archKernel_two_eq_GammaR_sectors (the celestial d=2
-- cut decomposes exactly into two shadow-paired real Archimedean Gamma sectors
-- (Gamma_R(Delta),Gamma_R(2-Delta)) and (Gamma_R(Delta+1),Gamma_R(3-Delta))). archWeylCoeff is
-- recorded for contrast only -- no identity relating it to archKernel is claimed or proved.
-- GlobalEisensteinCoefficient.lean: the global Eisenstein coefficient phi(Delta)=Lambda(Delta-1)/
-- Lambda(Delta) rewrites exactly as Lambda(2-Delta)/Lambda(Delta) (the celestial shadow
-- arguments) via Mathlib's own completedRiemannZeta functional equation, with reflection
-- phi(2-Delta)*phi(Delta)=1. NOT evidence toward RH -- Eisenstein scattering already contains
-- zeta(s) without proving anything about its zeros. Finite-place distinction (Gindikin-
-- Karpelevich ratio vs the derived positive kernel) and unit-modulus-on-critical-line are
-- documented/verified numerically only in discovery/local_field_shadow/ -- the former has no
-- Mathlib p-adic Haar infrastructure to formalize against, the latter needs Lambda's
-- conjugation symmetry (not directly in Mathlib). Cutkosky<->Rankin-Selberg/unitary-
-- intertwiner identification remains explicitly OPEN (task #13) -- no axiom added for it.
-- All new theorems kernel-clean, no axiom, no sorry.
import GppVerify.QuantumGravity.GlobalEisensteinCoefficient

-- ── The golden ratio as the minimal hyperbolic sector of PSL2(Z) (2026-08-22) ──────────────
-- From a research-front update: F = T∘J (unit translation after inversion), F(x)=1+1/x, has
-- unique positive fixed point phi. Represented projectively, M=!![1,1;1,0], A:=M^2=!![2,1;1,1]
-- is the MINIMAL-TRACE hyperbolic element of SL2(Z) (integrality forces |tr|>=3 once |tr|>2;
-- A attains it). Discriminant 5, eigenvalues phi^{+-2}, Mobius fixed points phi and -phi^-1.
-- Independently, the already-scoped finite-place shadow kernel K_{q,1}(s) evaluated at the
-- INDEPENDENTLY-selected discriminant q=5 and principal-series center s=1/2 equals exactly
-- phi^2 -- golden_convergence connects the two routes. Reuses Mathlib's Data.Real.GoldenRatio
-- throughout rather than redefining. Physical-sector identification explicitly NOT claimed --
-- see the file's own doc comment for the precise semantic boundary. All 14 theorems
-- kernel-clean, no axiom, no sorry.
import GppVerify.NumberTheory.GoldenRatioHyperbolicSector

-- ── Local shadow kernels and the finite-prime Weil kernel (2026-08-22/23) ──────────────────
-- From a research-front directive: celestial Cutkosky positivity -> local shadow kernels ->
-- finite-prime Weil kernel -> Casimir compression -> global Weil positivity -> RH. The final
-- logical step (finite Weil paired-form positivity on all nontrivial zeros <-> RH) is already
-- proved unconditionally in WeilPositivityCriterion.lean (rh_iff_weil_pairedForm_nonneg) --
-- an ABSTRACT pairing over finite subsets of the actual (unknown) zero set, NOT the classical
-- Weil explicit-formula prime-sum quadratic form built here; bridging the two needs the
-- classical explicit formula itself (substantial, separate, not attempted). Kp_pos (the
-- finite-place shadow kernel K_p(t) is a Poisson-kernel value, hence positive, for every
-- prime p>1) and H_nonneg (the Casimir-weighted Archimedean kernel H(t)=(t^2+1/4)*C(t), C the
-- already-derived celestial cut, is nonnegative for every real t) proved unconditionally.
-- CORRECTED central research finding (self-correction of an earlier-merged error, see the
-- file's module doc and discovery/cutkosky_weil/notes.md): the first pass tested the WRONG
-- positivity notion (a Toeplitz matrix of Fourier COEFFICIENTS, indices=frequencies -- found
-- indefinite) instead of the actual kernel-positivity question (a Gram matrix of POINT
-- EVALUATIONS (K_p-1)(theta_j-theta_k) -- found positive semidefinite, as Bochner/Herglotz
-- predicts, since convolution by K_p-1 is diagonal with nonneg eigenvalues). Proved rigorously
-- via a layered finite Fourier/Gram-square development (gram_square_freq -> gram_square_freqSum
-- -> gram_square_freqSum_nonneg -> KrN0/KrN0_gram_nonneg), each layer independently fast
-- (<4s) after an earlier monolithic HasSum-based attempt repeatedly hit elaboration timeouts
-- even at 4M heartbeats (bisected and diagnosed as a proof-engineering issue, not mathematical
-- -- see the module doc's "Proof-engineering note"). KrN0_gram_nonneg is the finite-truncation
-- milestone: for every truncation N, Sum_jk c_j-bar*c_k*K^0_{r,N}(theta_j-theta_k) >= 0.
-- FOURTH PASS (same session, following review): completed both items the third pass had
-- deferred. (1) Removable singularity: tendsto_cutKernel_zero proves the genuine limit
-- C(0)=1/(8*pi) (from sinh's derivative at 0, not asserted); Hext/Hext_zero/Hext_nonneg give
-- the continuous extension with H(0)=1/(32*pi) replacing Lean's junk 0/0=0. (2) The N->infinity
-- passage: tendsto_Icc_atTop (cofinality of Icc(-N,N) in Finset.atTop) + summable_KrClosed_summand
-- (Summable via geometric-tail comparison, Summable.of_nat_of_neg -- much cheaper than tracking
-- HasSum values through Int.rec, which is what timed out before) + tsum_KrClosed_summand_eq
-- (identifies the tsum's value as K_r(theta)-1, via the two one-sided geometric series) +
-- tendsto_KrN0 (KrN0 -> K_r-1 as N->infinity) + KrClosed_minus_one_positiveType (positivity
-- passes to the limit via ge_of_tendsto) = the genuine, untruncated
-- GppHaarPositivityWeil.PositiveType (K_r - 1), unconditional. 16 theorems total in this file,
-- all kernel-clean (Lean built-ins only), no axiom, no sorry.
-- FIFTH PASS (same session, following a further review directive): item 1 of the wider
-- program -- the ACTUAL operator statement, not the finite Fourier identity again. Built
-- Ell2Z := lp(fun _:Z=>C) 2 (the natural Fourier-coefficient model, unitarily dual to the
-- circle: convolution by a kernel <-> diagonal multiplication by its Fourier coefficients).
-- mulOpCLM w hw : Ell2Z ->L[C] Ell2Z is the bounded diagonal operator for a weight bounded by
-- 1; C_Kr := mulOpCLM(KrWeight r) (symbol r^|n|), P_0 := mulOpCLM P0Weight (symbol 0 at n=0,
-- 1 elsewhere -- projection deleting the vacuum mode), C_{Kr-1} := mulOpCLM(KrMinusOneWeight r).
-- vacuum_compression_operator_identity proves C_{Kr-1} = P_0 * C_Kr * P_0 as genuine bounded
-- ContinuousLinearMap composition (not a finite Gram identity), via composition-multiplies-
-- symbols (mulOpLin_comp) reducing to the pointwise fact P_0(n)*Kr(n)*P_0(n)=(Kr-1)(n) for
-- every n. vacuum_compressed_operator_positive derives positivity of the compressed operator
-- as a direct corollary of a general fact (mulOpCLM_inner_re_nonneg: nonneg-real-part diagonal
-- weight => positive semidefinite operator) applied to Kr-1's already-known eigenvalue signs
-- (0 at n=0, r^|n|>=0 elsewhere) -- no new analytic content, exactly "as a corollary" per the
-- directive. 8 new theorems, kernel-clean, no axiom, no sorry. This CLOSES item 1.
-- Also newly established (checked by hand, precise, not yet in Lean): the finite-prime Weil
-- kernel target named by the directive ("in the normalization used by rh_iff_weil_pairedForm_
-- nonneg") does not exist as literally stated -- that theorem's pairedForm is a zero-indexed
-- reflection pairing (Yakaboylu/Bombieri-Lagarias style) with NO prime, Mellin, or Haar-measure
-- content to match against; already flagged in this file's own module doc (see above) before
-- this pass began. The correct classical target is instead HaarPositivityWeil.lean's
-- weil_criterion (D_k = Sum_rho Omega-hat(rho) + local terms), which remains a full True-stub,
-- honestly blocked on Tate's thesis + idele class groups (neither in Mathlib) for its ADELIC
-- form. But the classical ELEMENTARY (non-adelic) explicit formula's finite-prime local term
-- has a clean, checked closed form: with zeta_p(s):=(1-p^{-s})^{-1} the local Euler factor,
-- Wp(p,t) = 2*Re(-zeta_p'/zeta_p(1/2+it)) exactly, via -zeta_p'/zeta_p(s) = log(p)*Sum_{k>=1}
-- p^{-ks} (standard log-derivative of the Euler factor) and Kp_eq_KrClosed +
-- tsum_KrClosed_summand_eq already proved above. This is the honest next Lean target for
-- items 2-3 of the directive; items 4 (Mellin/adelic bridge) and 6 (global assembly against
-- rh_iff_weil_pairedForm_nonneg specifically) do not apply as stated, since that theorem's
-- hypothesis carries no prime-side data to assemble in the first place -- see
-- docs/FORMALIZATION_PLAN.md and discovery/cutkosky_weil/notes.md for the full account.
import GppVerify.RiemannHypothesis.CutkoskyWeilBridge

-- ── Euler-Factor Log-Derivative (New, 2026-08-23, sixth+seventh Cutkosky-Weil passes) ──
-- zeta_p's genuine log-derivative -zeta_p'/zeta_p, from an actual HasDerivAt
-- computation, PLUS (seventh pass) the closed connection to Wp itself:
-- Wp p t = 2*Re(minusLogDerivZetaP p (1/2+it)), genuinely proved, not just
-- checked numerically. See discovery/cutkosky_weil/notes.md.
import GppVerify.RiemannHypothesis.EulerFactorLogDeriv

-- ── Codex local prime Green and fermionic Hodge--Dirac modules ──
-- Exact prime-power Green propagation, the exterior two-state CAR factor,
-- and the singlet/doublet Dirac blocks. These remain independent of the
-- imported Weil-Semiboundedness and Suzuki-Herglotz modules below.
import GppVerify.RiemannHypothesis.PrimeGreenAmplitude
import GppVerify.RiemannHypothesis.PrimeFermionDirac
import GppVerify.RiemannHypothesis.PrimeDoubletDirac

-- ── Thread Weil-Semiboundedness (New, 2026-08-23) ──
-- formalization_queue item 1b12010b: pure order-theoretic skeleton for
-- Suzuki's localized Weil ground energy lambda_a (nesting -> antitone;
-- global bound <-> bounded-below range; antitone+unbounded -> tendsto atBot).
-- Abstract only -- does not define Q_W, the Weil quadratic form, or C_c^infty
-- test spaces. See the file's own module doc for the honest boundary.
import GppVerify.ThreadWeilSemibound.LocalizedGroundOrder

-- ── Thread Weil-Parity, further items (New, 2026-08-23) ──
-- formalization_queue items 0182d9cf (no-crossing continuation, pure
-- topology/IVT) and 5e10a4f0 (cross-resolvent positivity below the even
-- ground forces the odd ground above it, pure algebra). Abstract cores
-- only -- neither defines Hermitian matrices or their eigenvalues; see
-- each file's own module doc for the honest boundary.
import GppVerify.ThreadWeilParity.GroundContinuation
import GppVerify.ThreadWeilParity.CrossResolventGroundOrdering

-- ── Thread Weil-Parity, strict interlacing IVT core (New, 2026-08-23) ──
-- formalization_queue item 9cc1e2f8, the item CLAUDE.md/FORMALIZATION_PLAN.md
-- had already flagged as the natural next target (needs real IVT/monotonicity,
-- not just block-matrix algebra). Abstract core only -- see the file's own
-- module doc for the honest boundary (does not yet connect to the concrete
-- f = sum c_j/(alpha_j - z) construction).
import GppVerify.ThreadWeilParity.StrictParityInterlacing

-- ── Thread Weil-Parity, cross-heat positivity (New, 2026-08-23) ──
-- formalization_queue item 68566b83: the Laplace-transform positivity core
-- (integral of an everywhere-positive integrable function over [0,infty) is
-- strictly positive). Does not define the matrix exponential or resolvent,
-- or prove the Laplace-resolvent identity itself; see the file's module doc.
import GppVerify.ThreadWeilParity.CrossHeatPositivity

-- ── Thread Weil-Parity, removable-singularity limit core (New, 2026-08-23) ──
-- formalization_queue item 4d97d8eb: a bounded numerator over a denominator
-- whose norm blows up tends to zero -- the reusable real-analysis fact behind
-- "qStar(x_i)=q_i" for the barycentric Pick interpolant. Does not construct
-- the Pick matrix or A/B/qStar themselves; see the file's module doc.
import GppVerify.ThreadWeilParity.RemovableSingularityLimit

-- ── Suzuki-Herglotz thread, reflection-symmetry algebra (New, 2026-08-23) ──
-- formalization_queue item dcebf59f. Re-checking this thread's items directly
-- (not just its Herglotz-suggestive name) found this one is pure algebra once
-- A, B are expressed through the same abstract function I -- costs nothing,
-- needs no operator/reflection/integral machinery at all.
import GppVerify.ThreadWeilParity.SuzukiReflectionSymmetry

-- ── Thread Weil-Parity, sharpening the d1aec733 open item (New, 2026-08-23) ──
-- Turns an earlier vague "carries a subtlety" note into a checked finding:
-- c_j = g_j * w^2 (plain square), not g_j * |w|^2, given the item's own
-- forward-direction definitions -- confirms the forward/converse formulas
-- only agree when w = u_j^*e0 is real, an unstated extra hypothesis.
import GppVerify.ThreadWeilParity.CommutingMetricResidueGap

-- ── Suzuki-Herglotz thread, item 1c684543 (New, 2026-08-23) ──────────────────────────
-- "Shifted logarithmic-derivative transfer preserves the xi zero divisor" -- flagged in
-- FORMALIZATION_PLAN.md as tractable (plain complex-analysis order-of-vanishing, not
-- Herglotz-dependent). Writing the order as m=k+1 to avoid Nat subtraction: for
-- F z := (z-rho)^(k+1) * g z with g analytic and g rho != 0, deriv F z - lam * F z =
-- (z-rho)^k * w z with w z := (k+1)*g z + (z-rho)*(deriv g z - lam*g z)
-- (deriv_shiftedTransferF_sub_smul_eq, from an actual HasDerivAt computation), and
-- w rho = (k+1)*g rho != 0, so the quotient R_lam := F/D_lam satisfies R_lam(z)/(z-rho) ->
-- 1/(k+1) as z->rho (tendsto_shiftedTransfer_quotient_div) -- the item's own stated
-- asymptotic R_lam(s)=(s-rho)/m+O((s-rho)^2), i.e. a genuine SIMPLE zero at rho for every
-- finite lambda -- and R_lam(z) -> 0 as z->rho (tendsto_shiftedTransfer_quotient_zero),
-- the "zeros of R_lam are (among) the zeros of F" half of the item's conclusion. 8
-- theorems, kernel-clean, no axiom, no sorry. Does NOT instantiate F=xi (a direct
-- application once xi's zeros are known simple with the right local model, not attempted)
-- and does NOT prove the global "exactly the zeros of F, no others" claim (needs D_lam
-- controlled away from F's zeros too, a separate global argument).
import GppVerify.ThreadWeilParity.ShiftedLogDerivativeTransfer

-- ── Codex: Global von Mangoldt / completed-factorization chain (merge fixup) ──
-- GlobalCompletedFactorization.lean and LogDerivativeProduct.lean were genuinely
-- orphaned in the codex/lean-workbench import list (not reachable from any import
-- root anywhere in the tree, confirmed by full-repo grep) -- added directly here so
-- `lake build GppVerify` actually type-checks them, matching every other file's
-- convention of being reachable from this root.
import GppVerify.RiemannHypothesis.GlobalCompletedFactorization
import GppVerify.RiemannHypothesis.LogDerivativeProduct
