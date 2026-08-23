-- Axiom audit script for GPPVerify
-- Run with: lake env lean scripts/check_axioms.lean
--
-- (Do NOT use `--run`: the file has no `main`, so `--run` exits nonzero on an
--  "unknown declaration 'main'" error even though the audit itself succeeded.
--  Without `--run` the #print axioms output is emitted and the exit code is 0.)
--
-- Reports the axiom dependencies of the flagship theorems.
--
-- ── READ THIS BEFORE ADDING A LINE ──────────────────────────────────────────
-- Audit the REAL theorem, never a stub. This repo parks open results as
-- `theorem foo : True := trivial` (or `∀ (_ : True), True`), which is the honest
-- convention — but such a stub reports "does not depend on any axioms", the
-- cleanest possible bill of health, while asserting nothing.
--
-- This script contained exactly that bug until 2026-08-14: it audited
-- `GppShadow.three_generations_from_c0_and_link6`, a `∀ (_ : True), True` stub in
-- ShadowSymmetry.lean, and duly reported it axiom-free. The real theorem is
-- `GppLink6.three_generations_from_c0`, which depends on six custom axioms
-- including the OPEN `link6_from_physics`. Audit that one instead.
--
-- Before adding a theorem here, check it is not a stub:
--   grep -n "<name>" -A 3 <file>      -- look for `: True :=` or `∀ (_ : True), True`
-- ────────────────────────────────────────────────────────────────────────────

import GppVerify

-- Haar / self-duality layer — expected: Lean built-ins only
#print axioms haar_invariant_under_automorphism
#print axioms grassmannian_haar_self_duality
#print axioms GppHaar.adelic_haar_self_dual

-- Zeta / functional-equation layer — expected: Lean built-ins only
#print axioms GppRH.two_zeros_at_ordinate
#print axioms GppFE.critical_line_is_fixed_locus
#print axioms GppShadow.shadow_equals_time_reversal

-- The flagship RH conditionals (Thread D / D2) — expected: Lean built-ins only.
-- These are the statements that matter: RH FROM a genuine positivity hypothesis,
-- never RH restated.
#print axioms GppWeilCriterion.rh_iff_weil_pairedForm_nonneg
#print axioms GppWeilCriterion.rh_of_weil_pairedForm_nonneg
#print axioms GppWeilCriterion.rh_iff_two_point_pairedForm_nonneg
#print axioms GppWeilCriterion.rh_of_two_point_pairedForm_nonneg

-- Transport / truncation layer — expected: Lean built-ins only
#print axioms GppTransport.logPrime_lattice_injective
#print axioms GppTransport.truncated_transport

-- Temperedness scaffold. `schwartz_integral_clm_exists` was retired as an axiom on
-- 2026-08-14 (now proved via Mathlib's `SchwartzMap.integralCLM`), so it must show
-- Lean built-ins only. `temperedness_iff_critical_line` should show exactly ONE
-- custom axiom, `exp_growth_not_tempered` — if a second appears, something regressed.
#print axioms GppRH.schwartz_integral_clm_exists
#print axioms GppRH.temperedness_iff_critical_line

-- Thread HT — the prime–Archimedean heat trace (elementary layer).
-- All expected: Lean built-ins only. Nothing here proves or assumes RH.
#print axioms GppHeatTrace.completelyMonotone_exp_neg
#print axioms GppHeatTrace.resolvent_laplace
#print axioms GppHeatTrace.laplace_resolvent_shift
#print axioms GppHeatTrace.subordination_at_zero
#print axioms GppHeatTrace.primeSide_heatGaussian
-- The general-x subordination formula, in full (no Bessel-function machinery used).
#print axioms GppHeatTrace.subordination_general
#print axioms GppHeatTrace.archimedeanLaplace_aux_one
#print axioms GppHeatTrace.archimedeanLaplace_aux_two

-- Thread S, Step 1 — abstract Hermitian inertia core (base layer only).
-- Expected: Lean built-ins only.
#print axioms GppThreadS.inertia_sum

-- OPEN PHYSICS INPUTS — these are EXPECTED to carry custom axioms. Listed so the
-- dependency is visible in every CI run rather than buried. `link6_from_physics`
-- is the open thm:link6; `boyle_turok_2021` is an uncited external analysis.
#print axioms GppLink6.three_generations_from_c0

-- Thread Weil-Parity — the exact Archimedean renormalization tail. Expected: Lean
-- built-ins only. Promotes a numerical-checkpoint correction (lean_results
-- 079ca52f) to a closed-form theorem. No claim about Q_{lambda,N}'s eigenvalues.
#print axioms GppWeilParity.archimedean_diagonal_tail

-- Thread Weil-Parity — cross-resolvent core (formalization_queue items 3ebed50a,
-- 0cf9aebf). Expected: Lean built-ins only. Abstract finite-dimensional theorems;
-- the actual arithmetic CCM matrix's positivity hypotheses are NOT established
-- (research_notes 35a9efdc: counterexample at c=13,N=6). No RH claim.
#print axioms cross_resolvent_det_identity
#print axioms parity_crossing_obstruction

-- Thread Weil-Parity — odd eigenpair canonical lift (formalization_queue item c0c96bbc).
-- Expected: Lean built-ins only.
#print axioms odd_eigenpair_defect_step1
#print axioms odd_eigenpair_defect_step2
#print axioms odd_eigenpair_canonical_lift

-- Tree-loop-sewing topology (GppTreeLoopSewing) — from Toupin "Loop Integrands Hidden
-- in Trees" (Aug 2026). Pure graph-combinatorics: expected Lean built-ins only. The
-- genuinely analytic celestial-sewing identity is a LOCAL hypothesis
-- (ShadowPairSewing.sewing_identity), not proved here — tree_to_loop_extraction is
-- correctly conditional on it (an instance argument), so auditing it shows the
-- built-ins used to derive the corollary from that hypothesis, not a claim the
-- hypothesis itself is discharged.
#print axioms GppTreeLoopSewing.principalSeries_isShadowPair
#print axioms GppTreeLoopSewing.shadowPair_sum_two
#print axioms GppTreeLoopSewing.shadowDim_involutive
#print axioms GppTreeLoopSewing.pairSewing_cycleRank
#print axioms GppTreeLoopSewing.tree_to_L_loop_counts
#print axioms GppTreeLoopSewing.sixPoint_onePair_oneLoop_counts
#print axioms GppTreeLoopSewing.boxDenominator_is_pairClosure
#print axioms GppTreeLoopSewing.ShadowPairSewing.tree_to_loop_extraction

-- Thread QG-Blackbody (StefanBoltzmannFamily, GammaModulusIdentity, AllLoopFiniteness)
-- — from haar_qg_paper_v215.tex, kinematic_block_v1.tex, blackbody_law_qg_dtoupin_v1.tex.
-- Expected: Lean built-ins only, on all five.
#print axioms GppStefanBoltzmann.stefan_boltzmann_family
#print axioms GppStefanBoltzmann.m_one_eq
#print axioms GppStefanBoltzmann.m_three_eq
#print axioms GppGammaModulus.gamma_one_add_mul_gamma_one_sub
#print axioms GppAllLoopFiniteness.finiteness

-- Thread QG-Blackbody round 2 (KinematicZetaBridge, SinhWeierstrassProduct) — from
-- kinematic_block_v1.tex Prop 7.1(a) and blackbody_law_qg_dtoupin_v1.tex T4.
-- Expected: Lean built-ins only, on both.
#print axioms GppKinematicBlock.zeta_bridge_kappa
#print axioms GppSinhWeierstrass.tendsto_prod_one_add_sq_div

-- Thread QG-Blackbody round 3 (CumulantLaw) — from blackbody_law_qg_dtoupin_v1.tex T5.
-- Expected: Lean built-ins only.
#print axioms GppCumulantLaw.cumulant_law

-- Thread QG-Blackbody round 4 (SpectralWeightIdentities) — Planck form and the reciprocal
-- Weierstrass product for P(lam) = pi*lam/sinh(pi*lam). Expected: Lean built-ins only, both.
#print axioms GppSpectralWeight.planck_form
#print axioms GppSpectralWeight.one_div_P_tendsto_tprod

-- Digamma via Mathlib's Gamma calculus (task #9). Expected: Lean built-ins only, all five.
#print axioms GppDigamma.digamma_one
#print axioms GppDigamma.digamma_one_half
#print axioms GppDigamma.digamma_nat_add_one
#print axioms GppDigamma.digamma_add_one

-- Local-field shadow kernels (new research front). Expected: Lean built-ins only, all five.
#print axioms GppLocalShadow.archKernel_reflection
#print axioms GppLocalShadow.archKernel_shadow_eq_conj
#print axioms GppLocalShadow.archKernel_principal_series
#print axioms GppLocalShadow.archKernel_principal_series_pos
#print axioms GppDiagonalLift.delta_D
#print axioms GppDiagonalLift.J_D
#print axioms GppDiagonalLift.D_one_sub_eq_shadow2_D
#print axioms GppDiagonalLift.delta_shadow2_D

-- §9 resolution (2026-08-22): the physical kernel and Weyl intertwiner are distinct objects.
-- (two_mul_pi_cpow_split is a private proof-internal helper, not auditable from here.)
-- Expected: Lean built-ins only, all three.
#print axioms GppLocalShadow.GammaC_eq_GammaR_mul_GammaR_succ
#print axioms GppLocalShadow.archKernel_two_eq_GammaC_product
#print axioms GppLocalShadow.archKernel_two_eq_GammaR_sectors

-- Global Eisenstein coefficient (completedRiemannZeta functional equation). NOT an RH claim.
-- Expected: Lean built-ins only, both.
#print axioms GppEisenstein.eisensteinCoeff_eq_shadow_ratio
#print axioms GppEisenstein.eisensteinCoeff_reflection

-- The golden ratio as the minimal hyperbolic sector of PSL2(Z) (2026-08-22). Physical-sector
-- identification is NOT claimed anywhere here -- these are pure arithmetic/matrix theorems.
-- Expected: Lean built-ins only, all eleven.
#print axioms GppGoldenHyperbolic.fixedPoint_iff_gold
#print axioms GppGoldenHyperbolic.M_sq_eq_A
#print axioms GppGoldenHyperbolic.det_M
#print axioms GppGoldenHyperbolic.det_A
#print axioms GppGoldenHyperbolic.trace_A
#print axioms GppGoldenHyperbolic.hyperbolic_trace_ge_three
#print axioms GppGoldenHyperbolic.A_trace_attains_min
#print axioms GppGoldenHyperbolic.A_charpoly_root_goldSq
#print axioms GppGoldenHyperbolic.A_charpoly_root_goldInvSq
#print axioms GppGoldenHyperbolic.discrA_eq_five
#print axioms GppGoldenHyperbolic.A_mobius_fixedPoints
#print axioms GppGoldenHyperbolic.finitePlaceKernel_half
#print axioms GppGoldenHyperbolic.finitePlaceKernel_five_half
#print axioms GppGoldenHyperbolic.golden_convergence

-- Dispersion reconstruction (GppDispersion) — the general, physics-convention-
-- independent Sokhotski-Plemelj mechanism underlying ShadowPairSewing.sewing_identity.
-- Expected: Lean built-ins only, on both. Does NOT discharge sewing_identity: see
-- DispersionReconstruction.lean's module doc for the three named hypotheses (H1-H3)
-- this reduces the opaque hypothesis to.
#print axioms GppDispersion.lorentzian_jump
#print axioms GppDispersion.lorentzian_kernel_tendsto_zero_off_pole

-- Local shadow kernels / finite-prime Weil kernel (2026-08-22/23, fourth pass). No RH claim,
-- no global positivity claim -- see CutkoskyWeilBridge.lean's module doc and
-- discovery/cutkosky_weil/notes.md for the corrected central finding (K_p-1 IS a positive
-- kernel; the earlier Toeplitz-indefiniteness claim tested the wrong notion) and the
-- completed analytic passage (removable singularity C(0)=1/(8*pi); the N->infinity limit
-- from the finite-truncation milestone KrN0_gram_nonneg to genuine, untruncated
-- PositiveType(K_r-1)). Expected: Lean built-ins only, all.
#print axioms GppCutkoskyWeil.Kp_pos
#print axioms GppCutkoskyWeil.H_nonneg
#print axioms GppCutkoskyWeil.gram_square_freq
#print axioms GppCutkoskyWeil.gram_square_freqSum
#print axioms GppCutkoskyWeil.gram_square_freqSum_nonneg
#print axioms GppCutkoskyWeil.KrN0_gram_nonneg
#print axioms GppCutkoskyWeil.Kp_eq_KrClosed
#print axioms GppCutkoskyWeil.tendsto_cutKernel_zero
#print axioms GppCutkoskyWeil.Hext_zero
#print axioms GppCutkoskyWeil.Hext_nonneg
#print axioms GppCutkoskyWeil.tendsto_Icc_atTop
#print axioms GppCutkoskyWeil.summable_KrClosed_summand
#print axioms GppCutkoskyWeil.tsum_KrClosed_summand_eq
#print axioms GppCutkoskyWeil.tendsto_KrN0
#print axioms GppCutkoskyWeil.KrClosed_minus_one_tendsto_positive
#print axioms GppCutkoskyWeil.KrClosed_minus_one_positiveType
-- Fifth pass: operator-level vacuum-compression identity on ℓ²(ℤ,ℂ)
#print axioms GppCutkoskyWeil.memℓp_mul_bounded
#print axioms GppCutkoskyWeil.mulOpLin_comp
#print axioms GppCutkoskyWeil.mulOpLin_norm_le
#print axioms GppCutkoskyWeil.mulOpCLM_inner_re_nonneg
#print axioms GppCutkoskyWeil.P0Weight_mul_KrWeight_mul_P0Weight_eq
#print axioms GppCutkoskyWeil.vacuum_compression_operator_identity
#print axioms GppCutkoskyWeil.KrMinusOneWeight_re_nonneg
#print axioms GppCutkoskyWeil.vacuum_compressed_operator_positive
