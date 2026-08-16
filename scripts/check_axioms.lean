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
