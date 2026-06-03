-- Axiom audit script for GPPVerify
-- Run with: lake env lean --run scripts/check_axioms.lean
-- Reports all axioms used by the main theorems.

import GppVerify

#print axioms haar_invariant_under_automorphism
#print axioms grassmannian_haar_self_duality
#print axioms GppHaar.adelic_haar_self_dual
#print axioms GppRH.two_zeros_at_ordinate
#print axioms GppRH.riemann_hypothesis
#print axioms GppShadow.shadow_equals_time_reversal
#print axioms GppShadow.three_generations_from_c0_and_link6
#print axioms GppFE.critical_line_is_fixed_locus
