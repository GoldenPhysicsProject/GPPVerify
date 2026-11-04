import GppVerify.StandardModel.OrientationCliffordCore
import GppVerify.StandardModel.FeynmanCheckerboard
import GppVerify.StandardModel.WhichWayForwardV26Gaps
import GppVerify.CelestialHolography.DiracZitterDeckPeriod
import GppVerify.StandardModel.WhichWayForwardSignatureScan
import GppVerify.StandardModel.WhichWayForwardDeterminantCover
import GppVerify.StandardModel.WhichWayForwardDeckAntilinear
import GppVerify.StandardModel.WhichWayForwardArithmetic
import GppVerify.StandardModel.WhichWayForwardFamilySigns
import GppVerify.StandardModel.WhichWayForwardPauliStrings
import GppVerify.StandardModel.WhichWayForwardParentSigns
import GppVerify.StandardModel.WhichWayForwardParentFamilies
import GppVerify.StandardModel.WhichWayForwardNewCPT

/-!
# *Which Way Is Forward?* — the Lean formalization, assembled

Capstone file for the formalization of *Which Way Is Forward? Charge,
Time and Orientation* (Daniel Toupin, Zenodo DOI
10.5281/zenodo.23421056). It imports every module of the
formalization and closes with an axiom audit of the principal
declaration of each claim group. Every declaration named below is
kernel-checked with no `sorry` and no axioms beyond the standard
three (`propext`, `Classical.choice`, `Quot.sound`), as the audit at
the end of this file verifies.

## The claim groups and where they live

1. **The orientation algebra and the Cl(2,2) carrier.**
   `OrientationCliffordCore`: the complex structures `a`, `b`, the real
   involution `c`, `chi = -ab = -(volume element)`
   (`chi_eq_neg_volume`), `r_t = r_q * c` (`rt_eq_rq_mul_c`), the
   unitary four-lift intertwiner (`intertwiner_unitary`), the carrier
   group of order 16 with its order counts and centre
   (`carrier_order_counts`, `carrier_center`, `D_not_central`), the
   real form Fix(D) (`fixD_iff`, `halfFlips_agree_on_fixD`,
   `Rt_reverses_chi`), and the Cl(3,1) Minkowski realization of the
   same algebra (`minkowski_realization`).
2. **The Feynman checkerboard.** `FeynmanCheckerboard`: the path sum
   (`pathSum_eq`), turn and step products, the massless transfer
   matrix, and the physical dispersion relation
   (`transfer_sq_physical`): mass is the reversal amplitude.
3. **Equal lift weight and the entropy profile.** `WhichWayForwardV26Gaps`:
   a reversal-invariant weight gives `mu(++) = mu(--)` with weight 1/2
   per orbit (`equal_lift_weight`); an even entropy profile has odd
   derivative, and the oriented rate is the absolute rate
   (`oriented_rate_eq_abs`).
4. **The half flip is not the deck element.** Linear case:
   `WhichWayForwardV26Gaps.half_flip_not_deck`. Antilinear case:
   `WhichWayForwardDeckAntilinear.half_flip_not_deck_antilinear`.
5. **The determinant cover.** Algebraic step:
   `WhichWayForwardV26Gaps.det_lorentz_chart`,
   `det_hermitian_slice`. Topological step:
   `WhichWayForwardDeterminantCover`: the meridian loop, its explicit
   square-root lift with `sqrtLift_sq` and the endpoint flip
   `sqrtLift_one`, and `no_periodic_sqrt` — no continuous periodic
   square root of the loop exists.
6. **Dimension splits.** `WhichWayForwardV26Gaps.so102_dimension_split`:
   66 = 28 + 6 + 32 and 32 = 24 + 4 + 4.
7. **The zitter period.** `DiracZitterDeckPeriod.zitterPeriod_eq_deckInterval`:
   `T_Z = pi / omega_C`, the deck interval, in exact algebra form.
8. **Character duality.** `WhichWayForwardV26Gaps.unit_character_inv_eq_conj`:
   `|z| = 1` implies `z^-1 = conj z`.
9. **The coordinate signature scan.** `WhichWayForwardSignatureScan`:
   the coordinate-bivector triples of the orientation algebra exist
   only at signature (2,2) (`signature_scan_counts`,
   `signature_scan_only_22`).
10. **The parent charge-conjugation signs (theorem
    `parentquaternionic`).** `WhichWayForwardFamilySigns` (layer A:
    the product formula `prod_mul_map_starRingEnd_prod`),
    `WhichWayForwardPauliStrings` (the Pauli-string engine),
    `WhichWayForwardParentSigns` (the generators), and
    `WhichWayForwardParentFamilies` (the concrete families):
    `B * conj(B) = -1` for both families at (6,2) (quaternionic),
    `B * conj(B) = +1` for both families at (10,2) (real), and the
    uniform intertwining `B * conj(gamma_j) = eps * (gamma_j * B)`
    with `eps = -1` for a real family and `eps = +1` for an imaginary
    family, at both signatures.
11. **Orientation arithmetic.** `WhichWayForwardArithmetic`:
    `mw_extension_ranks`, the factorwise congruences, `feynman_phase`.
12. **The CPT theorem in arrow form.** `WhichWayForwardNewCPT`: on the
    label model `(q, t, h) in {+-}^3` with `chi = q * t`, Wigner's
    `T_W` is fixed by its defining property (it fixes the charges),
    which forces `T_W = C o T_g`; the theorem `cpt_arrow_form` states
    `C o P o T_W = P o T_g` on every label, and
    `cpt_with_arrow_acts_as_parity` states that `C o P o T_g` acts on
    the observables `(chi, h)` as parity alone. `theta_chi`: the full
    operation `Theta = P o T_g` fixes `q` and flips `t`, `h`, `chi`.

## Scope

The formalization covers the paper's exact finite and algebraic
claims: the content of the paper's own check script `verify_wwif.py`
together with the algebraic cores above and the arrow-form CPT
theorem. The paper's five conjectures are open statements and are
not asserted here. The finite label model of group 12 models the
paper's CPT statement; the Lüders-Pauli field theorem is the
statement modelled, not reproved.
-/

-- Axiom audit: the principal declaration of each claim group.
#print axioms GppOrientationCliffordCore.orientation_algebra
#print axioms GppOrientationCliffordCore.chi_eq_neg_volume
#print axioms GppOrientationCliffordCore.rt_eq_rq_mul_c
#print axioms GppOrientationCliffordCore.intertwiner_unitary
#print axioms GppOrientationCliffordCore.carrier_order_counts
#print axioms GppOrientationCliffordCore.carrier_center
#print axioms GppOrientationCliffordCore.halfFlips_agree_on_fixD
#print axioms GppOrientationCliffordCore.Rt_reverses_chi
#print axioms GppOrientationCliffordCore.minkowski_realization
#print axioms GppCheckerboard.pathSum_eq
#print axioms GppCheckerboard.transfer_sq_physical
#print axioms GppWhichWayV26.equal_lift_weight
#print axioms GppWhichWayV26.oriented_rate_eq_abs
#print axioms GppWhichWayV26.half_flip_not_deck
#print axioms GppWhichWayV26.det_lorentz_chart
#print axioms GppWhichWayV26.det_hermitian_slice
#print axioms GppWhichWayV26.so102_dimension_split
#print axioms GppWhichWayV26.unit_character_inv_eq_conj
#print axioms GppDiracZitterDeckPeriod.zitterPeriod_eq_deckInterval
#print axioms GppWhichWayForwardSignatureScan.signature_scan_counts
#print axioms GppWhichWayForwardSignatureScan.signature_scan_only_22
#print axioms GppWhichWayForwardDetCover.sqrtLift_sq
#print axioms GppWhichWayForwardDetCover.sqrtLift_one
#print axioms GppWhichWayForwardDetCover.no_periodic_sqrt
#print axioms GppWhichWayForwardDeck.half_flip_not_deck_antilinear
#print axioms GppWhichWayForwardArithmetic.mw_extension_ranks
#print axioms GppWhichWayForwardArithmetic.feynman_phase
#print axioms GppWhichWayForwardFamilySigns.prod_mul_map_starRingEnd_prod
#print axioms GppWhichWayForwardPauliStrings.stringMatrix_mul
#print axioms GppWhichWayForwardPauliStrings.stringMatrix_sq
#print axioms GppWhichWayForwardParentSigns.genMatrix_sq
#print axioms GppWhichWayForwardParentSigns.genMatrix_conj
#print axioms GppWhichWayForwardParentSigns.prod_mul_of_mem
#print axioms GppWhichWayForwardParentFamilies.fam62real_prod_conj
#print axioms GppWhichWayForwardParentFamilies.fam62imag_prod_conj
#print axioms GppWhichWayForwardParentFamilies.fam102real_prod_conj
#print axioms GppWhichWayForwardParentFamilies.fam102imag_prod_conj
#print axioms GppWhichWayForwardParentFamilies.fam62real_intertwining
#print axioms GppWhichWayForwardParentFamilies.fam62imag_intertwining
#print axioms GppWhichWayForwardParentFamilies.fam102real_intertwining
#print axioms GppWhichWayForwardParentFamilies.fam102imag_intertwining
#print axioms GppWhichWayForwardNewCPT.cpt_arrow_form
#print axioms GppWhichWayForwardNewCPT.cpt_with_arrow_acts_as_parity
#print axioms GppWhichWayForwardNewCPT.theta_chi
