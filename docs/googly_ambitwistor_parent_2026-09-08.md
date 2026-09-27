# Googly problem: nonchiral ambitwistor parent architecture

Status: research architecture note, 2026-09-08. This document deliberately separates established external theorems, exact GPPVerify algebra, and the remaining GPP bridge.

## 1. What the original googly problem asks

The nonlinear graviton/Ward constructions are chiral. A single ordinary twistor space naturally describes one self-duality sector, while a generic physical field has both. The strict historical googly problem asks for an equally natural nonlinear twistor description of the opposite interacting helicity using the same chiral twistor framework.

A 2026 result of Adamo, Araneda, Seet and Sharma gives a single-twistor-space resolution for the particular Schwarzschild solution, not yet a general solution for arbitrary Einstein geometry.

## 2. Established nonchiral parent: projective ambitwistor space

For the physical goal of describing the full field rather than insisting on a single chiral PT, the older ambitwistor route is already much stronger than the current GPP manuscripts acknowledged.

Projective ambitwistor space PA is the space of projective complex null geodesics. In flat four dimensions it is the incidence quadric

    PA = {(Z,W) in PT x PT* : Z.W = 0}.

It carries the canonical contact structure descended from the cotangent symplectic potential.

Established external results used as inputs, not Lean theorems:

1. Witten / Isenberg-Yasskin-Green: a Yang-Mills connection is encoded by a holomorphic vector bundle on ambitwistor space, and the full Yang-Mills equations are equivalent to extension of the bundle to the third formal neighbourhood of the ambitwistor quadric in PT x PT*.

2. LeBrun: the complex structure of projective ambitwistor space determines the conformal spacetime; contact-preserving deformations correspond to conformal deformations.

3. Baston-Mason / LeBrun formal-neighbourhood results: fifth-order extension is tied to Bach-flatness; for algebraically general curvature, sixth-order extension corresponds to conformally Einstein geometry. LeBrun's Einstein bundle gives a direct conformal-class criterion for Einstein metrics.

Therefore the full nonchiral classical field already has a natural twistor-based parent. The strict unsolved part is not “can null/twistor geometry contain both helicities at all?” but “can this be reduced to an equally economical single-chiral-twistor nonlinear construction, and can the ambitwistor reconstruction be made intrinsic, global and computationally effective for general Einstein fields?”

## 3. Exact GPPVerify spine already proved

The branch `codex/orientation-mass-time-formalization` contains the following unconditional finite-dimensional pieces:

- `TaggedAmbitwistorParity.lean`: PT and PT* remain different representation types; factor exchange is an exact involution on tagged incidence pairs.
- `AmbitwistorContactExchange.lean`: factor exchange negates the flat ambitwistor contact potential while preserving its contact hyperplane distribution.
- `AmbitwistorContactNeutralCone.lean`: the contact screen splits into two Lagrangian halves with neutral quadratic form and antisymmetric Levi pairing.
- `AmbitwistorContactRaySlice.lean`: on every polarized rank-two screen slice, contact-half exchange descends exactly to the reciprocal ray involution `(x,p)->(p,x)` and the contact Levi form becomes the ray Wronskian.
- `EinsteinNullRaySL2Geometry.lean`: the null-ray Einstein/Sturm carrier is an SL(2) Wronskian system.
- `EinsteinChiralCurvatureBlocks.lean`: Einstein block-diagonality is invariant under orientation reversal, and orientation reversal exchanges the two already-existing diagonal Weyl sectors.
- `NonlinearGooglyClosure.lean`: once a genuine Penrose duality square and nonlinear compatibility equation are supplied, the opposite twistor representative is uniquely fixed on shell under injectivity.

These results support a nonchiral-parent interpretation. They do **not** yet prove the global analytic reconstruction theorem inside Lean.

## 4. Corrected GPP googly target

Do not use the old claim “shadow = T therefore the googly problem is solved” as the core theorem. The stronger and cleaner target is:

    curved PA/contact + sky family + Einstein selector
        -> full conformal/Einstein spacetime
        -> two chiral PT/PT* polarizations
        -> asymptotic celestial light/shadow/Fourier transforms.

The opposite helicity is not generated from nothing by the first chiral half. Both are projections of one nonchiral null-geodesic geometry.

The required new theorem is a global intertwiner identifying the rank-two projective system obtained from the sky/NSF null-geodesic bundle with the corresponding rank-two subsystem of the LeBrun/ambitwistor contact geometry, with compatible Wronskian/Levi form, projective connection, and chiral projection maps.

## 5. Relation to celestial holography

At null infinity, the nonchiral parent should reduce to the two celestial helicity representations. The already formalized half-Fourier/light-transform diamond supplies the finite representation-theoretic skeleton; the analytic Mellin/light integrals and their identification with the curved PA projections remain open.

The four-point crossing/Legendre program is relevant because the celestial cross-ratio base carries a canonical rank-two Gauss-Manin system and integral symplectic lattice. If the sky/NSF rank-two projective bundle is globally intertwined with that system, the primitive integral unipotent becomes canonical and the golden trace-three sector becomes a structural possibility rather than a coordinate choice. Pure Gamma(2) monodromy alone is formally proved insufficient.

## 6. Massive extension

A timelike momentum is assembled from two null spinor roots. GPPVerify proves that their symplectic area has modulus equal to mass and that the Grassmannian elliptic sector descends exactly to the rest-Dirac quarter-cycle. Thus the natural strategy is:

    massless nonchiral null parent
       + pair of null roots
       -> massive spinor pair
       -> mass = oriented spinor area modulus
       -> Compton phase omega_C = mc^2/hbar
       -> zitter beat = 2 omega_C.

This is a concrete massless-to-massive bridge. The interpretation of the negative-energy phase as a second CPT-oriented spacetime remains a hypothesis, not part of the zitter theorem.

## 7. Immediate proof frontier

1. Prove the sky/NSF ↔ curved ambitwistor/LeBrun rank-two projective-connection intertwiner.
2. Connect the projective solution ratio to the Legendre/Gauss-Manin period ratio, including the Schwarzian/projective connection and integral lattice.
3. Recover the two chiral Penrose projections from the nonchiral parent and prove the nonlinear compatibility equation required by `NonlinearGooglyClosure`.
4. Take the asymptotically flat limit and identify the induced boundary transform with the correct celestial light/shadow/Fourier operation, keeping linear shadow distinct from anti-linear time reversal.
5. Only then re-state a googly resolution theorem and rebuild the held papers.

This route preserves the useful GPP discoveries while replacing earlier overclaims by a theorem-compatible architecture.
