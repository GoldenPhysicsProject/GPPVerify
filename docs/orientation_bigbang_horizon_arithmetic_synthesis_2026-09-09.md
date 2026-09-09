# Orientation, matter origin, horizons, and arithmetic reciprocity — 2026-09-09

## Executive result

The current orientation programme has reached a sharper statement than the original
`q*t` mnemonic.

1. The first microscopic sign must be **representation-conjugacy orientation**, not the
   numerical sign of electric charge.  Ordinary matter already contains both electric
   signs (proton-like and electron-like species).  For a species with reference
   representation `R` and charge vector `q0`, a conjugacy sign `c=+/-1` distinguishes
   `R` from `R*` and sends the whole internal charge vector to its conjugate.
2. The second sign is the microscopic temporal/phase/sheet orientation `t=+/-1`, distinct
   from coordinate time and from the thermodynamic arrow.
3. The candidate relational matter character is

       chi = c t.

   A complete diagonal reversal `(c,t)->(-c,-t)` preserves `chi`; either half flip changes
   it.
4. Exact finite algebra now proves that diagonal CPT/deck invariance **does not require a
   matter/antimatter balance**.  The diagonal-even subspace contains independent `chi=+`
   and `chi=-` sectors.  In particular the pure matter lift

       |M> ~ |++> + |-->

   is already diagonal invariant.  Thus, if physical CPT is realized by the diagonal
   orientation involution, a globally CPT-symmetric state can lie entirely in the
   relational-matter sector.
5. A `chi`-even dynamics cannot convert a `chi=+` one-particle state into `chi=-`.
   Anti-aligned excitations require a `chi`-odd interaction/defect, or a many-body process
   with compensation elsewhere.  This is the exact form of the intuition that it is hard
   to obtain `+-` from an initially aligned `++/--` configuration.

The crucial caveat is equally sharp: physical CPT has not yet been proved to equal the
project's diagonal deck operation, and the Standard Model does create laboratory
antiparticles.  The claim under investigation is therefore **not** that antimatter
excitations are impossible.  It is that primordial global CPT symmetry need not mean a
50/50 population of relational matter and relational antimatter.

## Big-Bang pair creation without a missing-antimatter reservoir

For a species with reference charge scale `e`, define

    Q_conv = e c,
    Q_rel  = e c t.

The two CPT-related sheet representatives are

    (c,t)       on sheet +,
    (-c,-t)     on sheet -.

Then exactly

    Q_conv(c) + Q_conv(-c) = 0,

while

    Q_rel(c,t) = Q_rel(-c,-t)

and hence

    Q_rel(c,t) + Q_rel(-c,-t) = 2 Q_rel(c,t).

Therefore a CPT-paired creation event at a two-sheet branch surface can create opposite
**conventional** internal charges with zero global conventional charge while creating two
representatives of the same **relational matter class**.  From one sheet the partner is
called the antiparticle because its internal representation is conjugate.  Relative to its
own reversed microscopic orientation, however, it is matter.

This gives a concrete replacement for the phrase "half the Big Bang was antimatter":

    vacuum/boundary -> (R,+) + (R*,-)

is globally charge-conserving and CPT-paired, but both outputs have `chi=+`.

This mechanism removes a logical requirement for a primordial relational-antimatter
reservoir.  It does **not** yet determine why the sheetwise baryon density is nonzero or why
the observed baryon-to-photon ratio has its measured magnitude.

## Baryon and lepton number: the index route

The matter-antimatter cosmological problem is not primarily the sign of electric charge.
The robust observables are baryon/lepton asymmetries, while the Universe remains extremely
electrically neutral.  Electroweak topology provides an existing exact bridge between
fermion number and a chiral index/spectral flow.

For electroweak topological index `k` and `N_g` generations,

    Delta B = N_g k,
    Delta L = N_g k,
    Delta(B-L) = 0,
    Delta(B+L) = 2 N_g k.

Orientation reversal exchanges chiralities and reverses the chiral Dirac index, so a
CPT-mirror sheet naturally carries `-k`.  Therefore

    Delta B_+ + Delta B_- = 0,

but with sheet signs `t_+=+1`, `t_-=-1`,

    t_+ Delta B_+ + t_- Delta B_- = 2 Delta B_+.

The same holds for lepton number.

This suggests a much more concrete matter-origin target than generic baryogenesis:

> **Oriented-index hypothesis.**  The primordial matter excess seen by either sheet is the
> orientation-weighted boundary index/spectral flow of a globally CPT-paired Dirac/gauge
> system.  Conventional global baryon/lepton number cancels between sheets, while the
> relational/oriented index has the same sign on both.

A natural theorem target is an APS-type relation on the two-sheet geometry,

    ind D_+ = - ind D_-,
    I_rel := t ind D,

followed by an anomaly map from `I_rel` to the observed sheetwise `B`, `L`, or preferably
whatever exactly conserved/approximately conserved combination survives the neutrino and
electroweak sectors.  Electroweak sphalerons violate `B+L` but conserve `B-L`; this makes
`B-L` the first dynamical charge to test, without assuming it is exact in the ultraviolet.

This route could bypass the *interpretive* missing-antimatter problem while still leaving a
real quantitative problem: the boundary state/index must predict the magnitude and sign of
the sheetwise asymmetry rather than insert it.

## Horizon: no interior crossing in the quotient sense

The existing `HorizonCPTFluxGluing.lean` sign theorem already gives the right boundary
bookkeeping.  Under

    (q,u,n) -> (-q,-u,-n),

where `q` is internal conjugacy/charge orientation, `u` oriented worldline flow and `n` the
oriented hypersurface normal,

    j = q u

is unchanged, but its oriented normal flux reverses.  Hence paired fluxes cancel:

    Phi_Q^+ + Phi_Q^- = 0.

Quadratic stress is even, so energy flux instead adds:

    Phi_E^+ + Phi_E^- = 2 Phi_E^+.

This is exactly the sign pattern needed for a horizon which is a **fermion/current gluing
surface rather than a conduit to an independent interior**: no net oriented charge/fermion
flux crosses the quotient, while positive energy remains available to be converted into
neutral radiation.

The black-mirror geometry provides a concrete spacetime carrier for this idea: its horizon
is the boundary between two CPT-related exteriors and the model explicitly proposes that
infalling CPT-paired particle/antiparticle trajectories meet there and annihilate.  The GPP
extension is to interpret those two trajectories as the two orientation representatives of
one relational fermionic state, if a spin/gauge bundle intertwiner can actually be built.

The hard theorem is now precise.  Construct a two-sheet Dirac bundle and boundary map

    Psi_-|_H = e^{i alpha} Theta_CPT Psi_+|_H

such that

1. the Dirac operator is self-adjoint on the glued domain;
2. the quotient normal fermion current vanishes exactly;
3. the stress/energy form is positive;
4. the boundary S-matrix is unitary;
5. the map induces `(c,t)->(-c,-t)` on the microscopic orientation data;
6. there is no additional independent interior Hilbert space.

Only after these are proved should the statement "nothing crosses the horizon" be made as a
field-theoretic theorem rather than an interpretation.

## Arithmetic-field-theory clues

The recent arithmetic-principal-series programme contains four structures that now look
highly relevant.

### 1. Reflection-odd first-order generator, positive square

The arithmetic OS/reflection-positive formulation already isolates

    Theta D Theta^{-1} = -D,
    H = D^2 >= 0,
    Theta H Theta^{-1} = H.

This is almost exactly the desired microscopic-time architecture: orientation/frequency is
odd, physical energy is positive and even.  It is stronger than the old signed-energy
picture and should be imported into the matter paper as the preferred operator template.

### 2. Hilbert reciprocity: local sign defects require global compensation

For quadratic Hilbert symbols over a global field,

    product_v (a,b)_v = 1.

Thus a single isolated local `-1` defect cannot occur; nontrivial local signs must be
compensated globally.  This is mathematically independent of the charge-transfer argument,
but it has exactly the same shape.

The possible physics dictionary is:

    local half flip  <-> local quadratic defect,
    complete CPT/global constraint <-> reciprocity product law.

If this dictionary can be realized by an actual adelic/gauge construction, it would explain
why an isolated orientation half flip is forbidden while paired/boundary-compensated flips
are allowed.  At present this is a structural clue, not a physical theorem.

### 3. Hodge--Koszul bulk acyclicity: physical content can be boundary cohomology

In the arithmetic finite-prime construction, the multiplicative occupation bulk is a
fermionic/Koszul complex with a positive Hodge--Dirac operator.  Locally it is acyclic: the
prime occupation states pair and cancel in cohomology.  Nontrivial physical modes can only
appear when the global Archimedean boundary condition prevents the contracting homotopy
from extending.

That suggests a potentially powerful cosmological principle:

> **Matter-as-boundary-cohomology hypothesis.**  A CPT-paired bulk is locally paired and
> cohomologically trivial.  Net relational matter is an unpaired boundary cohomology/index
> associated with the Big Bang and, in reverse, black-hole horizons.

The natural continuum object is a graded Dirac operator on the two-sheet spacetime.  The
candidate observable would be

    N_M - N_A  ?=  ind D_orient

or its APS/eta-invariant refinement.  This would turn the matter asymmetry from a thermal
accident into an index/boundary problem.

### 4. Local Euler channels are individually too rich; the physical modes must be global

The arithmetic programme proves that each finite local prime shadow factor admits an exact
unitary doubled realization, but independent products have far too many periodic modes.
The correct spectrum can only arise after a genuinely global prime--Archimedean coupling.

The lesson for the orientation programme is important: **do not build the Universe as an
independent tensor product of microscopic two-sheet particles.**  The many-body no-go found
earlier says the same thing in a different language.  A single global gluing/constraint is
needed to remove the spurious relative orientation bits and produce collective physical
modes.

This convergence of two independent calculations is currently one of the strongest clues:

    local doubled systems are easy;
    the physical theory is in the global gluing.

## New closed-cycle picture to test

The working model now has a coherent possible cycle:

1. **Big Bang:** a CPT branch/gluing surface creates correlated pairs
   `(R,+)` and `(R*,-)`.  Conventional charges cancel globally; relational matter signs
   agree.  A boundary Dirac index/spectral flow may set the nonzero sheetwise fermion
   asymmetry.
2. **Bulk universe:** each sheet has ordinary positive energy and the same thermodynamic
   future away from the low-entropy boundary.  Laboratory antiparticles are local half-flip
   excitations relative to a fixed sheet, not the primordial mirror sheet itself.
3. **Black-hole horizon:** the two orientation representatives are glued again.  Paired
   oriented fermion/charge flux cancels while energy adds.  A valid boundary interaction
   could convert the pair into neutral horizon/radiative degrees of freedom.
4. **Global accounting:** conventional C-odd charges cancel over the full doubled geometry;
   orientation-weighted relational charges/indexes need not.  Arithmetic reciprocity and
   boundary cohomology provide candidate mathematical models for this local/global split.

The striking possibility is that Bang and horizon are the two operations of the same
orientation functor: the Bang is pair creation/splitting of a CPT-correlated state into two
sheets; a black-hole horizon is pair recombination/gluing.

## Immediate theorem targets

1. Build the actual chiral Dirac index orientation-reversal theorem and APS boundary version
   for the two-sheet manifold.
2. Couple the index to the electroweak anomaly and test whether an oriented `B-L` or another
   representation charge is the correct conserved relational quantity.
3. Construct the horizon Dirac self-adjoint boundary condition and prove zero quotient
   normal current with positive energy.
4. Determine whether the Big-Bang branch condition forces a nonzero index or merely permits
   one.  If it merely permits it, the framework has not yet explained the magnitude of
   matter.
5. Build an adelic/quadratic-character version of the orientation Z2 and test whether Hilbert
   reciprocity becomes an actual gauge-selection law rather than an analogy.
6. Only after these steps ask for the observed baryon-to-photon ratio.  Avoid fitting a small
   number before the integer/topological mechanism is fixed.

## Current status

The new Lean files added in this pass are:

- `CPTSymmetryDoesNotForceAntimatter.lean`
- `RelationalMatterSelectionRule.lean`
- `CPTSheetRelationalCharge.lean`
- `RepresentationConjugacyVsElectricSign.lean`
- `ArithmeticReciprocityOrientationParity.lean`
- `CPTOrientedIndexPair.lean`
- `CPTSheetElectroweakAnomalyBookkeeping.lean`

They formalize the finite algebra only.  The index theorem, electroweak anomaly itself,
curved horizon boundary problem, and adelic reciprocity dictionary remain the hard analytic
bridges.
