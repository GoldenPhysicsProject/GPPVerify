# Orientation, matter origin, horizons, and arithmetic reciprocity — 2026-09-09

## Executive result

The current orientation programme has reached a sharper statement than the original
`q*t` mnemonic.

1. The first microscopic sign must be **representation-conjugacy orientation**, not the
   numerical sign of electric charge. Ordinary matter already contains both electric signs
   (proton-like and electron-like species). For a species with reference representation `R`
   and charge vector `q0`, a conjugacy sign `c=+/-1` distinguishes `R` from `R*` and sends
   the whole internal charge vector to its conjugate.
2. The second sign is the microscopic temporal/phase/sheet orientation `t=+/-1`, distinct
   from coordinate time and from the thermodynamic arrow.
3. The candidate relational matter character is

       chi = c t.

   A complete diagonal reversal `(c,t)->(-c,-t)` preserves `chi`; either half flip changes
   it.
4. Exact finite algebra now proves that diagonal CPT/deck invariance **does not require a
   matter/antimatter balance**. The diagonal-even subspace contains independent `chi=+`
   and `chi=-` sectors. In particular the pure matter lift

       |M> ~ |++> + |-->

   is already diagonal invariant. Thus, if physical CPT is realized by the diagonal
   orientation involution, a globally CPT-symmetric state can lie entirely in the
   relational-matter sector.
5. A `chi`-even dynamics cannot convert a `chi=+1` one-particle state into `chi=-1`.
   Anti-aligned excitations require a `chi`-odd interaction/defect, or a many-body process
   with compensation elsewhere. This is the exact form of the intuition that it is hard to
   obtain `+-` from an initially aligned `++/--` configuration.

The crucial caveat is equally sharp: physical CPT has not yet been proved to equal the
project's diagonal deck operation, and the Standard Model does create laboratory
antiparticles. The claim under investigation is therefore **not** that antimatter
excitations are impossible. It is that primordial global CPT symmetry need not mean a
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
representatives of the same **relational matter class**. From one sheet the partner is
called the antiparticle because its internal representation is conjugate. Relative to its
own reversed microscopic orientation, however, it is matter.

This gives a concrete replacement for the phrase "half the Big Bang was antimatter":

    vacuum/boundary -> (R,+) + (R*,-)

is globally charge-conserving and CPT-paired, but both outputs have `chi=+`.

### Exact two-mode creation mechanism

The statement above can be made as an honest finite Fock-space mechanism rather than a
verbal relabelling. In the two-sheet basis

    |00>, |10>, |01>, |11>,

let `|10>` be relational matter on sheet + and `|01>` relational matter on sheet -. Relative
to one external convention they have opposite conventional charge. Define

    Q_conv = N_+ - N_-,
    N_rel  = N_+ + N_-.

A cross-sheet pair creator

    P^dagger : |00> -> |11>

commutes exactly with `Q_conv`, commutes with sheet exchange, but obeys

    [N_rel,P^dagger] = 2 P^dagger.

So an exactly sheet/CPT-symmetric and conventionally neutral interaction can create two
relational-matter quanta directly from the vacuum. No local half flip is needed and there is
no electric-charge bookkeeping crisis. This is now formalized in
`CPTPairCreationFromVacuum.lean`.

This mechanism removes the logical requirement for a primordial relational-antimatter
reservoir. It does **not** yet determine the cosmological mode functions, species spectrum,
production rate, or the observed baryon-to-photon ratio.

## Baryon and lepton number: the index route and its obstruction

The matter-antimatter cosmological problem is not primarily the sign of electric charge.
The robust observables are baryon/lepton asymmetries, while the Universe remains extremely
electrically neutral. Electroweak topology provides an existing exact bridge between
fermion number and a chiral index/spectral flow.

For electroweak topological index `k` and `N_g` generations,

    Delta B = N_g k,
    Delta L = N_g k,
    Delta(B-L) = 0,
    Delta(B+L) = 2 N_g k.

Orientation reversal exchanges chiralities and reverses the chiral Dirac index, so a
CPT-mirror sheet naturally carries `-k`. Therefore

    Delta B_+ + Delta B_- = 0,

but with sheet signs `t_+=+1`, `t_-=-1`,

    t_+ Delta B_+ + t_- Delta B_- = 2 Delta B_+.

The same holds for lepton number. This motivates the **oriented-index hypothesis**

    I_rel = t ind(D).

However, a serious obstruction appears immediately: the electroweak index alone has

    Delta(B-L)=0.

Therefore it cannot generate a nonzero B-L seed from zero. In an ordinary hot electroweak
history a pure B+L source is vulnerable to sphaleron washout unless an additional source,
nonstandard history, or protected nonequilibrium mechanism is present. The current
orientation programme must not hide this.

A particularly natural extra channel is a neutral-fermion/Majorana boundary sector. A
same-field conjugacy-mixing term carries twice the fermion's Abelian charge and is gauge
neutral only when that charge vanishes (or when a compensating charge-`-2q` field participates).
Thus neutral fermions are the one place where a direct conjugacy half flip can occur without
an electromagnetic obstruction. If such a boundary interaction supplies lepton-number
change `ell`, then algebraically

    B-L = -ell

while the electroweak index still controls B+L redistribution. This gives a concrete chain
to investigate:

    neutral boundary L/B-L source -> electroweak spectral flow -> sheetwise baryon excess.

The files `MajoranaHalfFlipNeutralPortal.lean` and `ElectroweakIndexBLObstruction.lean`
formalize the finite charge bookkeeping. They do not establish the cosmological dynamics.

## Horizon: no interior crossing in the quotient sense

The existing `HorizonCPTFluxGluing.lean` sign theorem gives the right boundary bookkeeping.
Under

    (q,u,n) -> (-q,-u,-n),

where `q` is internal conjugacy/charge orientation, `u` oriented worldline flow and `n` the
oriented hypersurface normal,

    j = q u

is unchanged, but its oriented normal flux reverses. Hence paired fluxes cancel:

    Phi_Q^+ + Phi_Q^- = 0.

Quadratic stress is even, so energy flux instead adds:

    Phi_E^+ + Phi_E^- = 2 Phi_E^+.

This is exactly the sign pattern needed for a horizon which is a **fermion/current gluing
surface rather than a conduit to an independent interior**: no net oriented charge/fermion
flux crosses the quotient, while positive energy remains available to be converted into
neutral radiation.

The black-mirror geometry provides a concrete spacetime carrier for this idea: its horizon
is the boundary between two CPT-related exteriors and the model explicitly proposes that
infalling CPT-paired particle/antiparticle trajectories meet there and annihilate. The GPP
extension is to interpret those two trajectories as the two orientation representatives of
one relational fermionic state, if a spin/gauge bundle intertwiner can actually be built.

There is now also an exact finite boundary-form criterion. If the doubled Dirac boundary
spinors obey

    psi_- = U psi_+

and `G` is the normal Clifford/current matrix on the + side, opposite outward normals make
the total Green boundary coefficient

    G - U^dagger G U.

Therefore

    U^dagger G U = G

is a sufficient algebraic condition for exact cancellation of the two boundary forms and of
net quotient normal fermion flux. This is formalized in
`DoubledDiracBoundaryGluingCriterion.lean`. The full self-adjoint Sobolev/domain theorem on
the curved horizon remains open.

The hard theorem is now precise. Construct a two-sheet Dirac bundle and boundary map

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

The current arithmetic-principal-series programme contains several structures which now
look directly relevant.

### 1. Reflection-odd first-order generator, positive square

The arithmetic OS/reflection-positive formulation isolates

    Theta D Theta^{-1} = -D,
    H = D^2 >= 0,
    Theta H Theta^{-1} = H.

This is almost exactly the desired microscopic-time architecture: orientation/frequency is
odd, physical energy is positive and even. It is stronger than the old signed-energy picture
and should be the preferred operator template for the orientation programme.

### 2. Exact co-Poisson diagonal duality

On the arithmetic test space the exact boundary identity is

    P = I P C,
    I P = P C,

where `P` is arithmetic summation, `C` is the Archimedean cosine/Fourier involution and `I`
is multiplicative inversion. This is not analogy: the source-side dualization and the
output-side inversion are exactly intertwined, and applying the two half operations together
leaves the synthesized arithmetic object unchanged.

Abstractly this has the same algebraic shape as the orientation proposal:

    internal half duality + geometric/time half duality = diagonal invariance.

The physical dictionary is not yet proved. `ArithmeticCoPoissonOrientationTemplate.lean`
formalizes the general intertwining consequence so that any future physics map has a sharp
target.

### 3. Hilbert reciprocity: local sign defects require global compensation

For quadratic Hilbert symbols over a global field,

    product_v (a,b)_v = 1.

Thus a single isolated `-1` defect cannot occur; nontrivial local signs must be compensated
globally. This is mathematically independent of the charge-transfer argument, but it has
exactly the same shape.

The possible physics dictionary is:

    local half flip  <-> local quadratic defect,
    complete CPT/global constraint <-> reciprocity product law.

If this dictionary can be realized by an actual adelic/gauge construction, it would explain
why an isolated orientation half flip is forbidden while paired/boundary-compensated flips
are allowed. At present this is a structural clue, not a physical theorem.

### 4. Hodge--Koszul bulk acyclicity: physical content can be boundary cohomology

In the arithmetic finite-prime construction, the multiplicative occupation bulk is a
fermionic/Koszul complex with a positive Hodge--Dirac operator. Locally it is acyclic: the
prime occupation states pair and cancel in cohomology. Nontrivial physical modes can only
appear when the global Archimedean boundary condition prevents the contracting homotopy
from extending.

That suggests a potentially powerful cosmological principle:

> **Matter-as-boundary-cohomology hypothesis.** A CPT-paired bulk is locally paired and
> cohomologically trivial. Net relational matter is an unpaired boundary cohomology/index
> associated with the Big Bang and, in reverse, black-hole horizons.

The natural continuum object is a graded Dirac operator on the two-sheet spacetime. The
candidate observable would be

    N_M - N_A  ?=  ind D_orient

or its APS/eta-invariant refinement. This would turn the matter asymmetry from a thermal
accident into an index/boundary problem.

### 5. Local Euler channels are individually too rich; the physical modes must be global

The arithmetic programme proves that each finite local prime shadow factor admits an exact
unitary doubled realization, but independent products have far too many periodic modes. The
correct spectrum can only arise after a genuinely global prime--Archimedean coupling.

The lesson for the orientation programme is important: **do not build the Universe as an
independent tensor product of microscopic two-sheet particles.** The many-body no-go found
earlier says the same thing in a different language. A single global gluing/constraint is
needed to remove the spurious relative orientation bits and produce collective physical
modes.

This convergence of two independent calculations is currently one of the strongest clues:

    local doubled systems are easy;
    the physical theory is in the global gluing.

### 6. The dyadic place is the unique equal-weight arithmetic shadow channel

The local Euler-shadow colligation has squared channel weights

    a_p^2 = 1/p,
    b_p^2 = 1 - 1/p.

Equal weighting forces

    1/p = 1 - 1/p,

hence uniquely

    p = 2.

At the dyadic place,

    a_2 = b_2 = 1/sqrt(2)

for the positive choice, and the local channel is

    S_2 = (1/sqrt(2)) [[1,1],[1,-1]],

exactly the normalized Hadamard/Z2 Fourier matrix independently appearing in the orientation
Haar average and the Dirac two-state basis change. `DyadicOrientationHadamardBridge.lean`
formalizes the uniqueness and matrix identity.

This is not yet permission to declare "prime 2 is time orientation." The non-fitted fact is
narrower and more interesting: **the unique prime whose local arithmetic shadow splits into
two equal channels is exactly the prime whose colligation is the binary orientation Fourier
transform.** The next test is whether the quadratic/dyadic Hilbert-symbol sector realizes
the actual orientation double cover.

## New closed-cycle picture to test

The working model now has a coherent possible cycle:

1. **Big Bang:** a CPT branch/gluing surface creates correlated pairs
   `(R,+)` and `(R*,-)` through a cross-sheet pair-creation channel. Conventional charges
   cancel globally; relational matter signs agree. A boundary Dirac index/cohomology or
   neutral-fermion source may fix the nonzero sheetwise fermion/B-L datum.
2. **Bulk universe:** each sheet has ordinary positive energy and the same thermodynamic
   future away from the low-entropy boundary. Laboratory antiparticles are local half-flip
   excitations relative to a fixed sheet, not the primordial mirror sheet itself.
3. **Black-hole horizon:** the two orientation representatives are glued again. Paired
   oriented fermion/charge flux cancels while energy adds. A valid boundary interaction
   could convert the pair into neutral horizon/radiative degrees of freedom.
4. **Global accounting:** conventional C-odd charges cancel over the full doubled geometry;
   orientation-weighted relational charges/indexes need not. Arithmetic reciprocity,
   co-Poisson duality and boundary cohomology provide candidate mathematical models for this
   local/global split.

The striking possibility is that Bang and horizon are the two operations of the same
orientation functor: the Bang is pair creation/splitting of a CPT-correlated state into two
sheets; a black-hole horizon is pair recombination/gluing.

## Immediate theorem targets

1. Build the actual chiral Dirac index orientation-reversal theorem and APS boundary version
   for the two-sheet manifold.
2. Determine whether the Big-Bang gluing condition forces a nonzero boundary index or merely
   permits one. If it merely permits it, the framework has not yet explained the magnitude
   of matter.
3. Test the neutral-fermion/Majorana boundary channel as a genuine B-L source and then couple
   it to electroweak sphaleron redistribution without importing a fitted asymmetry.
4. Construct the curved horizon Dirac self-adjoint boundary condition and prove zero quotient
   normal current with positive energy.
5. Build an adelic/quadratic-character version of the orientation Z2 and test whether Hilbert
   reciprocity becomes an actual gauge-selection law rather than an analogy.
6. Test whether the dyadic `p=2` Hadamard channel is the local manifestation of that quadratic
   orientation character or merely a binary coincidence.
7. Only after these steps ask for the observed baryon-to-photon ratio. Avoid fitting a small
   number before the integer/topological mechanism is fixed.

## Current status

New Lean files added in this research pass include:

- `CPTSymmetryDoesNotForceAntimatter.lean`
- `RelationalMatterSelectionRule.lean`
- `CPTSheetRelationalCharge.lean`
- `RepresentationConjugacyVsElectricSign.lean`
- `ArithmeticReciprocityOrientationParity.lean`
- `CPTOrientedIndexPair.lean`
- `CPTSheetElectroweakAnomalyBookkeeping.lean`
- `DoubledDiracBoundaryGluingCriterion.lean`
- `MajoranaHalfFlipNeutralPortal.lean`
- `ArithmeticCoPoissonOrientationTemplate.lean`
- `DyadicOrientationHadamardBridge.lean`
- `CPTPairCreationFromVacuum.lean`
- `ElectroweakIndexBLObstruction.lean`

They formalize finite/exact algebraic cores only. The actual curved index theorem, anomaly
dynamics, cosmological production rate, horizon domain theorem and adelic orientation
dictionary remain the hard analytic bridges.
