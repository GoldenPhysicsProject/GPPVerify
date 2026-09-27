# Nyman--Burnol / metaplectic defect attack

Date: 2026-09-12

## Starting point

The current arithmetic manuscript has an exact zero-independent Hilbert-space model of the
bad-zero sector. Under the Mellin identification

    X = L^2((0,1),du)  ~=  H^2(Re s > 1/2),

the closed Nyman--Burnol span `N` has transform

    N^ = B H^2,

where `B` is the Blaschke product of zeta zeros with `Re rho > 1/2`. Consequently

    X/N  ~=  H^2 \ominus B H^2 = K_B,

and

    RH  <=>  B is constant  <=>  N^ = H^2  <=>  K_B = 0.

The quotient `K_B` is the exact Hardy ghost space.

## Correction: the naive internal reflection theorem is impossible

An earlier version proposed constructing a bijective unitary or antiunitary `J` on the
single positive Hardy polarization with

    J S J^{-1} = S*,

where `S` is the multiplicity-one unilateral shift. This cannot happen.

Indeed

    ker S = {0},
    dim ker S* = 1.

Conjugation by any bijection preserves kernel dimension, so `S` and `S*` cannot be similar
or antiunitarily conjugate on the same ambient Hardy space.

This kills the naive internal-Hardy version of the metaplectic reflection. The physically
correct doubled picture is instead that reflection exchanges incoming and outgoing Hardy /
Lax--Phillips polarizations. The RH problem is then whether the arithmetic physical quotient
is causal/positive after that doubling. Burnol's adelic Lax--Phillips construction reaches
exactly this wall: global causality is equivalent to RH, so merely writing the doubled
reflection does not prove anything.

## A second no-go: every nonzero ghost model space already has its own reflection

There is an even sharper warning from standard Hardy model-space theory. For every inner
function `B`, including every nonconstant bad-zero Blaschke product, the model space

    K_B = H^2 \ominus B H^2

carries a canonical conjugation `C_B`. If

    S_B = P_{K_B} S |_{K_B}

is the compressed shift, then

    C_B S_B C_B = S_B*.

Thus a forward/backward reflection on the *ghost quotient itself* exists automatically even
when `K_B` is nonzero. Quotient-level reflection symmetry therefore cannot eliminate the
ghost sector. This is the infinite-dimensional theorem mirrored by the finite Lean module

    GppVerify/RiemannHypothesis/FiniteModelSpaceReflectionNoGo.lean.

That module proves on a two-state carrier that an involutive reflection can exchange forward
and backward nilpotent shifts while two nonzero rank-one boundary defects survive.

The target must therefore be stronger than reflected symmetry. It must annihilate the
boundary defect or lift the reflection to an ambient causal statement that rules the defect
out.

## The exact rank-one ghost defect

The compressed shift on `K_B` carries the standard rank-one defect identities

    I - S_B S_B* = k_0^B \otimes k_0^B,
    I - S_B* S_B = \widetilde k_0^B \otimes \widetilde k_0^B,

with `\widetilde k_0^B = C_B k_0^B` and, in the disk normalization,

    k_0^B(z) = 1 - overline(B(0)) B(z),
    ||k_0^B||^2 = 1 - |B(0)|^2.

So the reflection swaps the two defect directions; it does not kill them.

This gives a sharper exact RH target:

    RH  <=>  k_0^B = 0
        <=>  I - S_B S_B* = 0
        <=>  I - S_B* S_B = 0.

For a nonconstant inner `B`, the defect vector is nonzero. When `B` is constant unimodular,
`K_B=0` and the defect vanishes trivially.

## Why the distinguished point is exactly Burnol's Nyman product

Use the Cayley coordinate taking the critical half-plane to the unit disk and the physical
anchor `s=1` to the disk origin:

    z = (s-1)/s = 1 - 1/s.

A bad zero `rho` with `Re rho > 1/2` is sent to

    beta_rho = 1 - 1/rho,

and

    |beta_rho| < 1

because

    |rho|^2 - |rho-1|^2 = 2 Re(rho) - 1 > 0.

Therefore the disk Blaschke product satisfies, up to its irrelevant unimodular phase,

    |B(0)|
      = product_{Re rho > 1/2} |beta_rho|^{m_rho}
      = product_{Re rho > 1/2} |1 - 1/rho|^{m_rho}.

This is precisely the product that appears in Burnol's quantitative refinement of the
Nyman--Beurling criterion. In the corresponding normalized Hardy convention it is the norm
of the projection of the distinguished vacuum/kernel vector onto the Nyman subspace.
Hence

    ghost leakage^2
      = ||P_{K_B} 1||^2
      = 1 - |B(0)|^2
      = 1 - product_{Re rho > 1/2} |1 - 1/rho|^{2m_rho}.

Thus RH is equivalent to **one scalar saturation law**:

    ||P_N 1|| = 1,

or equivalently

    ||P_{K_B}1|| = 0.

This does not make RH easy, but it changes the operator target. We do not need a fictional
internal conjugacy of the unilateral shift. We need a zero-independent arithmetic mechanism
which proves that no norm leaks from the distinguished vacuum into the model-space defect.

## Finite-dimensional determinant interpretation

For a finite Blaschke product with zeros `beta_j`, the compressed shift has eigenvalues
(conjugates of) the `beta_j`, and therefore

    |det S_B| = product_j |beta_j| = |B(0)|.

The Burnol/Nyman projection product is consequently the finite ghost transfer determinant.
Every nontrivial ghost factor makes it strictly contractive:

    |det S_B| < 1.

RH corresponds to saturation at unit modulus only because the ghost space has disappeared.
This provides the right physical reading: reflection can pair the two boundary defects, but
a no-loss/no-ghost theorem must force the contraction defect itself to vanish.

## Relation to the current arithmetic heat/causality program

This rank-one model-space defect fits the structures already proved in the arithmetic
manuscript:

1. The shifted transfer `Theta_a` is boundary-unimodular unconditionally, but off-line zeros
   contribute a Blaschke denominator and a negative model-space kernel.
2. Burnol's adelic scattering supplies the doubled incoming/outgoing system, but its global
   causality is equivalent to RH.
3. The zero-independent heat function `K(t)` has OS positivity exactly under RH.
4. The causal Dirichlet heat construction produces exact prime boundary commutator traces,
   but the all-prime/Archimedean limit still permits escaped trace.
5. The Nyman--Burnol quotient identifies the escaped/odd sector exactly as `K_B`.

The new compression is therefore:

    global RH obstruction
      = nonzero model-space boundary defect
      = nonzero vacuum leakage ||P_{K_B}1||
      = 1 - |B(0)|^2.

The metaplectic/Fourier reflection remains useful only if it supplies an **ambient no-loss
identity** strong enough to prove this scalar defect vanishes. Reflection internal to `K_B`
is automatic and carries no RH information.

## Revised hard theorem

The strongest economical target is now a vacuum-saturation / no-escaped-norm theorem,
proved from zero-independent Tate--Poisson and prime--Archimedean data:

    ||P_N 1|| = 1.

Equivalent forms are

    P_{K_B}1 = 0,
    k_0^B = 0,
    B is constant,
    K_B = 0,
    RH.

A stronger but still valid route is to prove the full arithmetic OS/causality theorem. The
single-vector saturation formulation is preferable for experimentation because any proposed
positivity or conservation law can be tested directly against one distinguished state.

## What will not count as closure

The following are now explicitly ruled out as proof mechanisms by themselves:

* functional-equation pairing;
* boundary unimodularity;
* metaplectic/Fourier reflection alone;
* canonical conjugation of the compressed ghost shift;
* positivity of an ambient Hilbert metric;
* a doubled Krein-unitary realization;
* finite-place positivity without a global no-loss estimate.

All of these can coexist with a nonzero `K_B`.

The remaining theorem is genuinely a **no boundary leakage** statement.
