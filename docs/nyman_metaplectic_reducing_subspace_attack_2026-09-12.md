# Nyman--Burnol / metaplectic reducing-subspace attack

Date: 2026-09-12

## Starting point

The current arithmetic manuscript has an exact zero-independent Hilbert-space model of the
bad-zero sector.  Under the Mellin identification

    X = L^2((0,1),du)  ~=  H^2(Re s > 1/2),

the closed Nyman--Burnol span `N` is

    N^ = B H^2,

where `B` is the Blaschke product of zeta zeros with `Re rho > 1/2`.
Consequently

    X/N  ~=  H^2 \ominus B H^2 = K_B,

and

    RH  <=>  B is constant  <=>  N^ = H^2  <=>  K_B = 0.

The Nyman space is already invariant under the forward contraction/shift semigroup.  The
new question suggested by the metaplectic orientation picture is whether global
Poisson/Fourier duality can supply the *adjoint* invariance.

## Elementary operator reduction

For the multiplicity-one unilateral shift `S` on scalar Hardy space, the only reducing
subspaces are `0` and the whole Hardy space.  Therefore:

> If the nonzero Nyman--Burnol subspace `B H^2` were invariant under both `S` and `S*`, then
> it would reduce the unilateral shift.  Hence `B H^2 = H^2`, so `B` is constant and RH
> follows.

Thus a sufficient theorem is

    S* (B H^2) subset B H^2.

Equivalently, it would suffice to construct an arithmetic unitary or antiunitary `J` on the
physical Hardy boundary satisfying

    J (B H^2) = B H^2,
    J S J^{-1} = S*,

because forward invariance would then imply backward invariance.

This is an operator-theoretic version of the project's diagonal-duality idea: one half of
the structure supplies the causal/forward semigroup, the dual half must return its adjoint.
If both descend to the same physical quotient, the bad-zero invariant subspace has no room
to remain proper.

## Why ordinary functional-equation symmetry does not already do this

The shadow/functional-equation reflection exchanges the two Hardy half-planes.  It does not
by itself act as an internal adjoint symmetry of the positive Hardy space.  Consequently one
cannot simply set `J=Fourier` and claim the theorem: that would hide exactly the global
causality/OS-positivity step equivalent to RH.

This is the same separation already seen elsewhere:

    boundary unitarity != reflection positivity,
    forward invariance != reducing invariance,
    functional-equation pairing != no-ghost theorem.

The finite no-go `PositiveSquareOddSectorNoGo.lean` is the two-state version of the same
warning.

## Metaplectic candidate mechanism

The semilocal Connes--Consani--Moscovici cyclic pair has

    F_S D_S = -D_S F_S,

with Fourier acting as spectral reflection and the cyclic spectral density

    dmu_S(t) = | product_{v in S} L_v(1/2-it) |^2 dt.

For every finite set of places this is a genuine positive even cyclic pair.  The full Weil
representation gives the natural double-cover/Fourier structure.  The desired global `J`
would have to survive the all-place Tate quotient and, after the OS/Hardy polarization,
turn the forward semigroup into its adjoint *without leaving the physical quotient*.

That last phrase is the whole problem.  The present arithmetic manuscript proves that local
Euler homotopies leave the global Poisson domain and that bilateral Gaussian smoothing
breaks Tate causality.  Hence `J` cannot be assembled as an identity tensor product of local
prime operations.  It must be a genuinely global Poisson/scattering operator.

## Normal-derivative bridge from semilocal positive measures to the Weil prime term

There is an exact local relation which makes the target more concrete.  For

    L_p(s) = (1-p^{-s})^{-1},
    R_p(sigma,t) = |L_p(sigma-it)|^2,

logarithmic differentiation gives

    - d/dsigma log R_p(sigma,t)
      = 2 sum_{m>=1} (log p) p^{-m sigma} cos(m t log p).

At `sigma=1/2`,

    - d/dsigma log R_p |_(1/2)
      = 2 sum_{m>=1} Lambda(p^m) p^{-m/2} cos(m t log p),

which is exactly the symmetric Fourier transform of the local prime-power measure in the
Weil explicit formula.

Equivalently, with `r=p^{-1/2}` and `theta=t log p`,

    |L_p(1/2-it)|^2
      = 1/(1-2r cos theta+r^2)
      = P_r(theta)/(1-r^2),

where `P_r` is the positive Poisson kernel.  Thus the local Weil prime distribution is the
normal/logarithmic derivative of a positive semilocal Plancherel density.

This explains both the promise and the obstruction:

* every finite local spectral measure is positive;
* the Weil form is a boundary derivative/compression of those measures, not the measures
  themselves;
* positivity of a measure does not imply positivity of its normal derivative;
* the missing global theorem is a convexity/causality/reflection statement for the
  all-place boundary flow.

## A sharper contraction formulation

The desired global reflection positivity can be expressed as a frame contraction.  Seek
feature maps

    V_infty : test -> H_infty,
    V_p     : test -> H_p

and a nonlocal arithmetic map `T` such that

    V_p = T V_infty,
    ||T|| <= 1.

Then

    Q_Weil(f)
      = ||V_infty f||^2 - ||V_p f||^2
      = <V_infty f,(1-T* T)V_infty f>
      >= 0.

The ultraviolet support obstruction in the current manuscript rules out local/identity
choices of `T`; Burnol's global scattering and the adelic Weil/metaplectic representation
are the natural nonlocal carriers.

## Hard theorem now isolated

A particularly sharp route to RH is therefore one of the following equivalent-strength
statements, proved from zero-independent arithmetic data:

1. the Nyman--Burnol subspace is invariant under the adjoint Hardy shift;
2. a global metaplectic/Poisson reflection `J` preserves the Nyman subspace and conjugates
   forward shift to backward shift;
3. the arithmetic scattering transfer is causal/inner;
4. the prime feature map is a contraction of the real-place feature map;
5. the Gaussian heat kernel `K(s+t)` has a positive Hilbert Gram factorization.

The first formulation is useful because its final step is completely elementary operator
theory: a nonzero reducing subspace of the simple unilateral shift must be the whole space.
All of the difficulty is therefore concentrated into one explicit global duality-invariance
statement.

## Status

This is a research reduction, not a proof of the missing duality-invariance statement.  It
should be used to test proposed metaplectic/Poisson constructions: if a candidate `J` does
not genuinely preserve the Nyman physical subspace while conjugating the causal semigroup to
its adjoint, it has not crossed the RH wall.
