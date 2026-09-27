# Metaplectic dilation, spinorial order four, and the Weil-positivity RH target

Date: 2026-09-12

## Executive result

The spin/orientation discussion leads to an exact arithmetic operator architecture, but it
also identifies the precise theorem that is still missing.

On `L^2(R)` the centered self-adjoint dilation generator is

    A = -i (x d/dx + 1/2).

The `1/2` is the half-density correction required for unitary dilation.  For the unitary
Fourier transform `F`,

    F A F^{-1} = -A,

while

    H = A^2 >= 0,
    F H F^{-1} = H.

On the full Fourier carrier,

    F^2 = parity,
    F^4 = 1.

Hence on the odd-parity sector `F^2=-1`, giving the same order-four algebra already found
in the Grassmannian/spin lift:

    quarter-turn^2 = -1,
    quarter-turn^4 = 1.

This is a genuine metaplectic/Weil-representation structure, not an analogy.  It does NOT
identify the metaplectic double cover with the physical spin group; they are different
double covers sharing the same order-four lifting mechanism.

The half-density Mellin character

    chi_s(a) = exp(log(a)(s-1/2))

has unit modulus for every positive dilation exactly on

    Re(s)=1/2.

Thus the critical line is exactly the unitary half-density axis for multiplicative scaling.
This fact was already formalized in `ScaleMassDiagnostic.lean` and
`ScaleShadowHalfDensity.lean`; the new point is that the same `1/2` is the metaplectic
half-form correction in the centered dilation generator.

## Collision with existing spectral-number-theory machinery

Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators* (2024), already build
precisely the relevant finite/semilocal cyclic-pair structure.  For a finite set of places
`S` containing infinity they have a self-adjoint scaling generator `S`, cyclic vector
`xi_S`, and Fourier grading `F_S` with

    F_S S = - S F_S.

In canonical spectral coordinates the cyclic measure is

    d mu_S(t) = | product_{v in S} L_v(1/2-it) |^2 dt

(up to their fixed normalization), and Fourier becomes reflection `t -> -t`.  They further
relate the prolate operator to the metaplectic representation of the double cover of
`SL(2,R)`.  Thus the metaplectic/scaling/Fourier spine is established machinery and is a
strong collision check for the present synthesis.

What is NOT established there, and what remains the same wall as in the current GPP
arithmetic programme, is the global all-place positivity needed to force RH.

## Exact local prime observation

For a finite prime `p`, put

    r = p^{-1/2},
    theta = t log p.

Then on the critical axis

    |L_p(1/2-it)|^2
      = 1 / (1 - 2 r cos(theta) + r^2)
      = P_r(theta)/(1-r^2),

where

    P_r(theta) = (1-r^2)/(1-2r cos(theta)+r^2)

is the positive Poisson kernel.  Its Fourier series is

    P_r(theta) = 1 + 2 sum_{m>=1} r^m cos(m theta).

Therefore

    (log p)(P_r(theta)-1)
      = 2 sum_{m>=1} Lambda(p^m) p^{-m/2} cos(m t log p).

So the local prime-power contribution to the explicit formula is the nonconstant Fourier
part of a positive Poisson kernel.  This gives a concrete bridge between the semilocal
positive cyclic measure and the prime atoms of the Weil explicit formula.

However, local positive type is not enough.  The completed global heat trace is built from

    W = nu_infty - nu_p,

and the current arithmetic manuscript proves an ultraviolet support obstruction: identity
or positive local Mellin gluing remains indefinite on a prime-free interval below `log 2`.
Any successful proof therefore requires a genuinely nonlocal Poisson/scattering boundary
map.

Fourier/metaplectic transformation is exactly such a nonlocal operation, which makes it a
natural structural candidate, but its existence/unitarity alone does not imply the needed
OS positivity.

## The RH positivity target in its sharp form

The current arithmetic programme defines the completed prime--Archimedean heat trace

    K(t) = (4 pi t)^(-1/2) <W, exp(-x^2/(4t))>,  t>0,

and proves/reduces RH to the positivity hierarchy

    RH  <=>  K is completely monotone
        <=>  [ K(t_i+t_j) ]_{i,j} >= 0 for every finite positive-time set
        <=>  arithmetic Osterwalder--Schrader reflection positivity.

Thus the desired theorem is not another functional-equation or unitarity statement.  It is
an unconditional Hilbert-space Gram realization

    K(t) = <Omega_ar, exp(-t H) Omega_ar>,
    H >= 0,

or equivalently

    K(s+t)
      = < exp(-sH) Omega_ar, exp(-tH) Omega_ar >.

Then for every finite coefficient vector `c`,

    sum_{i,j} conj(c_i)c_j K(t_i+t_j)
      = || sum_i c_i exp(-t_i H) Omega_ar ||^2
      >= 0,

and the existing heat-trace/Weil criterion gives RH.

The finite sum-of-squares core of this mechanism is now formalized in
`RiemannHypothesis/FiniteHeatGramPositive.lean`.

## Stronger operator formulation: nonlocal frame contraction

A useful way to isolate the global theorem is to split the explicit-formula quadratic form
into real-place and arithmetic feature maps.  Schematically seek maps

    V_infty : test -> H_infty,
    V_p     : test -> H_p

such that

    Q_Weil(f) = ||V_infty f||^2 - ||V_p f||^2

(after the exact boundary/pole bookkeeping appropriate to the chosen completion).

A sufficient theorem would be a canonical nonlocal arithmetic operator `T` with

    V_p = T V_infty,
    ||T|| <= 1.

Then

    Q_Weil(f)
      = <V_infty f, (1-T* T) V_infty f>
      >= 0.

The program's ultraviolet support obstruction proves that `T` cannot be an identity/local
Euler gluing or any positive local Mellin average.  It must encode global Poisson/scattering
information.  Candidate carriers are Tate synthesis/co-Poisson, Burnol's adelic causal
scattering, or a global Weil/metaplectic compression analogous to the Connes--Consani Sonin
construction.

This `T`-contraction formulation is the concrete version of the phrase "the global gluing
is the physics" on the RH side.

## Hodge/no-ghost formulation and its exact limitation

The arithmetic manuscript also gives the sufficient Hodge theorem:

    K(t) = Str_H exp(-t L)

for a positive Z2-graded Hilbert complex, together with Hodge cancellation and cohomology
concentrated in even degree, implies RH.

The metaplectic/Fourier grading supplies a canonical candidate for the orientation grading,
and centered dilation supplies the reflection-odd first-order generator.  But this alone is
not enough.  A positive graded Hilbert space can have nonzero odd cohomology.

The smallest finite counterexample is now formalized in
`RiemannHypothesis/PositiveSquareOddSectorNoGo.lean`: `gamma^2=1`, `D^2=1`, and
`gamma D=-D gamma` coexist with a nonzero `gamma=-1` state.

Thus the spin/metaplectic positivity architecture supplies the correct operator skeleton,
but RH still requires the arithmetic no-ghost theorem.

The current manuscript identifies the ghost rigorously through the Nyman--Burnol cokernel:

    X/N  ~=  K_B,

where `B` is the Blaschke product of zeros with `Re rho > 1/2`.  RH is equivalent to
vanishing of this reduced odd cohomology.  The remaining theorem is therefore equivalent to
a coercive global Poisson gluing which kills this odd boundary sector without inserting zero
data.

## Elementary no-go: symmetry plus positivity is insufficient

The reciprocal polynomial

    P(w) = 2 w^2 + 5 w + 2
         = (2w+1)(w+2)

has positive coefficients and exact inversion symmetry

    w^2 P(1/w) = P(w),

but its zeros are

    -2, -1/2,

both off the unit circle.  This is formalized in
`RiemannHypothesis/ReciprocalPositivityNoGo.lean`.

So functional-equation symmetry plus elementary coefficient/state positivity cannot locate
zeros.  The needed positivity is the stronger reflected/Hankel/Weil Gram positivity.

## New formalized finite metaplectic core

`RiemannHypothesis/MetaplecticDilationReflectionCore.lean` proves the finite algebra

    J^2 = -1,
    J^4 = 1,
    J D = - D J,
    D^2 = 1,

and therefore `J` commutes with the positive square `D^2`.  This is the exact finite
quarter-turn / reflection-odd Dirac / positive-energy skeleton shared by the spinorial and
arithmetic pictures.

No analytic Fourier-domain theorem is claimed by that file.

## The sharpened research frontier

The most promising target is now:

**Arithmetic metaplectic OS factorization theorem.** Construct from zero-independent
Tate--Poisson / prime--Archimedean data a positive Hilbert space, a nonnegative self-adjoint
`H`, and a cyclic arithmetic boundary vector `Omega_ar` such that

    K(t) = <Omega_ar, exp(-tH) Omega_ar>

for the exact completed arithmetic heat trace `K`.

Equivalent formulations are:

1. prove every Gaussian semigroup Weil Gram matrix is positive;
2. construct the nonlocal prime-to-real-place contraction `T` above;
3. construct the global boundary Hilbert complex and prove its odd cohomology vanishes;
4. prove Burnol's global scattering transfer is causal/inner from an independent global
   arithmetic estimate;
5. prove the finite self-adjoint prime--Archimedean determinants converge compact-uniformly
   to centered xi while preserving real spectral zeros.

These are not five different miracles.  The current evidence says they are different
presentations of the same missing global positivity theorem.

The metaplectic discovery sharpens the architecture but does not remove that theorem.  The
next useful attack should therefore be on the *global nonlocal contraction/coercivity*, not
on another local Euler factor or another reformulation of the functional equation.

## Collision references

- A. Connes, C. Consani, H. Moscovici, "Zeta zeros and prolate wave operators: Semilocal
  adelic operators," Annals of Functional Analysis 15 (2024), Article 87.
- A. Connes, C. Consani, "Weil positivity and trace formula, the archimedean place,"
  Selecta Mathematica 27 (2021), Article 77.
- J.-F. Burnol, "An adelic causality problem related to abelian L-functions" (2001).
- Classical Weil/metaplectic representation and theta transformation machinery.

## Status

The new Lean modules were written to `codex/orientation-mass-time-formalization`.  They are
connector-written and have not yet been certified by an exact-head CI run.  No RH proof is
claimed.  The concrete gain is a much narrower theorem target and an exact operator bridge
between the project's spin/orientation algebra and the existing arithmetic positivity
programme.
