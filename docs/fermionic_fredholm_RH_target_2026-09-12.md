# Positive fermionic Fredholm determinant target for RH

Date: 2026-09-12

## 1. A sharper operator form of the BPY cumulant criterion

Let

    F(z) = xi(1/2+z) / xi(1/2).

Under RH the centered Hadamard product is

    F(z) = product_{gamma>0}
             (1 + z^2/gamma^2)^(m_gamma).

Therefore, if `A` is the positive trace-class operator whose eigenvalues are

    lambda_gamma = gamma^(-2)

with multiplicities `m_gamma`, then

    boxed: F(z) = det(I + z^2 A).

Conversely, if one can construct **without using the zero locations** a positive trace-class
operator `A>=0` satisfying this Fredholm determinant identity, every zero of `F` has the form

    z = +/- i / sqrt(lambda)

for a positive eigenvalue `lambda` of `A`.  Hence every zero is on the imaginary `z` axis,
which is RH.

So there is an exact operator criterion:

    RH
      <=> F is the Fredholm determinant det(I+z^2 A)
          of some positive trace-class A,

where the reverse implication is immediate and the forward implication uses the RH zero
product to define `A` spectrally.

The theorem is elementary as an equivalence; the content is to construct `A` arithmetically
without importing the zeros.

## 2. The signed BPY cumulants are exactly positive power traces

Write

    K(z)=log F(z)
        = sum_{m>=1} kappa_{2m} z^(2m)/(2m)!.

For a positive trace-class `A`, the Fredholm logarithm gives

    log det(I+z^2 A)
      = sum_{m>=1} (-1)^(m+1) z^(2m) Tr(A^m)/m.

Hence

    kappa_{2m}
      = 2 (2m-1)! (-1)^(m+1) Tr(A^m).

For the manuscript's BPY moment sequence

    mu_n = (-1)^n kappa_{2n+2}/(2n+1)!,

this becomes the extremely simple identity

    boxed: mu_n = 2 Tr(A^(n+1)).

Therefore the unshifted cumulant Hankel form has the canonical Hilbert--Schmidt Gram
factorization

    H_ij = mu_(i+j)
         = 2 Tr(A^(i+j+1))
         = 2 <A^(i+1/2), A^(j+1/2)>_HS.

For finite coefficients `c_i`,

    sum_ij conjugate(c_i)c_j mu_(i+j)
      = 2 Tr[A |sum_i c_i A^i|^2]
      >= 0.

This is exactly the missing positivity in the BPY cumulant--Stieltjes theorem.

So that theorem can be reread as:

> The BPY cumulant Hankel family is positive exactly when its signed cumulants are the power
> traces of a positive one-particle operator.

The canonical Jacobi operator already constructed from a positive moment solution is the
moment-problem realization of the same object.  The Fredholm formulation states more
physically what has to be built upstream.

## 3. The exterior-Fock interpretation is genuinely fermionic

For a trace-class one-particle operator `T`, fermionic second quantization gives the standard
identity

    Tr_{Lambda H} Gamma(T) = det(I+T).

Consequently

    F(z)=det(I+z^2 A)

is the grand partition function of independent exterior/Fermi modes with one-particle
weights `z^2 lambda_gamma`.

This makes the sign pattern of the BPY cumulants unsurprising:

    log(1+x)
      = x - x^2/2 + x^3/3 - ... .

The alternating cumulants are not a nuisance to be repaired by ordinary bosonic positivity.
They are precisely the logarithm of a fermionic determinant.

This is a more faithful interpretation of the existing `two-fermion BPY` and
Möbius--Koszul calculations than treating the sign hierarchy as an accidental analytic
feature.

## 4. Prime side versus zero side

The prime occupation basis already has the exact bosonic combinatorics

    zeta(s)
      = product_p (1-p^(-s))^(-1)
      = sum_{n>=1} n^(-s).

Each prime mode has arbitrary occupation number `0,1,2,...`, giving the geometric Bose
factor.

The reciprocal Euler product

    1/zeta(s) = product_p (1-p^(-s))

is the corresponding exterior/supertrace factor and is exactly what the finite
Möbius--Koszul complex is built to encode.  The finite prime bulk is contractible: its local
fermionic ghost modes cancel.

The zero side, if the global completion is positive, has instead

    F(z) = det(I+z^2 A),

an ordinary positive exterior-Fock determinant.

This suggests the following global architecture:

    bosonic prime bulk
      -> Möbius/Koszul supersymmetric cancellation
      -> global Poisson--Archimedean boundary cohomology
      -> positive physical one-particle operator A
      -> fermionic boundary determinant F(z).

That architecture is compatible with the manuscript's finite Hodge--Koszul theorem: local
prime cohomology vanishes and a physical spectrum can only appear because the global
Archimedean/Poisson boundary obstructs the local contracting homotopy.

## 5. Equivalent positive Hamiltonian form

Write

    A = H^(-1)

on the physical nonzero sector.  Then the desired operator is

    H >= 0,

with compact resolvent and sufficiently summable inverse, and

    F(z) = det(I + z^2 H^(-1)).

If the corresponding first-order orientation operator is `D` with

    H = D^2,

then

    F(z) = det(I + z^2 D^(-2)).

This is exactly the same first-order/positive-square architecture appearing in the
metaplectic and orientation work:

    reflection: D -> -D,
    energy:     H=D^2 >=0.

The determinant forgets the sign of the oriented eigenfrequency and retains its positive
square.  This is the operator-level version of the spinorial statement that the first-order
lift remembers orientation while the quadratic observable does not.

## 6. Heat trace, OS positivity, cumulants and the determinant are one package

If `H` exists, then

    K_heat(t) = Tr(e^(-tH)) >= 0

is completely monotone in the spectral Laplace variable, while

    log F(z)
      = Tr log(I+z^2 H^(-1)).

Using

    log(1+z^2/lambda)
      = integral_0^infty (1-e^(-z^2 t)) e^(-lambda t) dt/t

in its appropriate regularized form, the determinant and heat-trace pictures are two
transforms of the same positive spectral measure.

Thus the current RH criteria are not separate tricks:

    arithmetic OS heat positivity,
    BPY cumulant Hankel positivity,
    Stieltjes/Nevanlinna positivity,
    positive Fredholm determinant,
    Hodge no-ghost positivity

are different shadows of the same missing positive spectral object.

## 7. What this does and does not solve

This does **not** construct `A` or `H`.  Defining `A` from the zero ordinates assumes RH and
is circular.

The useful reduction is that the construction target is now extremely rigid.  A valid
zero-independent candidate must simultaneously reproduce

    2 Tr(A^(n+1)) = mu_n

for every BPY signed cumulant, and/or

    det(I+z^2 A)=F(z)

as an entire-function identity.

A candidate that matches finitely many moments or low zeros is not enough.

## 8. Best current route

The most plausible source of `A` is not an arbitrary new kernel.  It should arise as the
inverse square of the completed global boundary Dirac/scaling operator already suggested by
three existing structures:

1. the metaplectic half-density dilation generator;
2. the finite prime Möbius--Koszul/Hodge Dirac;
3. the Poisson--Archimedean boundary condition which is exactly where the finite contracting
   homotopy fails.

The hard theorem can therefore be stated as:

> Construct a zero-independent self-adjoint completed boundary operator `D_ar` such that
>
>     D_ar^2 > 0,
>     D_ar^(-2) is trace class,
>     xi(1/2+z)/xi(1/2)
>       = det(I+z^2 D_ar^(-2)).

That one identity proves RH immediately.

It also gives the cleanest mathematical version yet of the current physics intuition:
**the arithmetic object that localizes the zeros is a positive square of an oriented
first-order fermionic generator.**
