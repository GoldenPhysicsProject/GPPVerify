# Intrinsic critical GCD completion and its exact arithmetic generator

Date: 2026-09-14.
Status: analytical construction with finite numerical cross-check, not Lean-certified.
Continues critical_boundary_domain_audit_2026-09-14.md. No RH claim.

## 1. Explicit unitary coordinates, valid for every sigma>0

Let H_sigma be the completion of finite sequences in the GCD inner product
K_sigma(m,n)=(gcd(m,n)^2/(mn))^sigma. Put
J(d)=d^(2sigma) product_(p|d)(1-p^(-2sigma)).

On finite sequences define

    (T c)_d = sqrt(J(d)) sum_(d|n) c_n/n^sigma,
    (U y)_n = n^sigma sum_(n|d) mu(d/n) y_d/sqrt(J(d)).

All these sums are finite on this initial domain. Divisor Möbius inversion
gives UT=TU=I. The Jordan-totient identity gives q_sigma(c)=||Tc||_2^2.
Moreover T and U map finite sequences to finite sequences. Thus T extends
to a unitary H_sigma -> l2, onto, with inverse extending U.

In particular the vectors

    w_d = (1/sqrt(J(d))) sum_(n|d) n^sigma mu(d/n) e_n

form an explicit orthonormal basis of H_sigma. At sigma=1/2, J is Euler's
totient and this construction is completely well-defined.
It does not contradict nonclosability on ordinary l2: the source space is H_sigma.

For completed vectors, the inverse U is interpreted by convergence in H_sigma,
not by an unjustified pointwise infinite Möbius sum.

## 2. A genuine positive self-adjoint arithmetic generator

Let L be the diagonal log-energy operator on l2:

    (Ly)_d=(log d)y_d,
    D(L)={y : sum_d (log d)^2 |y_d|^2 < infinity}.

Define B_sigma=T^(-1) L T with D(B_sigma)=T^(-1)D(L).
This is positive self-adjoint, and finite sequences are a core.
Its orthonormal eigenvectors are w_d, with eigenvalues log d.

On finite coefficient sequences the operator has the exact formula

    (B_sigma c)_n
      = (log n)c_n
        - sum_(k>=2) Lambda(k) k^(-sigma) c_(nk).

To derive it, expand ULT. The coefficient for m=nk is
(n/m)^sigma sum_(a|k) mu(a) log(na).
For k>1 the latter divisor sum equals -Lambda(k); at k=1 it is log n.

This supplies a global, closed generator with the half-density von Mangoldt
connection. Its upper-triangular multiple-sum orientation differs from the
lower divisor-convolution convention in DirichletLogGaugeIdentity. The sign
and orientation above follow from ULT; they must not be identified silently.

## 3. Exact contraction semigroup

For tau>=0, exp(-tau B_sigma)=U diag(d^(-tau)) T is a strongly continuous
self-adjoint contraction semigroup on H_sigma.

On finite sequences its matrix entries are zero unless n|m. For m=nk,

    [exp(-tau B_sigma)]_(n,m)
      = n^(-tau) k^(-sigma) sum_(a|k) mu(a) a^(-tau)
      = n^(-tau) k^(-sigma) product_(p|k)(1-p^(-tau)).

The empty product for k=1 is one. For tau>0 the coefficients are nonnegative.
At tau=0 this is the identity. Nonnegative coefficients on finite sequences
are not a claim about an unspecified coordinate cone in the completion.

The basis and semigroup identities were checked on n<=30 at sigma=1/2:
max residual UT-I = 2.23e-16,
max residual T* T-K = 4.45e-16,
max residual ULT minus the Mangoldt formula = 4.45e-16.
These are floating-point checks of the algebra, not substitutes for proofs.

## 4. Exactly why this is not the desired Fredholm operator

The construction repairs the Hilbert-domain problem, but its spectrum is log n.
Removing the vacuum w_1 removes the zero eigenvalue. Nevertheless

    Tr(B_sigma^(-2) on w_1-perp)
      = sum_(n>=2) 1/(log n)^2 = infinity.

Thus the immediate candidate A=B_sigma^(-2) is positive and compact but NOT
trace class. More generally no fixed inverse power has finite trace.
The resolvent is compact because log n -> infinity.

The spectral counting function is floor(exp(E))-1 on the vacuum complement.
A bounded self-adjoint perturbation of B_sigma shifts ordered eigenvalues by
at most its norm (min-max principle), so it cannot change this exponential
growth into the Riemann-zero counting law of order E log E. Consequently
bounded corrections to THIS generator cannot supply the required spectrum.

For real tau>1, Tr(exp(-tau B_sigma))=zeta(tau). This is a partition trace,
not a determinant whose zeros are forced by one-particle eigenvalues.
Analytic continuation of that trace does not preserve a convergent positive
trace representation into the critical strip. The identity must not be
presented as a Hilbert–Polya theorem.

Even a finite positive spectrum allows partition traces with zeros in a
right half-plane: 1+2exp(-sE) vanishes at Re(s)=log(2)/E for E>0.
Positivity of a generator therefore gives no general zero-location theorem
for its complex-temperature partition trace.

## 5. What a successful next construction must do

This isolates two different tasks. The intrinsic completion and global
Mangoldt generator now have explicit solutions. The remaining task is an
arithmetic spectral reduction, not a bounded metric adjustment.

A viable Archimedean/shadow completion must either select a substantially
smaller arithmetic spectral space or change the generator unboundedly.
In either case it must prove the exact completed xi determinant identity
and preserve its divisor. A projection chosen from zero ordinates would be
circular. An arbitrary compression can alter eigenvalue density but supplies
no xi identity.

Next concrete comparison: attach the automorphic/co-Poisson boundary relation
to this explicit basis and calculate its Schur complement. The proof-bearing
question is whether that boundary relation is derived from arithmetic data
and controls the completed determinant, including canceled/escaped factors.

The older positive Pick ratio counterexample still applies: convergence of
ratios alone cannot establish conservation of the unreduced divisor.

## 6. Verification checkpoint

Cold workflow 34847057509 checked out 8e250eb6c78919649b7f436a04f184960be23c3c.
All six previously repaired RH modules built:
CayleyShadowAdjointBridge, DirichletLogGaugeIdentity,
FiniteFermionicDeterminantCriticalZeros, ZetaGaugeGramPositivity,
MobiusVonMangoldtGaugeConnection, MetaplecticDilationReflectionCore.
The first two emitted warnings; Cayley's unused binder would fail the
unused-hypothesis gate. The overall build FAILED in remaining files.
Further repairs are being made without weakening theorem statements.
The whole project remains unverified; PR173 remains draft/open.

Finite GCD divisor factorization is classical; no priority claim is made.
General zeta reference: https://dlmf.nist.gov/25.10
