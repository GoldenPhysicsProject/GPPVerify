# Möbius gauge, half-density GCD metric, and fermionic determinant attack on RH

Date: 2026-09-13

This note records the current Codex attack after the single-Hardy reflection route was killed.
Nothing below claims RH is proved.  The point is to replace vague `unitarity should force RH`
language by exact algebraic objects and to isolate the remaining theorem as sharply as possible.

## 1. The finite reciprocal-contraction theorem

Use the Cayley coordinate

\[
\beta(s)=\frac{s-1}{s}.
\]

Functional-equation reflection sends

\[
s\mapsto1-s,
\qquad
\beta\mapsto\beta^{-1},
\]

while Hilbert adjunction sends

\[
s\mapsto\bar s,
\qquad
\beta\mapsto\bar\beta.
\]

Hence shadow equals Hilbert adjoint precisely when

\[
\beta^{-1}=\bar\beta,
\]

i.e. when `|beta|=1`, equivalently `Re(s)=1/2`.

An equivalent positivity formulation is stronger than one-sided contractivity.  If BOTH reflected
channels are contractions in the same positive norm,

\[
|\beta(s)|\le1,
\qquad
|\beta(1-s)|\le1,
\]

then reciprocity gives

\[
|\beta(s)|\,|\beta(1-s)|=1,
\]

so both norms are exactly one and `Re(s)=1/2`.

The scalar core is formalized in

`GppVerify/RiemannHypothesis/ReciprocalContractionCriticalLine.lean`.

This does NOT prove that the global arithmetic realization supplies both contraction inequalities.
That is precisely the positivity/causality theorem still missing.

## 2. Möbius inversion is an exact arithmetic gauge connection

Let `*` denote Dirichlet convolution, let `zeta` denote the constant-one arithmetic function, let
`mu=zeta^{-1}` be Möbius, and let

\[
(Df)(n)=\log(n)f(n)
\]

be logarithmic length differentiation.

Because

\[
\log(ab)=\log a+\log b,
\]

`D` is a derivation of the Dirichlet-convolution algebra:

\[
D(f*g)=Df*g+f*Dg.
\]

Therefore, formally on any domain on which the operations make sense,

\[
\begin{aligned}
\mu * D(\zeta*f)
&=\mu*(D\zeta*f+\zeta*Df)\\
&=(\mu*D\zeta)*f+Df.
\end{aligned}
\]

But `D zeta = log`, and Mathlib already proves the exact identity

\[
\boxed{\mu*\log=\Lambda.}
\]

Consequently

\[
\boxed{
\mu * D\zeta
= D+\Lambda*.
}
\]

Thus the von Mangoldt prime-power channel is not an independent decoration.  It is the connection
one-form generated when logarithmic length is conjugated by zeta synthesis / Möbius inversion.
At the half-density normalization its coefficients are exactly

\[
\frac{\Lambda(n)}{\sqrt n},
\]

the prime side of the Weil distribution.

The exact scalar convolution identity and the half-density weights are formalized in

`GppVerify/RiemannHypothesis/MobiusVonMangoldtGaugeConnection.lean`.

The derivation identity `D(f*g)=Df*g+f*Dg` is the next direct ArithmeticFunction theorem to wire in;
it has not yet been machine checked on this branch.

## 3. Finite zeta synthesis automatically carries a positive gauge metric

At a finite arithmetic cutoff let `Z` be any invertible synthesis matrix and let `D>=0` be a
nonnegative diagonal length operator.  Put

\[
B=Z^{-1}DZ,
\qquad
G=Z^*Z.
\]

Then

\[
GB=B^*G=Z^*DZ
\]

and for every vector `x`,

\[
\boxed{
\langle x,GBx\rangle
=\langle Zx,DZx\rangle
=\|D^{1/2}Zx\|^2\ge0.
}
\]

So every finite zeta-gauged logarithmic generator is positive and self-adjoint in its natural
zeta Gram metric.  A general finite Gram-square core has been formalized in

`GppVerify/RiemannHypothesis/ZetaGaugeGramPositivity.lean`.

This makes the global obstruction much more specific: RH is not failing for lack of finite positive
metrics.  The question is whether the metric has a nondegenerate causal completion at the critical
half-density after the reflected and Archimedean channels are attached, with no norm escaping into
the Nyman--Burnol model space.

## 4. The critical half-density metric is an Euler product of local Poisson kernels

There is a concrete arithmetic metric hidden in the preceding construction.

Take finite divisor/zeta synthesis

\[
(Z_N f)(n)=\sum_{d\mid n}f(d),
\qquad 1\le n\le N.
\]

The Gram matrix of its divisor-incidence columns is

\[
(Z_N^*Z_N)_{d,e}
=\#\{n\le N:d\mid n,\ e\mid n\}
=\left\lfloor\frac{N}{\operatorname{lcm}(d,e)}\right\rfloor.
\]

After division by `N`, the entrywise limit is

\[
G_0(d,e)=\frac1{\operatorname{lcm}(d,e)}.
\]

Conjugating by the half-density weights `sqrt(d)` gives

\[
\boxed{
K_{1/2}(d,e)
=\frac{\sqrt{de}}{\operatorname{lcm}(d,e)}
=\frac{\gcd(d,e)}{\sqrt{de}}.
}
\]

Writing

\[
d=\prod_p p^{a_p},
\qquad
e=\prod_p p^{b_p},
\]

gives the exact Euler factorization

\[
\boxed{
K_{1/2}(d,e)
=\prod_p p^{-|a_p-b_p|/2}.
}
\]

Thus each prime contributes the local Toeplitz/Poisson covariance

\[
K_p(a,b)=r_p^{|a-b|},
\qquad r_p=p^{-1/2}.
\]

This is exactly the same local parameter `a_p=p^{-1/2}` that appears in the existing prime
beam-splitter / Poisson-kernel formalizations.  The global half-density metric is therefore the
tensor product of the local Poisson metrics, not an analogy to them.

For one prime, if `S` is the unilateral occupation shift, then formally

\[
Z_p=(I-r_pS)^{-1}
\]

and

\[
\boxed{
(1-r_p^2)Z_p^*Z_p
=\bigl[r_p^{|a-b|}\bigr]_{a,b\ge0}.
}
\]

So the Poisson kernel is the normalized local zeta Gram matrix.

### Collision check

The kernel

\[
\frac{\gcd(m,n)}{\sqrt{mn}}
\]

is a classical GCD-sum kernel and is heavily used in the resonance theory of large values of
`zeta(1/2+it)`.  The new point needed here is not ownership of the kernel; it is its derivation as
the critical half-density Gram metric of zeta synthesis and its coupling to the Möbius/von-Mangoldt
gauge connection above.

## 5. The same metric exposes a sharp critical-boundary obstruction

For general real `sigma>0`, the analogous multiplicative Poisson kernel is

\[
K_\sigma(m,n)
=\prod_p p^{-\sigma|a_p-b_p|}
=\left(\frac{\gcd(m,n)^2}{mn}\right)^\sigma.
\]

The first column is

\[
K_\sigma(1,n)=n^{-\sigma}.
\]

Hence its naive `ell^2(N)` column norm is controlled by

\[
\sum_{n\ge1}n^{-2\sigma}.
\]

This converges for `sigma>1/2` and diverges at the critical value `sigma=1/2`.
Therefore the half-density metric is positive as a kernel but sits exactly on the boundary where the
naive `ell^2` Gram operator ceases even to have its vacuum column in `ell^2`.

The shadow exponent is `1-sigma`.  Requiring both the primal and shadow metrics to be naively
bounded would require simultaneously

\[
\sigma>\frac12,
\qquad
1-\sigma>\frac12,
\]

which is impossible.  Their unique common boundary is

\[
\boxed{\sigma=\frac12.}
\]

This is an important no-go and a guide to the correct topology: the global RH Hilbert space cannot
be the naive one-sided `ell^2` completion.  It must be a doubled/renormalized principal-series or
rigged-Hilbert completion in which the two opposite Hardy orientations meet at the common boundary.
This is consistent with the existing Burnol/Lax--Phillips obstruction rather than evading it.

## 6. The BPY cumulants are exactly the power traces of the desired fermionic operator

Let

\[
F(z)=\frac{\xi(1/2+z)}{\xi(1/2)}
\]

and write the BPY cumulant expansion

\[
\log F(z)
=\sum_{m\ge1}\kappa_{2m}\frac{z^{2m}}{(2m)!}.
\]

The current manuscript defines

\[
\mu_n=(-1)^n\frac{\kappa_{2n+2}}{(2n+1)!}.
\]

Suppose there is a positive trace-class one-particle operator `A` with

\[
\boxed{
F(z)=\det(I+z^2A).
}
\]

Then

\[
\log\det(I+z^2A)
=\sum_{m\ge1}(-1)^{m+1}\frac{z^{2m}}m\operatorname{Tr}(A^m).
\]

Coefficient comparison gives the exact identity

\[
\boxed{
\operatorname{Tr}(A^m)=\frac{\mu_{m-1}}2.
}
\]

Equivalently,

\[
\boxed{
\mu_n=2\operatorname{Tr}(A^{n+1}).
}
\]

So the alternating BPY cumulants are precisely the loop/power traces of the desired positive
fermionic one-particle operator.

Under RH one may take `A` to have eigenvalues

\[
\gamma^{-2}
\]

with the multiplicities of the critical zeros.  Then `A` is positive trace class and the centered
Hadamard product gives exactly the determinant above.

Conversely, ANY positive trace-class representation

\[
F(z)=\det(I+z^2A)
\]

forces every zero of `F` to satisfy

\[
z^2=-\lambda^{-1}\le0
\]

for a positive eigenvalue `lambda`, hence `Re(z)=0` and therefore RH.

The finite root-localization core is formalized in

`GppVerify/RiemannHypothesis/FiniteFermionicDeterminantCriticalZeros.lean`.

This is the cleanest operator target found so far:

> **Construct the positive trace-class one-particle operator `A` from zero-independent arithmetic / BPY data and prove that its fermionic Fredholm determinant is `F`.**

That is stronger and more explicit than merely asking for an unspecified Hilbert--Polya operator.

## 7. Relation to the existing BPY Stieltjes criterion

The manuscript's exact function

\[
\mathcal S(w)
=\frac{F'(\sqrt w)}{\sqrt w F(\sqrt w)}
\]

would satisfy, for the positive operator above,

\[
\boxed{
\mathcal S(w)
=2\operatorname{Tr}\!\left[A(I+wA)^{-1}\right].
}
\]

Expanding at zero gives

\[
\mathcal S(w)
=2\sum_{n\ge0}(-1)^n\operatorname{Tr}(A^{n+1})w^n
=\sum_{n\ge0}(-1)^n\mu_nw^n.
\]

So the manuscript's cumulant--Stieltjes/Hankel criterion is exactly the resolvent moment condition
for a positive fermionic one-particle spectrum.

The remaining subtlety is important.  Ordinary moment positivity first produces a positive
representing measure, not automatically a trace-class operator with integer spectral
multiplicities.  Here `S(w)` is already a fixed meromorphic logarithmic derivative of the entire
function `F`; if its Stieltjes positivity is proved, its meromorphic continuation forces the
representing measure onto its real poles, and the residues are the integer zero multiplicities.
That is the bridge from moment positivity to the genuine determinant.

## 8. What reflection does and does not do

The earlier single-Hardy proposal

\[
JSJ^{-1}=S^*
\]

is impossible for the unilateral shift because the kernel dimensions differ.

Moving to the ghost model space does not solve this: every nonzero `K_B` already possesses a
canonical conjugation exchanging its compressed shift with its adjoint.  Reflection therefore
pairs the defect directions but does not annihilate them.

The actual Nyman--Burnol defect remains

\[
\|P_{K_B}1\|^2=1-|B(0)|^2.
\]

The metaplectic/Fourier double cover can contribute to a proof only if it supplies an ambient
**no-loss identity** which forces this quantity to vanish.

## 9. Revised closure target

The attacks now line up as follows.

1. Finite arithmetic synthesis has an exact positive zeta Gram metric.
2. Its gauge connection is exactly the von Mangoldt channel `Lambda`.
3. Half-density normalization gives the Euler product of local Poisson metrics
   `gcd(m,n)/sqrt(mn)`.
4. The critical line is the unique common boundary of the primal and shadow Hilbert metrics.
5. BPY cumulants are exactly the power traces required by a positive fermionic determinant.
6. A positive trace-class determinant representation of `F` would prove RH immediately.
7. The only remaining nonlocal obstruction is the critical global completion: prove that the
   prime--Archimedean / Tate--Poisson gluing carries no Nyman ghost and no escaped trace.

The win condition is therefore no longer vague:

\[
\boxed{
F(z)=\det(I+z^2A),\qquad A\ge0,\quad A\in\mathcal S_1,
}
\]

constructed without zero data.

Equivalently, prove the BPY moment/Hankel positivity by an arithmetic Gram factorization whose
completion retains the Möbius connection and cancels the Archimedean boundary defect before the
physical quotient is taken.

That is the theorem to attack next.
