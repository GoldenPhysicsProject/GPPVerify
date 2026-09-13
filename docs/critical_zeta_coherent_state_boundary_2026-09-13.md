# Critical half-density as a zeta coherent-state orthogonality boundary

Date: 2026-09-13

This note continues the Möbius-gauge / GCD-metric attack.  It records an exact positive-state
construction that explains why `Re(s)=1/2` is a singular Hilbert boundary, not merely the line on
which scalar Euler weights have modulus one.  Nothing here proves RH.

## 1. Local normalized prime occupation state

For a prime `p` and `s = sigma + i t` with `sigma > 0`, define on the occupation basis
`|a>`, `a >= 0`,

\[
 |\Omega_{p,s}\rangle
 = \sqrt{1-p^{-2\sigma}}\sum_{a\ge0}p^{-as}|a\rangle .
\]

It is exactly normalized:

\[
 \|\Omega_{p,s}\|^2
 = (1-p^{-2\sigma})\sum_{a\ge0}p^{-2\sigma a}=1.
\]

For two parameters `s,w`,

\[
 \langle\Omega_{p,s},\Omega_{p,w}\rangle
 = \frac{\sqrt{(1-p^{-2\Re s})(1-p^{-2\Re w})}}
        {1-p^{-(\bar s+w)}}.
\]

Thus every local Euler channel is an honest positive Hilbert overlap.

## 2. Finite-prime tensor product and the zeta kernel

For a finite prime set `P`, let

\[
 |\Omega_{P,s}\rangle=\bigotimes_{p\in P}|\Omega_{p,s}\rangle .
\]

Then

\[
 \langle\Omega_{P,s},\Omega_{P,w}\rangle
 =\prod_{p\in P}
 \frac{\sqrt{(1-p^{-2\Re s})(1-p^{-2\Re w})}}
      {1-p^{-(\bar s+w)}}.
\]

On a common vertical line `Re(s)=Re(w)=sigma>1/2`, the all-prime limit converges absolutely and
is

\[
 \boxed{
 K_\sigma(t,u)
 =\frac{\zeta(2\sigma+i(u-t))}{\zeta(2\sigma)} .
 }
\]

This is a normalized positive-definite kernel because it is literally a vector overlap.  It is
also the characteristic kernel of the zeta Gibbs law

\[
 \mathbb P_\sigma(N=n)=\frac{n^{-2\sigma}}{\zeta(2\sigma)}:
 \qquad
 K_\sigma(t,u)
 =\mathbb E_\sigma e^{-i(u-t)\log N}.
\]

Hence the prime-Fock and zeta-Gibbs pictures are the same state in two bases.

## 3. The critical line is an orthogonality catastrophe

For `t=u`, `K_sigma(t,t)=1`.  For `t != u`, `zeta(1+i(u-t))` is finite, while
`zeta(2 sigma) -> +infinity` as `sigma -> 1/2+`.  Therefore

\[
 \boxed{
 \lim_{\sigma\downarrow1/2}K_\sigma(t,u)
 =\begin{cases}
 1,&t=u,\\
 0,&t\ne u.
 \end{cases}}
\]

Thus distinct principal-series phases become mutually orthogonal at the critical half-density.
The pointwise limiting characteristic function is discontinuous at the origin, so it is not the
characteristic function of a probability measure on the ordinary real log-energy line.  The Gibbs
mass escapes to infinity.  Equivalently, the boundary states cease to live in the same ordinary
vacuum representation and must be treated as generalized / rigged-Hilbert spectral states.

This is the precise operator-theoretic content of the earlier observation that the vacuum column
`n^{-sigma}` is in `ell^2` for `sigma>1/2` and fails exactly at `sigma=1/2`.

## 4. Vacuum fidelity and the von Mangoldt connection

The finite-prime vacuum fidelity is

\[
 |\langle0|\Omega_{P,s}\rangle|^2
 =\prod_{p\in P}(1-p^{-2\sigma}).
\]

For `sigma>1/2`, the all-prime value is

\[
 \boxed{
 |\langle0|\Omega_s\rangle|^2=\frac1{\zeta(2\sigma)}.
 }
\]

Its logarithmic radial derivative is

\[
 \boxed{
 \partial_\sigma\log |\langle0|\Omega_s\rangle|^2
 =-2\frac{\zeta'}{\zeta}(2\sigma)
 =2\sum_{n\ge1}\frac{\Lambda(n)}{n^{2\sigma}} .
 }
\]

So the von Mangoldt prime-power channel derived algebraically in
`DirichletLogGaugeIdentity.lean` is also the susceptibility of the positive zeta-state vacuum
fidelity.  The same connection is being seen in three forms:

1. `mu * D(zeta * f) - Df = Lambda * f` (Dirichlet gauge connection);
2. the normal derivative of the Euler/Poisson metric;
3. the radial derivative of the zeta coherent-state normalization.

This is an exact structural unification, not an RH assumption.

## 5. Local Poisson covariance and weighted Möbius precision

At one prime put `r=p^{-sigma}` and let `S` be the unilateral occupation shift.  The local zeta
synthesis is

\[
 Z_p=(I-rS)^{-1}.
\]

Its normalized covariance is

\[
 \boxed{
 K_p=(1-r^2)Z_p^*Z_p,
 \qquad
 (K_p)_{ab}=r^{|a-b|}.
 }
\]

The inverse precision operator is therefore

\[
 \boxed{
 K_p^{-1}
 =\frac1{1-r^2}(I-rS)(I-rS^*).
 }
\]

Thus the Poisson/GCD metric is the Green covariance of the local weighted Möbius difference
`I-rS`.  Expanding the product over primes gives the global weighted Möbius operator with
squarefree coefficients

\[
 \prod_p(I-p^{-\sigma}S_p)
 =\sum_{d\ \mathrm{squarefree}}\mu(d)d^{-\sigma}S_d
\]

at every finite-prime cutoff.

At `sigma=1/2` the product of local covariance normalizations is

\[
 \prod_p(1-p^{-1})=0,
\]

whereas for `sigma>1/2`

\[
 \prod_p(1-p^{-2\sigma})=\zeta(2\sigma)^{-1}>0.
\]

Hence the critical half-density is exactly the point at which the infinite tensor-product
normalization collapses.  This is the same boundary at which the primal and shadow Hardy/Fock
polarizations meet.

## 6. What this does and does not buy for RH

This does **not** prove that zeta zeros lie on the critical line.  It proves something more basic
that the earlier scalar-unity language obscured:

* `Re(s)>1/2` is the ordinary positive-energy/vacuum Fock phase of zeta synthesis;
* `Re(s)=1/2` is its generalized spectral boundary, with delta-like orthogonality in the Mellin
  parameter;
* the prime-power/von-Mangoldt distribution is the radial gauge connection of that positive state;
* the weighted Möbius operator is the precision (inverse covariance) of the local Poisson metric.

The remaining RH theorem must show that the completed Archimedean/reflected theory admits a
positive renormalized boundary pairing with **no additional model-space ghost sector**.  In the
Nyman--Burnol language this is `K_B=0`; in the BPY language it is positivity/contractivity of the
odd channel; in the fermionic determinant language it is existence of a positive trace-class
one-particle operator whose determinant is the centered `xi` function.

The coherent-state calculation gives a concrete candidate carrier for the required boundary
renormalization and identifies exactly where ordinary Hilbert normalization fails: the Euler
normalization `1/zeta(2 sigma)` collapses at the principal-series boundary.