# Eisenstein Satake parameters and the exact arithmetic spin tower

Date: 2026-09-12

## 1. The prime-power coefficients in the Riemann Wigner kernel

The principal-series Hecke coefficient occurring in the exact Wigner--Bessel expansion is

    lambda_t(n)=n^(it) sigma_{-2it}(n).

For a prime power `n=p^m`, put

    theta_p = t log p.

Then

    lambda_t(p^m)
      = p^(imt) sum_{j=0}^m p^(-2ijt)
      = sum_{j=0}^m exp(i(m-2j) theta_p).

This is exactly the character of the `(m+1)`-dimensional irreducible representation

    Sym^m(C^2)

of `SU(2)` evaluated on the diagonal torus element

    g_p(t)=diag(e^(i theta_p), e^(-i theta_p)).

Equivalently,

    boxed:

    lambda_t(p^m)
      = chi_{m/2}(theta_p)
      = sin((m+1)theta_p)/sin(theta_p)
      = U_m(cos theta_p),

with the continuous limiting value `m+1` when `sin(theta_p)=0`.

Here `U_m` is the Chebyshev polynomial of the second kind and `chi_{m/2}` is the ordinary
spin-`m/2` `SU(2)` character.

This is an exact representation-theoretic identity, not a physical-spin claim.

## 2. The first levels are literally the integer / half-integer spin characters

The first prime-power repetitions are

    m=0:  lambda_t(1)   = 1                         spin 0,

    m=1:  lambda_t(p)   = e^(i theta)+e^(-i theta)
                          = 2 cos theta             spin 1/2,

    m=2:  lambda_t(p^2) = e^(2i theta)+1+e^(-2i theta)
                          = 1+2 cos(2 theta)         spin 1,

    m=3:  lambda_t(p^3) = e^(3i theta)+e^(i theta)
                          +e^(-i theta)+e^(-3i theta) spin 3/2,

and so on.

Thus the prime-power tower naturally runs

    0, 1/2, 1, 3/2, 2, ...

through every `SU(2)` spin.

This gives a precise number-theoretic version of the intuition that integer and half-integer
rotation sectors should arise from one double-cover representation theory.  It does **not**
identify these `SU(2)` representation labels with physical spacetime spin without an
additional intertwiner.

## 3. Why the half appears

The local normalized Satake parameter on the unitary Eisenstein principal series is the pair

    alpha_p = e^(i theta_p),
    alpha_p^(-1)=e^(-i theta_p).

The fundamental two-dimensional carrier has weights `+1` and `-1`.  Its symmetric `m`th
power has weights

    m, m-2, ..., -m,

which is precisely the `SU(2)` irrep of spin `j=m/2`.

So the half-integer is not inserted by hand.  It comes from the fact that the fundamental
rank-two double-cover representation has highest weight one, while physical angular momentum
is conventionally labelled by half that highest weight:

    m = 2j.

That is the same group-theoretic reason that the fundamental representation of `SU(2)` is
called spin `1/2` even though its two torus weights are `+1` and `-1` in the natural integral
weight lattice.

## 4. Critical line = compact Satake locus

The same formula extends away from the unitary axis.  If

    s=1/2 + delta + it,

then the normalized local pair is

    alpha_p(s)=p^delta e^(i t log p),
    alpha_p(s)^(-1)=p^(-delta)e^(-i t log p).

The determinant remains one, so this is an `SL_2(C)` pair.  But it lies in the compact torus
of `SU(2)` exactly when

    delta=0,

that is,

    Re(s)=1/2.

Therefore

    boxed:

    critical line
      = local compact/unitary Satake locus
      = tempered principal-series axis.

An off-critical analytic continuation has reciprocal eigenvalues of unequal modulus: one
expands and the other contracts.  This is the same contraction/expansion geometry already
found in the Burnol/Nyman Cayley coordinate.

## 5. Relation to the spin / metaplectic discussion

There are now three exact but distinct double-cover structures in the project:

1. spacetime spin:

       Spin(3) = SU(2) -> SO(3),

   with half-integer representations and `4 pi` spinorial closure;

2. harmonic/metaplectic analysis:

       Mp(2) -> Sp(2),

   with Fourier quarter-turn and the order-four relation `F^2=parity`, `F^4=1`;

3. the normalized local `GL_2` Eisenstein Satake pair:

       diag(alpha,alpha^-1),

   which on the principal line lies in an `SU(2)` compact torus and whose prime-power Hecke
   coefficients are the complete `SU(2)` spin-character tower.

They must not be declared identical.  But the arithmetic principal series really does
contain the same rank-two compact representation theory that generates integer and
half-integer spin characters.

That makes the earlier spin intuition mathematically much less accidental.

## 6. A sign no-go which matters for RH positivity

The character itself is not positive.  Already at a prime,

    lambda_t(p)=2 cos(t log p).

Choosing

    t = pi/log p

makes

    lambda_t(p)=-2.

So Hecke self-adjointness or local `SU(2)` unitarity does **not** make the Riemann Wigner
kernel termwise positive.

Likewise higher-spin characters oscillate in sign.  Therefore any proof of the Jensen/BPY
positivity cannot be a statement that each local representation character is positive.

The positivity, if true, has to arise from the full coupled object:

    Hecke/Satake tower
      + Whittaker/K-Bessel radial kernel
      + Archimedean completion
      + the specific Jensen/OS polarization.

This is exactly consistent with the existing no-go theorem that independent positive local
prime blocks have excessive spectral density and cannot converge to `xi` without a global
multichannel compression.

## 7. The representation-theoretic RH statement

The exact Wigner--Eisenstein bridge derived in the companion note shows that the Riemann
Wigner kernel is a fixed differential observable evaluated on the Eisenstein principal
series.

The new Satake calculation sharpens that statement: every arithmetic coefficient entering
that observable is a compact `SU(2)` character on the unitary axis.

So one can formulate the missing theorem as follows:

> Construct the global prime--Archimedean polarization which turns the analytically
> continued reciprocal `SL_2(C)` Satake data into an actual unitary physical spectrum.
> Then only the compact `SU(2)` locus survives, forcing the spectral parameter onto the
> principal line.

This is the same logical pattern as the Rosati argument over finite fields:

    reciprocal duality
      + positive polarization
      -> compact/unitary normalized spectrum.

The local compactness is already exact.  The unresolved theorem is why the global zeta
resonances must belong to the positive polarized spectrum rather than merely to its analytic
continuation.

## 8. Collision check

The classical facts used here are standard:

- the weight-zero Eisenstein Hecke eigenvalue
  `lambda_t(n)=n^(it) sigma_{-2it}(n)`;
- unramified unitary principal-series Satake parameters lie on the compact torus;
- `Sym^m(C^2)` has `SU(2)` character
  `sin((m+1)theta)/sin(theta)`.

The project-specific point is their exact appearance inside the previously derived
Riemann-Wigner Bessel expansion and their use as the arithmetic spin-tower dictionary.
No priority claim is made.
