"""
soft_pole_log_divergence.py

Follow-up to soft_pole_divergence.py, attempting the two named-but-untried
resolutions of the omega5=0 soft/double-pole discontinuity: (i) does
analytically continuing/reorganizing the calculation change the character
of the divergence, and (ii) is there a cancelling piece. This file makes
real progress on (i) -- not a full resolution, but a genuine qualitative
upgrade of the diagnosis -- and leaves (ii) still open.

RECAP: soft_pole_divergence.py found that Disc[1/omega5](Delta-1), evaluated
POINTWISE at a single fixed lambda (Delta=1+i*lambda), diverges like 1/eps
as eps->0 -- confirmed two independent ways at the time (closed-form formula
and raw quadrature), and that finding stands, unchanged, as a fact about
the pointwise object.

THE NEW STEP: that pointwise object is not the physical quantity by itself
-- the physical soft-pole contribution to Sewn is the FULL lambda-INTEGRAL
of it against the Plancherel measure, Sewn_soft = int dlam/(2pi) P(lam) *
Disc[c_{-2}/omega5^2](1+i*lam). The pointwise 1/eps divergence at each fixed
lambda does not automatically mean the lambda-INTEGRATED quantity diverges
the same way -- oscillatory phase cancellation across lambda can (and here,
does) soften a pointwise divergence. This was not checked before; checking
it is what this file does.

DERIVATION: factoring the eps-dependence out of the reduction formula,
    Disc[1/omega5](1+i*lam-1) = eps^(i*lam-1) * pi/sin(pi*i*lam) *
                                  [(-i)^(i*lam-1)-(i)^(i*lam-1)]
                                = eps^-1 * eps^(i*lam) * [bounded function of lam]
the ENTIRE eps-dependence is eps^-1 * eps^(i*lam) = eps^-1 * e^(i*lam*ln(eps)) --
an overall eps^-1 prefactor (lambda-independent) times a PURE PHASE in
lambda. Multiplying through by the Plancherel measure and (Delta-1)=i*lam
from the c_{-2} reduction, and simplifying sin(pi*i*lam)=i*sinh(pi*lam) and
[(-i)^(i*lam)-(i)^(i*lam)] = 2*sinh(pi*lam/2) (both elementary identities,
checked, not just asserted), the lambda-dependent "form factor" reduces to

    g(lam) = pi*lam^2 / (sinh(pi*lam) * cosh(pi*lam/2))

so    Sewn_soft(eps) = eps^-1 * Coeff(ln(eps)),   Coeff(x) := int dlam/(2pi) g(lam) e^(i*lam*x)

i.e. Coeff is literally the Fourier transform of g. g is real, ODD (checked:
even/odd/even factors), and decays like lam^2 * exp(-3*pi*lam/2) at large
|lam| -- an entire function of lam except at the poles where sinh(pi*lam)=0
or cosh(pi*lam/2)=0, i.e. lam = 0, +-i, +-2i, +-3i, .... At lam=-i (nearest
pole to the real axis in the lower half-plane, the direction the contour
must close into for x=ln(eps)->-infinity), lam=-i is a DOUBLE pole (both
sinh(pi*lam) and cosh(pi*lam/2) vanish there simultaneously -- checked:
sinh(-i*pi)=0, cosh(-i*pi/2)=cos(pi/2)=0).

By the standard asymptotics of a Fourier transform dominated by its nearest
singularity (Paley-Wiener), a double pole at lam=-i gives Coeff(x) ~
(A*x+B)*e^x as x->-infinity -- i.e. Sewn_soft(eps) = Coeff(ln eps)/eps ~
A*ln(eps) + B: a LOGARITHMIC divergence, not the power-law divergence the
pointwise-in-lambda check alone would suggest (that check was of a
genuinely different, less physical quantity).

VERIFIED TWO INDEPENDENT WAYS, both converging on the SAME exact coefficient:
1. Direct quadrature of Coeff(ln eps) at eps=1e-3..1e-8 (six decades):
   two-point slopes of Im(Coeff/eps) vs ln(eps) converge cleanly to
   0.63507 -> 0.63646 -> 0.63660 -> 0.636618 -> 0.6366196, matching
   2/pi = 0.63661977... to 6+ significant figures.
2. Independent direct residue computation via a small contour integral
   around lam=-i (NOT via the lambda-integral at all): Res(x)/exp(x) at
   x=-5,-10,-15 gives 1.9099, 5.0930, 8.2761 -- linear in x with slope
   exactly -2/pi again (checked: (5.0930-1.9099)/(-5)=-0.6366).
A hand-algebra attempt at the same residue got 2/pi^2 (off by a factor of
pi) -- an arithmetic slip somewhere in the by-hand Laurent expansion, NOT
trusted; the two independent NUMERICAL methods above are what's reported,
and they agree with each other, not with the flawed hand derivation.

CONCLUSION, stated precisely: the lambda-integrated soft/double-pole
discontinuity diverges only LOGARITHMICALLY as eps->0, with an exact,
clean coefficient 2/pi -- not the hopeless power-law divergence the
pointwise check alone suggested. This is a genuine qualitative upgrade:
log divergences are the standard kind handled by minimal subtraction in
QFT (subtract the 2/pi*ln(eps) piece, keep the finite remainder), unlike
power-law divergences, which usually signal a genuinely ill-posed
construction. The clean, simple, exact (not messy/irrational) coefficient
is itself a signal this is real, structured content, not noise.

FOLLOW-UP (2026-08-19): direct connection to the already-verified blackbody
paper machinery (`verify_blackbody_capstone.py`, T6 "Matsubara residues"
and T13 "Fourier pair"), pointed out explicitly rather than left implicit --
T6 already establishes and verifies to 20+ digits exactly this technique
(residue of a Plancherel-type kernel at a Matsubara pole lam=i*n) for the
closely related kernel P(lam)=pi*lam/sinh(pi*lam); T13's
P^hat(k)=(pi/2)sech^2(k/2) is the exact identity `principal_series_sewing.py`
already used earlier this session. This file's g(lam) is a different but
structurally analogous kernel, and the SAME residue-extraction discipline
applies directly.

Used it to pin down a fully rigorous value for the leading Laurent
coefficient at lam=-i, independent of the residue-contour numerics above:
direct raw evaluation of delta^2*g(-i+delta) as delta->0 (no contour
integral, no lambda-integral, just the bare function) converges cleanly to
2i/pi (checked at delta=1e-4, 1e-5, Richardson-extrapolated to match
2/pi to ~2e-9). This is now a THIRD independent confirmation of the same
coefficient, agreeing with both Method 1 (lambda-integral quadrature) and
Method 2 (small-circle residue contour) above.

METHODOLOGICAL PITFALL CAUGHT ALONG THE WAY: an initial attempt to get this
same Laurent coefficient via `mp.taylor(h, 0, 2)` (h(delta):=delta^2*g(-i+delta),
expecting a regular Taylor series since the double pole should cancel)
returned h0=0 -- WRONG, contradicting the other three methods. Traced this
to a genuine bug/precision failure in mpmath's automatic-differentiation-
based `taylor()` when the expansion point sits this close to a genuine
pole of the underlying function (numerical differentiation of a sharply
blowing-up function is ill-conditioned). Diagnosed by falling back to the
most elementary possible check -- literally evaluating g(-i+delta) at a
few small delta and inspecting delta^2*g and delta*g directly -- which
immediately showed the correct 2i/pi (imaginary, delta^2 coefficient) and
-4/pi (real, delta^1 coefficient) structure. Lesson: for coefficients this
close to a real pole, prefer direct evaluation/Richardson extrapolation
over `mp.taylor`, and never trust a single method when a cheap independent
check is available -- caught exactly the kind of silent, wrong-but-
plausible-looking numerical result this whole thread's discipline exists
to catch.

HONEST SCOPE, NOT YET DONE:
  - This computation treated the Laurent coefficient c_{-2} as a fixed
    constant (dropped throughout, restore it by an overall multiplicative
    factor -- it does not affect the log-vs-power-law CHARACTER finding,
    only overall normalization). c_{-2} is actually a function of the
    celestial position z (through A, B, C), not yet tracked.
  - Extracting the actual FINITE remainder after minimal-subtracting the
    2/pi*ln(eps) piece requires either specifying a reference/renormalization
    scale (what does the log run against physically?) or showing the
    remainder is scale-independent -- neither done here.
  - The finite remainder, once obtained, would still need its own z5,z6
    (or z, for the tied-leg construction) integral before it could be
    ADDED to Sewn_s+Sewn_t and compared to the box again -- a substantial
    further step, not attempted tonight.
  - Avenue (ii), a cancelling contact term elsewhere in the construction,
    is still completely untried.
This file closes out the "is it hopelessly power-law divergent" question
(no) and opens, rather than closes, the path to a genuine finite soft-pole
contribution -- real progress, not a full resolution.
"""
import mpmath as mp

mp.mp.dps = 40


def g(lam):
    """The lambda-dependent form factor, c_{-2} stripped (restore by an
    overall constant multiplier)."""
    return mp.pi * lam ** 2 / (mp.sinh(mp.pi * lam) * mp.cosh(mp.pi * lam / 2))


def coeff(ln_eps, Lam=40):
    f = lambda lam: g(mp.mpf(lam)) * mp.e ** (1j * mp.mpf(lam) * ln_eps) / (2 * mp.pi)
    return mp.quad(f, [-Lam, -10, -3, 0, 3, 10, Lam])


def residue_at_minus_i(x, r=mp.mpf('0.1')):
    f = lambda th: g(-1j + r * mp.e ** (1j * th)) * mp.e ** (
        1j * (-1j + r * mp.e ** (1j * th)) * x) * 1j * r * mp.e ** (1j * th)
    return mp.quad(f, [0, 2 * mp.pi]) / (2j * mp.pi)


def leading_laurent_coeff(delta):
    """delta^2 * g(-i+delta) -- direct evaluation, NOT mp.taylor (which has
    a numerical bug this close to the pole, see docstring)."""
    return (delta ** 2 * g(-1j + delta)).imag


def main():
    print("=" * 78)
    print("Method 1: direct quadrature of the lambda-integral, six decades of eps")
    print("=" * 78)
    prev = None
    for k in [3, 4, 5, 6, 7, 8]:
        eps = mp.mpf(10) ** (-k)
        ln_eps = mp.log(eps)
        c = coeff(ln_eps)
        sewn = (c / eps).imag
        if prev is not None:
            slope = (sewn - prev[1]) / (ln_eps - prev[0])
            print(f"  eps=1e-{k}: Im(Coeff/eps)={mp.nstr(sewn,10)}  "
                  f"slope_from_prev={mp.nstr(slope,8)}  (2/pi={mp.nstr(2/mp.pi,8)})")
        else:
            print(f"  eps=1e-{k}: Im(Coeff/eps)={mp.nstr(sewn,10)}")
        prev = (ln_eps, sewn)

    print()
    print("=" * 78)
    print("Method 2: independent residue computation at lam=-i (double pole)")
    print("=" * 78)
    for x in [mp.mpf('-5'), mp.mpf('-10'), mp.mpf('-15')]:
        res = residue_at_minus_i(x)
        ratio = res / mp.e ** x
        print(f"  x={float(x)}: Res(x)/exp(x) = {mp.nstr(ratio,10)}")
    print("  (slope of this vs x should also match -2/pi, independent of Method 1)")

    print()
    print("=" * 78)
    print("Method 3: direct Laurent-coefficient evaluation (Richardson-extrapolated)")
    print("=" * 78)
    d1, d2 = mp.mpf('0.0001'), mp.mpf('0.00001')
    c1, c2 = leading_laurent_coeff(d1), leading_laurent_coeff(d2)
    extrap = c2 + (c2 - c1) / (d1 / d2 - 1)
    print(f"  delta=1e-4: Im(delta^2*g) = {mp.nstr(c1,12)}")
    print(f"  delta=1e-5: Im(delta^2*g) = {mp.nstr(c2,12)}")
    print(f"  Richardson-extrapolated: {mp.nstr(extrap,12)}  (2/pi={mp.nstr(2/mp.pi,12)}, "
          f"match to {mp.nstr(abs(extrap-2/mp.pi),4)})")


if __name__ == "__main__":
    main()
