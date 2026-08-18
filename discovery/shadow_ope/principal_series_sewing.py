"""
principal_series_sewing.py

Direct continuation of tied_leg_continuation.py, per Daniel's steer:
"it should be anywhere the internal operators equal 2" -- i.e. the
Delta5+Delta6=2 shadow-pair condition is always satisfied on the principal
series Delta=1+i*lambda paired with its shadow 2-Delta=1-i*lambda, so the
natural completion of the tied-leg result is to integrate the verified
disc(Delta) over the WHOLE principal series (lambda real, -inf to inf)
against the Plancherel measure -- exactly the sewing integral this thread
has been trying to make sense of since shadow_sewing.py, except now built
from a genuinely non-singular ingredient instead of the pathological
L(Delta5)*R(Delta6) product.

disc(Delta) = -2*pi*i/(A*C*B) * w0^(Delta-3)   (w0 = -s/B, verified in
tied_leg_continuation.py against direct eps->0 quadrature to ~1e-10, error
shrinking as O(eps^2))

On the principal series Delta=1+i*lambda (w0 real positive), w0^(Delta-3)
= w0^(-2) * w0^(i*lambda) = w0^(-2) * e^(i*lambda*ln(w0)) -- a PURE PHASE
times a fixed real prefactor. |disc(1+i*lambda)| is therefore CONSTANT in
lambda -- no growth, no coincident-pole pathology anywhere on this
contour, unlike every previous attempt in this thread. Multiplying by the
Plancherel measure P(lambda)=pi*lambda/sinh(pi*lambda), which decays
exponentially, the sewing integral

    Sewn := int_{-inf}^{inf} dlambda/(2*pi) * P(lambda) * disc(1+i*lambda)

is manifestly absolutely convergent (bounded oscillating integrand times
an exponentially decaying measure) -- textbook convergence, checked
directly by quadrature at increasing cutoffs (20/40/80, identical to 15
digits) before trusting anything further.

CLOSED FORM (derived here, not assumed): the real integral inside, int
P(lambda) cos(lambda*x) dlambda, was numerically scanned against several
candidates at 5 different x and matched EXACTLY (ratio = pi to 8 digits,
every x) to (pi/2)*sech(x/2)^2 -- a standard Fourier-transform identity
for the SL(2,C) Plancherel kernel. This gives

    Sewn = -i*pi/(2*A*C*B) * w0^(-2) * sech(ln(w0)/2)^2

Verified against DIRECT numerical quadrature of the lambda-integral to
~1e-30 relative error (not just the eps-regularized discontinuity check --
this is a second, independent verification) at THREE independent
kinematic points below.

WHAT THIS SHOWS: the tied-leg / real-Lorentzian-slice construction gives a
finite, closed-form, non-singular value for the D2-threshold contribution
to the shadow-pair sewing integral, integrated over the ENTIRE principal
series -- the operation that diverged in every previous attempt in this
thread (shadow_sewing.py, dispersive_extraction.py,
mandelstam_regulator_check.py) now converges cleanly with an exact answer.

WHAT THIS DOES NOT YET SHOW: this is still only the D2-threshold piece.
The omega5=0 soft/IR double pole (D1 and the crossing-continued D3
vanishing together) has not been included -- its contribution to the full
sewing integral is a separate, not-yet-attempted calculation, likely
needing a derivative-of-delta-type Sokhotski-Plemelj identity rather than
the simple-pole one used here. The (z,zbar) integral supplying
t=(p2+p3)^2-dependence (see discovery/README.md's structural finding) is
also not included -- Sewn above is evaluated at ONE fixed z (a single
point on the celestial sphere), not integrated over it. No claim that
Sewn, as computed here, equals any piece of the box integral -- it is a
finite, closed-form, doubly-verified number, nothing more asserted.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def build_ABC(s_in, t_in, z):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    s_val = mp.mpf(str(s_val))
    zb = mp.conj(z)
    A = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p1))
    Bv = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(p1[i] + p2[i])) for i in range(4)))
    C = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p4))
    return A, Bv, C, s_val


def plancherel(lam):
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def disc(Delta, A, Bv, C, w0):
    return -2j * mp.pi / (A * C * Bv) * w0 ** (Delta - 3)


def sewn_numeric(A, Bv, C, w0):
    f = lambda lam: plancherel(mp.mpf(lam)) * disc(mp.mpc(1, lam), A, Bv, C, w0) / (2 * mp.pi)
    return mp.quad(f, [-30, -5, 0, 5, 30])


def sewn_closed_form(A, Bv, C, w0):
    x = mp.log(w0)
    return -1j * mp.pi / (2 * A * C * Bv) * w0 ** (-2) * mp.sech(x / 2) ** 2


def main():
    print("=" * 72)
    print("Robustness of the lambda-integral (should stabilize with cutoff,")
    print("no previous quantity in this thread ever did)")
    print("=" * 72)
    A, Bv, C, s_val = build_ABC(3.0, -2.0, mp.mpc('0.31', '0.20'))
    w0 = (-s_val / Bv).real
    for cutoff in [20, 40, 80]:
        f = lambda lam: plancherel(mp.mpf(lam)) * disc(mp.mpc(1, lam), A, Bv, C, w0) / (2 * mp.pi)
        val = mp.quad(f, [-cutoff, 0, cutoff])
        print(f"  cutoff={cutoff}: Sewn = {mp.nstr(val, 15)}")

    print()
    print("=" * 72)
    print("Closed form vs direct quadrature, three independent kinematic points")
    print("=" * 72)
    cases = [
        (3.0, -2.0, mp.mpc('0.31', '0.20')),
        (5.0, -1.0, mp.mpc('0.6', '-0.4')),
        (2.0, -1.0, mp.mpc('-0.15', '0.35')),
    ]
    for s_in, t_in, z in cases:
        A, Bv, C, s_val = build_ABC(s_in, t_in, z)
        w0 = (-s_val / Bv).real
        if w0 <= 0:
            print(f"  s={s_in} t={t_in}: w0<=0, skip (not on the physical branch)")
            continue
        num = sewn_numeric(A, Bv, C, w0)
        closed = sewn_closed_form(A, Bv, C, w0)
        err = abs(num - closed) / abs(closed)
        print(f"  s={s_in} t={t_in} z={z}: w0={float(w0):.6f}")
        print(f"    Sewn (quadrature)  = {mp.nstr(num,12)}")
        print(f"    Sewn (closed form) = {mp.nstr(closed,12)}")
        print(f"    rel_err = {mp.nstr(err,4)}")

    print()
    print("CLOSED FORM: Sewn = -i*pi/(2*A*C*B) * w0^-2 * sech(ln(w0)/2)^2")
    print("  w0 = -s/B, the D2 threshold on the real Lorentzian celestial slice.")


if __name__ == "__main__":
    main()
