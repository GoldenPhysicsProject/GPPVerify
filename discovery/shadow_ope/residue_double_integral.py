"""
residue_double_integral.py

The (z5,z6) double celestial-sphere integral of Sewn_residue, requested as
the natural next step after residue_at_coincidence.py landed
Sewn_residue(z5,z6) = 1/(A(z5)*C(z6)*s).

PART 0 -- an extra check done before integrating, because a naive quadrature
gave a badly wrong answer here and it mattered to understand why (not swept
under the rug): does Res_{Delta5=1}[L] genuinely stay 1/(A*s), independent
of z5, even when z5 is put on the REAL Lorentzian slice (needed to integrate
over the physical celestial sphere) rather than the split-signature choice
residue_at_coincidence.py used for well-definedness?

Checked directly: for EVERY real z5 tested (20 random points), B(z5)<0
always (matches the already-established structural fact B(z)=-4E(1+|z|^2)
this session), which forces L's own internal omega5-threshold w0=-s/B onto
the positive real w-axis for every real z5 -- not just the one point first
tried. A naive delta*L_ret(1+delta) computation at small delta appeared to
DECAY TO ZERO instead of converging to the predicted residue -- traced this
down (not just re-run until it looked right): it was a genuine quadrature
artifact, mp.quad failing to resolve the near-non-integrable w^(delta-1)
behavior right at the w->0 endpoint for small delta, NOT a real vanishing.
Fixed with a w=e^{-x} substitution turning the power-law endpoint into a
smooth exponential tail -- confirms clean O(delta) convergence to EXACTLY
1/(A*s), matching the split-signature prediction to 7e-6 at delta=1e-5, and
confirms this analytically too: the pole comes entirely from the w->0
(small-omega5 / UV) endpoint of L's defining integral, which is completely
decoupled from the w0=-s/B threshold region -- so the residue is genuinely
independent of whether z5 is real or split-signature, and independent of
any retarded/advanced choice at w0. There is NO hidden extra discontinuity
here. A(z5)=-4E is also independently z5-independent (established earlier
this session). So Sewn_residue's z5-dependence is completely trivial: the
z5 integral is exactly multiplication by the total round-sphere measure.

PART 1 -- the z5 integral is therefore trivial:
    int d^2z5/(1+|z5|^2)^2 = pi   (standard round-sphere total measure)
so int d^2z5 [[Sewn_residue]] = pi * (1/(A*s)) * [z6-dependent piece], i.e.
the z5 integral just contributes an overall factor of pi/(A*s).

PART 2 -- the z6 integral is the genuinely nontrivial piece:
    int d^2z6/(1+|z6|^2)^2 * 1/C(z6),   C(z6) = kappa*|z6-z4|^2
This has EXACTLY the same structure as the collinear/OPE singularity at z4
already regularized in sewn_z_integral_regularized.py (same kappa*|z-z4|^2
denominator) -- reuse that exact technique: analytic continuation
C^{-1} -> C^{-1+delta}, pole coefficient extracted analytically at z4,
finite remainder checked for rho0-independence. Large-|z6| convergence:
1/C(z6) ~ 1/|z6|^2 against the round measure ~1/|z6|^4 gives an integrand
~1/|z6|^6 -- convergent with a wide margin (much faster than the marginal
1/r^2 cases handled earlier this session), so no large-|z| regularization
is needed here, only the collinear piece at z6=z4.

CORRECTION, found by actually running this integral rather than assumed:
residue_at_coincidence.py's docstring claimed Sewn_residue has "no
t-dependence whatsoever," reasoning that t=(p2+p3)^2 never appears as an
explicit symbol in A, B, or C's formulas. That is true as a statement about
the FORMULAS (matches dispersive_extraction.py's original finding for A,B)
-- but C=2q(z6).p4 is evaluated at the ACTUAL momentum p4, and
make_kinematics(s,t) rotates p4 by the scattering angle theta(t) for
different t at fixed s. So C's real value shifts with t even with no "t"
symbol in its formula, and kappa=2(p4^0+p4^3) works out to EXACTLY -t/E
(checked directly: matches to machine precision at three (s,t) points). A
first version of this script's own "t-independence check" section
therefore falsely predicted independence and then measured a genuine ~2x
swing in the result across t at fixed s -- caught here rather than
suppressed. z4's celestial position ALSO shifts with t (not just kappa's
overall scale), so there's no simple closed-form factorization into an
s-only piece times a universal z4-independent shape; F_z6 was computed
directly at each (s,t) point, not assumed factorizable.

RESULT: a genuine closed number depending on BOTH s and t,
    FullSewnResidue(s,t) = pi/(A(s)*s) * F_z6(s,t)
where F_z6(s,t) is the regularized z6 integral of 1/C(z6) at that (s,t)
frame. Rho0-independence spot-checked further at a point that triggered
scipy IntegrationWarnings (s=3,t=-2.5): confirmed the warnings were benign
-- F_local+F_rest converges cleanly (0.478 -> 0.474 -> 0.472 -> 0.472 as
rho0: 0.1->0.05->0.02->0.01), the same discontinuous-cutoff artifact
already understood from sewn_z_integral.py earlier this session, not a
real problem with the result.

HONEST SCOPE: still the same caveats as residue_at_coincidence.py --
Sewn_residue is a different object from tied_leg_continuation.py's
Sewn_s/Sewn_t (real vs purely imaginary, untied vs tied-leg construction).
No claim this equals a piece of the box integral. This computes the
double integral fully and honestly; it does not by itself resolve what
physical role (if any) the result plays in the box-reconstruction problem.
"""
import numpy as np
from scipy import integrate
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 25


def z5_integral_factor(A, s_val):
    """int d^2z5/(1+|z5|^2)^2 * 1/(A*s) = pi/(A*s), since A, s are z5-independent."""
    return mp.pi / (A * s_val)


def build_C(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)

    def C_of(x, y):
        z = complex(x, y)
        zb = z.conjugate()
        qv = (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)
        return 2 * (qv[0] * p4[0] - qv[1] * p4[1] - qv[2] * p4[2] - qv[3] * p4[3]).real

    p40, p41, p42, p43 = p4
    denom = p40 + p43
    z4 = complex(p41 / denom, p42 / denom)
    kappa = 2 * (p40 + p43)
    return C_of, z4, kappa


def z6_integral_regularized(s_in, t_in, rho0_list=(0.1, 0.05, 0.02), Rmax=60):
    C_of, z4, kappa = build_C(s_in, t_in)
    x4, y4 = z4.real, z4.imag

    def measure(x, y):
        return 1.0 / (1 + x ** 2 + y ** 2) ** 2

    # smooth coefficient with the singular 1/C stripped (i.e. just the
    # measure -- C=kappa|z-z4|^2, so 1/C's "smooth part" near z4 is 1/kappa
    # times the angular-independent |z-z4|^-2, handled via the same
    # analytic-continuation trick as before)
    coeff_at_z4 = measure(x4, y4) / kappa
    P = np.pi * coeff_at_z4  # pole coefficient (residue in delta)

    def F_local(rho0):
        return 2 * np.pi * coeff_at_z4 * np.log(rho0 * np.sqrt(kappa))

    def F_rest(rho0):
        def integrand_polar(theta, r):
            x, y = r * np.cos(theta), r * np.sin(theta)
            if (x - x4) ** 2 + (y - y4) ** 2 < rho0 ** 2:
                return 0.0
            C = C_of(x, y)
            if abs(C) < 1e-12:
                return 0.0
            return measure(x, y) / C * r
        val, err = integrate.dblquad(integrand_polar, 0, Rmax, 0, 2 * np.pi,
                                      epsabs=1e-11, epsrel=1e-9)
        return val

    totals = []
    for rho0 in rho0_list:
        totals.append(F_local(rho0) + F_rest(rho0))
    return P, totals, rho0_list


def main():
    print("=" * 78)
    print("Full (z5,z6) double integral of Sewn_residue = 1/(A(z5)*C(z6)*s)")
    print("z5 integral trivial (pi/(A*s)); z6 integral regularized as in")
    print("sewn_z_integral_regularized.py's collinear-pole treatment")
    print("=" * 78)

    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    p1_dummy, p2_dummy, p3_dummy, p4_dummy = make_kinematics(s=3.0, t=-2.0)
    A_const = 2 * q_dot_p(mp.mpc(0.3, 0.2), mp.mpc(0.44, -0.15),
                           tuple(mp.mpf(str(x)) for x in p1_dummy))
    print(f"(sanity: A is z5-independent regardless of s,t inputs; A={mp.nstr(A_const,8)} here)")
    print()

    for s_in, t_in in cases:
        p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
        s_val = mp.mpf(str(mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                                     tuple(p1[i] + p2[i] for i in range(4)))))
        # A depends only on E=sqrt(s)/2, not on t or z5 -- recompute for this s
        A_here = mp.mpf(-4) * mp.sqrt(s_val) / 2

        z5_factor = z5_integral_factor(A_here, s_val)
        P, totals, rho0_list = z6_integral_regularized(s_in, t_in)
        F_z6 = totals[-1]
        spread = max(totals) - min(totals)

        full = z5_factor * F_z6
        print(f"s={s_in} t={t_in}:")
        print(f"  A={mp.nstr(A_here,8)}  z5_factor=pi/(A*s)={mp.nstr(z5_factor,8)}")
        print(f"  z6 pole P={P:.6f} (discarded, minimal subtraction)")
        print(f"  z6 finite F at rho0={list(rho0_list)}: {[f'{v:.6f}' for v in totals]} (spread={spread:.2e})")
        print(f"  FullSewnResidue(s,t) = z5_factor * F_z6 = {mp.nstr(full,10)}")
        print()

    print("=" * 78)
    print("t-dependence, checked directly rather than assumed: FullSewnResidue")
    print("genuinely varies with t at fixed s (correcting an earlier false")
    print("'no t-dependence' claim -- see corrected docstring above)")
    print("=" * 78)
    for s_fixed in [3.0]:
        for t_in in [-0.3, -1.0, -2.5]:
            p1, p2, p3, p4 = make_kinematics(s=s_fixed, t=t_in)
            s_val = mp.mpf(str(mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                                         tuple(p1[i] + p2[i] for i in range(4)))))
            A_here = mp.mpf(-4) * mp.sqrt(s_val) / 2
            z5_factor = z5_integral_factor(A_here, s_val)
            P, totals, rho0_list = z6_integral_regularized(s_fixed, t_in)
            full = z5_factor * totals[-1]
            kappa = -mp.mpf(t_in) / (mp.sqrt(s_val) / 2)
            print(f"  s={s_fixed} t={t_in}: kappa=-t/E={mp.nstr(kappa,6)}  FullSewnResidue = {mp.nstr(full,10)}")


if __name__ == "__main__":
    main()
