"""
sewn_t_z_integral.py

t-channel analog of sewn_z_integral_regularized.py, built from
t_channel_sewing.py's independently-verified Sewn_t(z) closed form:

    Sewn_t(z) = -i*pi/(2*A'*C*B'') * w0_t^-2 * sech(ln(w0_t)/2)^2,
    w0_t = -t/B''(z),  A'=2*q(z).p2,  B''=2*q(z).(p2+p3),  C=2*q(z).p4

TWO singularities found in this construction, structurally different from
the s-channel case:

1. A'(z) = 2*q(z).p2 is EXACTLY proportional to |z-z2|^2 (checked: A'(0,0)=0
   exactly, matching z2=0 for this frame's p2). Same collinear/OPE
   structure as the s-channel's C(z) at z4, handled the same way (analytic
   continuation A'^{-1} -> A'^{-1+delta}, local Laurent expansion at z2).

2. B''(z) = 2*q(z).(p2+p3) GENUINELY CHANGES SIGN across the z-plane
   (checked directly by grid scan: unlike the s-channel's B(z), which is a
   frame artifact -- always one sign because p1,p2 happen to sit on the
   same axis in make_kinematics' frame -- p2+p3 is NOT along a special axis
   here, so B'' has real angular dependence and crosses zero on a genuine
   curve). Because w0_t=-t/B'' inherits this sign change, and the closed
   form's sech(ln(w0_t)/2) needs a REAL log, this is a genuine branch cut,
   not the removable/no-op restriction found (and used harmlessly) in the
   s-channel case. Correctly continuing this branch cut needs a careful,
   causality-motivated choice (matching how the retarded/advanced epsilon
   was originally fixed in the omega5 Sokhotski-Plemelj derivation) --
   NOT done rigorously here.

FIRST-PASS TREATMENT (explicit, incomplete, clearly flagged): restrict the
z-integration domain to {w0_t(z) > 0} and treat the rest of the plane as a
zero contribution. This is very likely NOT the physically complete answer
-- it discards whatever the w0_t<0 region's correct analytic continuation
would contribute -- but gives an honest first number rather than nothing,
and is exactly analogous to the "restrict to physical branch" step that
turned out to be a harmless no-op for the s-channel (there, because B never
actually changed sign; here, it is NOT a no-op, so this really is
discarding a piece of the true answer).
"""
import numpy as np
from scipy import integrate

from celestial_kinematics import make_kinematics, mink_dot


def build_functions(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    t_val = mink_dot(tuple(p2[i] + p3[i] for i in range(4)),
                      tuple(p2[i] + p3[i] for i in range(4)))
    t_val = float(t_val.real if hasattr(t_val, "real") else t_val)

    def q(x, y):
        z = complex(x, y)
        zb = z.conjugate()
        return (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)

    def dotp(qv, p):
        return (qv[0] * p[0] - qv[1] * p[1] - qv[2] * p[2] - qv[3] * p[3]).real

    def Ap_of(x, y):
        return 2 * dotp(q(x, y), p2)

    def Bpp_of(x, y):
        return 2 * dotp(q(x, y), tuple(p2[i] + p3[i] for i in range(4)))

    def C_of(x, y):
        return 2 * dotp(q(x, y), p4)

    p20, p21, p22, p23 = p2
    denom = p20 + p23
    z2 = complex(p21 / denom, p22 / denom) if abs(denom) > 1e-12 else None
    kappa2 = 2 * (p20 + p23)  # A'(x,y) = kappa2 * |z - z2|^2

    return Ap_of, Bpp_of, C_of, t_val, z2, kappa2


def full_integrand(x, y, Ap_of, Bpp_of, C_of, t_val):
    Ap, Bpp, C = Ap_of(x, y), Bpp_of(x, y), C_of(x, y)
    if abs(Ap) < 1e-9 or abs(Bpp) < 1e-9 or abs(C) < 1e-14:
        return 0.0
    w0 = -t_val / Bpp
    if w0 <= 0:
        return 0.0
    sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
    coeff = -np.pi / (2 * Ap * C * Bpp) * w0 ** (-2) * sech2
    return coeff / (1 + x ** 2 + y ** 2) ** 2


def smooth_coeff_at(x, y, Bpp_of, C_of, t_val):
    """everything except the singular 1/A' factor"""
    Bpp, C = Bpp_of(x, y), C_of(x, y)
    w0 = -t_val / Bpp
    if w0 <= 0:
        return 0.0
    sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
    measure = 1.0 / (1 + x ** 2 + y ** 2) ** 2
    return -np.pi / (2 * C * Bpp) * w0 ** (-2) * sech2 * measure


def regularized_finite_part(s_in, t_in, rho0_list=(0.1, 0.05, 0.02), Rmax=60):
    Ap_of, Bpp_of, C_of, t_val, z2, kappa2 = build_functions(s_in, t_in)
    x2, y2 = z2.real, z2.imag
    coeff_at_z2 = smooth_coeff_at(x2, y2, Bpp_of, C_of, t_val)
    P = np.pi * coeff_at_z2 / kappa2

    def F_local(rho0):
        return 2 * np.pi * coeff_at_z2 / kappa2 * np.log(rho0 * np.sqrt(kappa2))

    def F_rest(rho0):
        def integrand_polar(theta, r):
            x, y = r * np.cos(theta), r * np.sin(theta)
            if (x - x2) ** 2 + (y - y2) ** 2 < rho0 ** 2:
                return 0.0
            return full_integrand(x, y, Ap_of, Bpp_of, C_of, t_val) * r
        val, err = integrate.dblquad(integrand_polar, 0, Rmax, 0, 2 * np.pi,
                                      epsabs=1e-11, epsrel=1e-9)
        return val, err

    totals = []
    for rho0 in rho0_list:
        Fr, err = F_rest(rho0)
        total = F_local(rho0) + Fr
        totals.append(total)
    return P, totals, rho0_list


def main():
    print("=" * 78)
    print("t-channel z-integral (w0_t>0 branch only, first pass)")
    print("=" * 78)
    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    for s_in, t_in in cases:
        P, totals, rho0_list = regularized_finite_part(s_in, t_in)
        F = totals[-1]
        spread = max(totals) - min(totals)
        print(f"s={s_in} t={t_in}: pole P={P:.6f}  "
              f"F at rho0={list(rho0_list)}: {[f'{v:.6f}' for v in totals]} "
              f"(spread={spread:.2e})")
        print(f"  Sewn_t_total = -i*F = {-1j*F}")


if __name__ == "__main__":
    main()
