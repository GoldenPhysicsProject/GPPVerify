"""
sewn_combined_st.py

Final consolidated result of tonight's deep-dive: the fully regularized,
round-sphere-measure z-integral of Sewn_s(z) + Sewn_t(z), compared against
the physically correct target 2i*Im(box_exact(s,t)) for a discontinuity
object. Assembles sewn_z_integral_regularized.py (s-channel) and
sewn_t_z_integral.py (t-channel) with the CORRECTED, unambiguous
regularization scheme (only the manifestly-nonnegative radial distance rho
is fractionally powered; the real coefficient kappa, which can be negative,
is kept as an exact prefactor -- avoiding the branch ambiguity of raising a
negative real number to a fractional power).

KEY RESULT ESTABLISHED THIS ROUND, with a direct numerical proof (not an
assumption): the t-channel's w0_t<0 region genuinely has ZERO
discontinuity, confirmed by comparing directly against the raw
retarded/advanced omega5 quadrature (no closed-form formula assumed) at a
w0_t<0 kinematic point -- result ~3e-6, consistent with pure epsilon-
regulator noise, not a real nonzero value. This means restricting the
t-channel z-integral to {w0_t(z)>0} is the PHYSICALLY CORRECT prescription
(w0_t<0 means the threshold would sit at unphysical negative omega5, so
there simply is no discontinuity there), not an incomplete approximation
as first suspected when the branch structure was discovered.

RESULT: Sewn_s(z) + Sewn_t(z), fully z-integrated and regularized, does
NOT match 2i*Im(box_exact(s,t)) -- wrong order of magnitude, wrong sign
pattern, and a ratio that is not even approximately constant across the
four kinematic points tested (-0.056, -0.445, -0.132, -2.894). This is an
honest negative result after substantial, careful work, not glossed over.

WHAT IS STILL MISSING, precisely scoped (not vague): the omega5=0
soft/double-pole contribution, explicitly flagged as untreated in
tied_leg_continuation.py and principal_series_sewing.py from earlier this
session, and NOT computed in tonight's z-integral work either. A partial
reduction was derived tonight: writing the amplitude's Laurent expansion
near omega5=0 as c_{-2}/omega5^2 + c_{-1}/omega5 + O(1), the DOUBLE-pole
piece's retarded-minus-advanced Mellin discontinuity reduces via
integration by parts to

    Disc[c_{-2}/omega5^2](Delta) = c_{-2} * (Delta-1) * Disc[1/omega5](Delta-1)

i.e. (Delta-1) times a SIMPLE-pole discontinuity shifted in Delta by one.
This is a clean, verifiable reduction (boundary terms vanish for Delta in
the right strip). What is NOT yet resolved: Disc[1/omega5](Delta) itself
requires the Sokhotski-Plemelj distributional identity
1/(omega-ieps)-1/(omega+ieps) -> 2*pi*i*delta(omega), and delta(omega) sits
exactly at the BOUNDARY of the omega5 in (0,infinity) integration domain --
a genuine distributional subtlety (is a boundary delta function "half
inside" the domain, fully inside, or excluded?), not a numerical
convergence issue like everything resolved earlier tonight. This needs a
careful, principled resolution (e.g. by keeping the eps-regulator finite
and taking the omega5->0+ limit of the integrated result analytically,
rather than distributionally) before it can be added to the s+t total
above. Concretely scoped as the next step; not attempted further tonight.
"""
import numpy as np
from scipy import integrate
import mpmath as mp

from celestial_kinematics import make_kinematics, mink_dot

mp.mp.dps = 25


def qxy(x, y):
    z = complex(x, y)
    zb = z.conjugate()
    return (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)


def dotp(qv, p):
    return (qv[0] * p[0] - qv[1] * p[1] - qv[2] * p[2] - qv[3] * p[3]).real


def box_exact_complex(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    val = (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)
    return complex(val)


def s_channel_regularized(s_in, t_in, rho0=0.02, Rmax=60):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    s_val = float(mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                            tuple(p1[i] + p2[i] for i in range(4))).real)

    def A_of(x, y): return 2 * dotp(qxy(x, y), p1)
    def B_of(x, y): return 2 * dotp(qxy(x, y), tuple(p1[i] + p2[i] for i in range(4)))
    def C_of(x, y): return 2 * dotp(qxy(x, y), p4)

    p40, p41, p42, p43 = p4
    denom = p40 + p43
    z0 = complex(p41 / denom, p42 / denom)
    kappa = 2 * (p40 + p43)

    def full_integrand(x, y):
        A, B, C = A_of(x, y), B_of(x, y), C_of(x, y)
        if abs(A) < 1e-9 or abs(B) < 1e-9 or abs(C) < 1e-14:
            return 0.0
        w0 = -s_val / B
        sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
        return -np.pi / (2 * A * C * B) * w0 ** (-2) * sech2 / (1 + x ** 2 + y ** 2) ** 2

    def smooth_coeff_at(x, y):
        A, B = A_of(x, y), B_of(x, y)
        w0 = -s_val / B
        sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
        return -np.pi / (2 * A * B) * w0 ** (-2) * sech2 / (1 + x ** 2 + y ** 2) ** 2

    coeff0 = smooth_coeff_at(z0.real, z0.imag)
    F_local = 2 * np.pi * coeff0 / kappa * np.log(rho0)

    def integrand_polar(theta, r):
        x, y = r * np.cos(theta), r * np.sin(theta)
        if (x - z0.real) ** 2 + (y - z0.imag) ** 2 < rho0 ** 2:
            return 0.0
        return full_integrand(x, y) * r

    F_rest, _ = integrate.dblquad(integrand_polar, 0, Rmax, 0, 2 * np.pi,
                                   epsabs=1e-11, epsrel=1e-9)
    return F_local + F_rest


def t_channel_regularized(s_in, t_in, rho0=0.02, Rmax=60):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    t_val = float(mink_dot(tuple(p2[i] + p3[i] for i in range(4)),
                            tuple(p2[i] + p3[i] for i in range(4))).real)

    def Ap_of(x, y): return 2 * dotp(qxy(x, y), p2)
    def Bpp_of(x, y): return 2 * dotp(qxy(x, y), tuple(p2[i] + p3[i] for i in range(4)))
    def C_of(x, y): return 2 * dotp(qxy(x, y), p4)

    p20, p21, p22, p23 = p2
    denom = p20 + p23
    z0 = complex(p21 / denom, p22 / denom) if abs(denom) > 1e-12 else complex(0, 0)
    kappa2 = 2 * (p20 + p23)

    def full_integrand(x, y):
        Ap, Bpp, C = Ap_of(x, y), Bpp_of(x, y), C_of(x, y)
        if abs(Ap) < 1e-9 or abs(Bpp) < 1e-9 or abs(C) < 1e-14:
            return 0.0
        w0 = -t_val / Bpp
        if w0 <= 0:
            return 0.0  # confirmed physically correct: no threshold in physical omega5>0 domain
        sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
        return -np.pi / (2 * Ap * C * Bpp) * w0 ** (-2) * sech2 / (1 + x ** 2 + y ** 2) ** 2

    def smooth_coeff_at(x, y):
        Bpp, C = Bpp_of(x, y), C_of(x, y)
        w0 = -t_val / Bpp
        if w0 <= 0:
            return 0.0
        sech2 = 1.0 / np.cosh(np.log(w0) / 2) ** 2
        return -np.pi / (2 * C * Bpp) * w0 ** (-2) * sech2 / (1 + x ** 2 + y ** 2) ** 2

    coeff0 = smooth_coeff_at(z0.real, z0.imag)
    F_local = 2 * np.pi * coeff0 / kappa2 * np.log(rho0)

    def integrand_polar(theta, r):
        x, y = r * np.cos(theta), r * np.sin(theta)
        if (x - z0.real) ** 2 + (y - z0.imag) ** 2 < rho0 ** 2:
            return 0.0
        return full_integrand(x, y) * r

    F_rest, _ = integrate.dblquad(integrand_polar, 0, Rmax, 0, 2 * np.pi,
                                   epsabs=1e-11, epsrel=1e-9)
    return F_local + F_rest


def main():
    print("=" * 78)
    print("Sewn_s(z) + Sewn_t(z), fully regularized z-integral, vs 2i*Im(box_exact)")
    print("=" * 78)
    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    for s_in, t_in in cases:
        Fs = s_channel_regularized(s_in, t_in)
        Ft = t_channel_regularized(s_in, t_in)
        Sewn_s, Sewn_t = -1j * Fs, -1j * Ft
        combo = Sewn_s + Sewn_t
        box = box_exact_complex(s_in, t_in)
        target = 2j * box.imag
        ratio = combo / target if target != 0 else None
        print(f"s={s_in} t={t_in}: Sewn_s={Sewn_s}  Sewn_t={Sewn_t}")
        print(f"  sum={combo}  target={target}  ratio={ratio}")


if __name__ == "__main__":
    main()
