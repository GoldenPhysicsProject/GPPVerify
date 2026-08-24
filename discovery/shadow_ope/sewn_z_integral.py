"""
sewn_z_integral.py

The real next step flagged by principal_series_sewing.py's own "what this
does not yet show": complete the (z,zbar) integral of the verified, doubly-
checked closed form

    Sewn(z) = -i*pi/(2*A*C*B(z)) * w0(z)^-2 * sech(ln(w0(z))/2)^2,
    w0(z) = -s/B(z)

against the natural round-sphere measure dx dy/(1+x^2+y^2)^2 (z=x+iy, real
Lorentzian slice zbar=conj(z)), and compare against the correct physical
target for a genuine discontinuity/unitarity-cut object: NOT box_exact(s,t)
itself, but 2i*Im(box_exact(s,t)) (Schwarz reflection: Disc f = f(s+ieps)-
f(s-ieps) = 2i*Im f is manifestly purely imaginary for real couplings,
matching Sewn's own manifestly-purely-imaginary structure -- comparing to
box_exact directly, as every earlier K1 attempt did, was comparing a
discontinuity object to the full complex amplitude, a category mismatch).

Structural fact found while setting this up (verified directly, not
assumed): in the make_kinematics(s,t) frame, A=2*q(z).p1 is EXACTLY
z-independent (p1 sits along the same axis as the stereographic chart's
pole, a frame degeneracy of this specific kinematic parametrization, not a
general fact). B(z)=2*q(z).(p1+p2) depends only on |z|^2 (radially
symmetric). Only C(z)=2*q(z).p4 has genuine angular dependence, since p4's
transverse components are generically nonzero. This means the z-integral is
NOT trivially reducible to a 1D radial integral -- the angular dependence
through C(z) is real physics here, not integrated out by symmetry.

w0(z)=-s/B(z) changes sign as B(z) crosses zero; the closed form's sech(ln(w0)/2)^2
requires w0>0 to stay on the real/physical branch used in its derivation. This
script restricts the z-integration domain to {w0(z)>0} as the most direct
first attempt (the honest alternative -- analytically continuing across
w0<0 -- is flagged as a further open refinement, not attempted here).

STATUS: exploratory, first attempt at completing this specific open item.
Report the actual number and its ratio to 2i*Im(box_exact) honestly,
whatever it turns out to be.
"""
import numpy as np
from scipy import integrate

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot


def build_functions(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    s_val = float(s_val.real if hasattr(s_val, "real") else s_val)

    def q(x, y):
        z = complex(x, y)
        zb = z.conjugate()
        return (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)

    def dotp(qv, p):
        return (qv[0] * p[0] - qv[1] * p[1] - qv[2] * p[2] - qv[3] * p[3]).real

    def A_of(x, y):
        return 2 * dotp(q(x, y), p1)

    def B_of(x, y):
        return 2 * dotp(q(x, y), tuple(p1[i] + p2[i] for i in range(4)))

    def C_of(x, y):
        return 2 * dotp(q(x, y), p4)

    return A_of, B_of, C_of, s_val


def sewn_integrand(x, y, A_of, B_of, C_of, s_val):
    """Real and imaginary parts of the round-sphere-weighted Sewn(z)
    integrand, restricted to the w0>0 branch (returns 0 outside it)."""
    A = A_of(x, y)
    B = B_of(x, y)
    C = C_of(x, y)
    if abs(A) < 1e-12 or abs(B) < 1e-12 or abs(C) < 1e-12:
        return 0.0
    w0 = -s_val / B
    if w0 <= 0:
        return 0.0
    logw0 = np.log(w0)
    sech2 = 1.0 / np.cosh(logw0 / 2) ** 2
    # Sewn(z) = -i*pi/(2*A*C*B) * w0^-2 * sech2 -- purely imaginary, so we
    # track only its (real) coefficient of -i, then multiply by the
    # round-sphere measure.
    coeff = -np.pi / (2 * A * C * B) * w0 ** (-2) * sech2
    measure = 1.0 / (1 + x ** 2 + y ** 2) ** 2
    return coeff * measure


def box_exact_complex(s_in, t_in):
    import mpmath as mp
    mp.mp.dps = 25
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    val = (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)
    return complex(val)


def main():
    print("=" * 72)
    print("z-integral of Sewn(z) (round-sphere measure, w0>0 branch only)")
    print("vs the physically correct target 2i*Im(box_exact(s,t))")
    print("=" * 72)
    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    for s_in, t_in in cases:
        A_of, B_of, C_of, s_val = build_functions(s_in, t_in)
        # integrate the -i coefficient (real number) over a large disk
        R = 40.0
        val, err = integrate.dblquad(
            lambda y, x: sewn_integrand(x, y, A_of, B_of, C_of, s_val),
            -R, R, -R, R,
            epsabs=1e-10, epsrel=1e-8,
        )
        Sewn_total = -1j * val  # reattach the overall -i
        box = box_exact_complex(s_in, t_in)
        target = 2j * box.imag
        ratio = Sewn_total / target if target != 0 else None
        print(f"s={s_in} t={t_in}:")
        print(f"  z-integral coeff (real, quad_err~{err:.1e}) = {val:.10g}")
        print(f"  Sewn_total = {Sewn_total}")
        print(f"  target 2i*Im(box) = {target}")
        print(f"  ratio = {ratio}")
        print()


if __name__ == "__main__":
    main()
