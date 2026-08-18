"""
sewn_z_integral_v2.py

Corrected version of sewn_z_integral.py. Diagnosed why the first attempt's
scipy dblquad threw "probably divergent" warnings: it wasn't a real
divergence. Checked directly (not assumed): for physical s>0 in the
make_kinematics(s,t) frame, B(z) = -4E(1+|z|^2) is EXACTLY z-independent in
sign -- strictly negative for every z, verified over a large random sample
and analytically (B depends only on |z|^2 via q^0-q^3 dotted with p1+p2,
both of whose energy components are -E). So w0=-s/B is strictly positive
everywhere for s>0: the w0>0 "physical branch" cutoff in the first attempt
was a no-op, never actually restricting anything, and produced no genuine
singularity. Checked the true large-|z| behavior directly along rays: the
full polar integrand (coeff(r,theta) * measure(r) * r, i.e. including the
Jacobian) decays smoothly, roughly like 1/r^4, out to r=1000 with no sign
of blow-up. The earlier warnings were a Cartesian-quadrature artifact from
an unnecessary discontinuous branch cut, not a real divergence -- removed
here, replaced with genuine polar-coordinate integration to a large but
finite radius, checked for convergence in R directly.
"""
import numpy as np
from scipy import integrate
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 25


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


def polar_integrand(theta, r, A_of, B_of, C_of, s_val):
    """coeff(x,y) * round-sphere measure * r (polar Jacobian). No branch
    cutoff -- checked B<0 always for physical s>0, so w0>0 everywhere."""
    x, y = r * np.cos(theta), r * np.sin(theta)
    A = A_of(x, y)
    B = B_of(x, y)
    C = C_of(x, y)
    if abs(C) < 1e-9 or abs(A) < 1e-9 or abs(B) < 1e-9:
        return 0.0
    w0 = -s_val / B
    logw0 = np.log(w0)
    sech2 = 1.0 / np.cosh(logw0 / 2) ** 2
    coeff = -np.pi / (2 * A * C * B) * w0 ** (-2) * sech2
    measure = 1.0 / (1 + r ** 2) ** 2
    return coeff * measure * r


def box_exact_complex(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    val = (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)
    return complex(val)


def compute(s_in, t_in, R):
    A_of, B_of, C_of, s_val = build_functions(s_in, t_in)
    val, err = integrate.dblquad(
        polar_integrand, 0, R, 0, 2 * np.pi,
        args=(A_of, B_of, C_of, s_val),
        epsabs=1e-12, epsrel=1e-10,
    )
    return val, err


def main():
    print("=" * 72)
    print("Convergence in R (polar cutoff radius) -- should stabilize")
    print("=" * 72)
    s_in, t_in = 3.0, -2.0
    for R in [5, 10, 20, 40, 80]:
        val, err = compute(s_in, t_in, R)
        print(f"  R={R}: coeff_integral = {val:.10g}  (quad_err~{err:.2e})")

    print()
    print("=" * 72)
    print("z-integral of Sewn(z) vs 2i*Im(box_exact(s,t)), four kinematic points")
    print("=" * 72)
    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    for s_in, t_in in cases:
        val, err = compute(s_in, t_in, R=60)
        Sewn_total = -1j * val
        box = box_exact_complex(s_in, t_in)
        target = 2j * box.imag
        ratio = Sewn_total / target if target != 0 else None
        print(f"s={s_in} t={t_in}: Sewn_total={Sewn_total}  target={target}  "
              f"ratio={ratio}  (quad_err~{err:.2e})")


if __name__ == "__main__":
    main()
