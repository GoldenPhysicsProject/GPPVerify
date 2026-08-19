"""
residue_t_channel.py

t-channel analog of residue_at_coincidence.py + residue_double_integral.py,
built the same way tied_leg_continuation.py's s-channel construction was
completed by t_channel_sewing.py: swap the comb ordering to put legs 2,3
adjacent to leg 5 instead of 1,2 (5-2-3-1-4-6), so the propagator carrying
the Mandelstam scale is D2'=(k5+p2+p3)^2=omega5*B''+t instead of +s.

Res_{Delta5=1}[L'(Delta5)] = 1/(A'*t) by the exact same derivation as the
s-channel case (the pole comes from the omega5->0 endpoint, independent of
which A,B,scale labels are used -- verified this is a fully general fact,
not re-derived from scratch here).

NEW WRINKLE, not present in the s-channel case: A'(z5) = 2q(z5).p2 =
-4E*|z5|^2 is NOT z5-independent (unlike A=2q(z5).p1=-4E in the s-channel
case) -- checked directly. So the z5 integral is no longer trivial
multiplication by pi; it has its own OPE-collinear-type singularity at
z5=0 (where A'=0), structurally identical to the z6 integral's singularity
at z4 (both are "kappa*|z-z0|^2" perfect squares), regularized the exact
same way (analytic continuation of the singular power, pole extracted
analytically, rho0-independence checked).

RESULT: ResidueSewn_t(s,t) = F_z5(regularized, pole at z5=0) * F_z6(same C,
same z4 as the s-channel case) / t, a genuine, doubly-regularized (z5 AND
z6, two independent collinear poles) closed number. Both regularizations
individually rho0-independence-checked (converge cleanly, e.g. the z5 one
at s=3,t=-2: -0.290->-0.238->-0.224->-0.221->-0.220 as rho0 shrinks
0.2->0.01) before trusting the combined result.

HONEST RESULT, four kinematic points: Sewn_s(residue)+Sewn_t(residue) vs
box_exact(s,t) and vs Re(box_exact(s,t)) -- neither ratio is remotely
constant, and unlike the single-channel comparison (residue_double_integral.py),
this one doesn't even hold a consistent SIGN:
    s=3,t=-0.5:  ratio/box = -0.0081-0.0107j   ratio/Re(box) = -0.0223
    s=3,t=-1.0:  ratio/box = +0.0117+0.0103j   ratio/Re(box) = +0.0207
    s=5,t=-1.0:  ratio/box = -0.0358-0.0420j   ratio/Re(box) = -0.0852
    s=3,t=-2.0:  ratio/box = +0.0417+0.0288j   ratio/Re(box) = +0.0615
A clean, honest negative: the residue/completeness-relation construction
(untied legs, s+t channel comb orderings), even after being made fully
finite and doubly cross-checked at every step, does not reproduce the box
integral or its real part, in either magnitude or even sign pattern. This
closes out (negatively) the natural next test after residue_at_coincidence.py
and residue_double_integral.py -- the untied/residue picture is a genuinely
different, self-consistent construction from the tied-leg Sokhotski-Plemelj
picture, but neither one, alone, reproduces the box.
"""
import warnings
import numpy as np
from scipy import integrate
import mpmath as mp

from celestial_kinematics import make_kinematics, mink_dot

warnings.filterwarnings("ignore")
mp.mp.dps = 25


def box_exact_complex(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    val = (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)
    return complex(val)


def regularized_pole_integral(func_of, z0, rho0_list=(0.1, 0.05, 0.02), Rmax=60):
    """Generic: int d^2z/(1+|z|^2)^2 / func_of(z), func has a kappa*|z-z0|^2
    zero at z0 -- same analytic-continuation regularization used throughout
    this thread."""
    x0, y0 = z0.real, z0.imag
    # find kappa numerically from func_of near z0 (func(z0+h) ~ kappa*|h|^2)
    h = 1e-4
    kappa = func_of(x0 + h, y0) / h ** 2
    coeff = 1.0 / (1 + x0 ** 2 + y0 ** 2) ** 2 / kappa
    totals = []
    for rho0 in rho0_list:
        F_local = 2 * np.pi * coeff * np.log(rho0 * np.sqrt(abs(kappa)))

        def integrand_polar(theta, r):
            x, y = r * np.cos(theta), r * np.sin(theta)
            if (x - x0) ** 2 + (y - y0) ** 2 < rho0 ** 2:
                return 0.0
            val = func_of(x, y)
            if abs(val) < 1e-12:
                return 0.0
            return (1.0 / (1 + x ** 2 + y ** 2) ** 2) / val * r

        F_rest, _ = integrate.dblquad(integrand_polar, 0, Rmax, 0, 2 * np.pi,
                                       epsabs=1e-11, epsrel=1e-9)
        totals.append(F_local + F_rest)
    return totals[-1], kappa


def full_sewn_s(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    s_val = mp.mpf(str(mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                                 tuple(p1[i] + p2[i] for i in range(4)))))
    A_here = mp.mpf(-4) * mp.sqrt(s_val) / 2
    z5_factor = mp.pi / (A_here * s_val)

    def C_of(x, y):
        z = complex(x, y); zb = z.conjugate()
        qv = (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)
        return 2 * (qv[0] * p4[0] - qv[1] * p4[1] - qv[2] * p4[2] - qv[3] * p4[3]).real

    p40, p41, p42, p43 = p4
    z4 = complex(p41 / (p40 + p43), p42 / (p40 + p43))
    F_z6, _ = regularized_pole_integral(C_of, z4)
    return complex(z5_factor) * F_z6


def full_sewn_t(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    t_val = mp.mpf(str(mink_dot(tuple(p2[i] + p3[i] for i in range(4)),
                                 tuple(p2[i] + p3[i] for i in range(4)))))

    def Ap_of(x, y):
        z = complex(x, y); zb = z.conjugate()
        qv = (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)
        return 2 * (qv[0] * p2[0] - qv[1] * p2[1] - qv[2] * p2[2] - qv[3] * p2[3]).real

    def C_of(x, y):
        z = complex(x, y); zb = z.conjugate()
        qv = (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)
        return 2 * (qv[0] * p4[0] - qv[1] * p4[1] - qv[2] * p4[2] - qv[3] * p4[3]).real

    F_z5, kappa5 = regularized_pole_integral(Ap_of, complex(0, 0))
    p40, p41, p42, p43 = p4
    z4 = complex(p41 / (p40 + p43), p42 / (p40 + p43))
    F_z6, _ = regularized_pole_integral(C_of, z4)

    # Res_{Delta5=1}[L'] = 1/(A'*t); Sewn_t = (1/C) * that, then z5,z6-integrated
    # = [int d^2z5 measure/A'(z5)] * [int d^2z6 measure/C(z6)] / t
    return complex(F_z5 * F_z6 / t_val)


def main():
    print("=" * 90)
    print("Residue construction, s AND t channel, vs box_exact and Re(box_exact)")
    print("=" * 90)
    cases = [(3.0, -0.5), (3.0, -1.0), (5.0, -1.0), (3.0, -2.0)]
    for s_in, t_in in cases:
        Ss = full_sewn_s(s_in, t_in)
        St = full_sewn_t(s_in, t_in)
        combo = Ss + St
        box = box_exact_complex(s_in, t_in)
        ratio_box = combo / box if abs(box) else None
        ratio_re = combo / box.real if box.real else None
        print(f"s={s_in} t={t_in}:")
        print(f"  Sewn_s(residue)={Ss:.6f}  Sewn_t(residue)={St:.6f}  sum={combo:.6f}")
        print(f"  box_exact={box:.6f}  ratio(sum/box)={ratio_box:.4f}  ratio(sum/Re(box))={ratio_re:.4f}")


if __name__ == "__main__":
    main()
