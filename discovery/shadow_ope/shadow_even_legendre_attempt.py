"""
shadow_even_legendre_attempt.py

Direct test of whether verify_qg_kinematics.py's Theorem 3.1 (Shadow
connection) resolves K1(lambda;s,t), after Daniel asked directly whether
this thread was actually using the measure/kinematics/blackbody papers'
established results. It hadn't been for K1 specifically -- this file fixes
that, tests the natural resulting ansatz, and reports the result honestly
(negative, but with a real, well-scoped lead identified, not a dead end).

THE IDEA: Theorem 3.1 gives an EXACT closed form for the difference between
a Legendre Q_nu and its shadow partner Q_{-nu-1}:
    Q_{-nu-1}(x) - Q_nu(x) = i*pi*tanh(pi*lam/2) * P_nu(x)
with P_nu = P_{-nu-1} manifestly SHADOW-EVEN. Combined with Theorem 2.1
(k_h(z) = c(lam)*Q_{h-1}(2/z-1), c(lam)=2*Gamma(2h)/Gamma(h)^2, and
h-1 = -1/2+i*lam/2 = nu exactly for h=(1+i*lam)/2), this means P_nu(2/z-1)
is EXACTLY the properly-normalized shadow-DIFFERENCE of the chiral block
k_h(z) and its shadow partner k_{1-h}(z) -- not their PRODUCT, which is
what kinematic_block_attempt2.py's K1_v2 used. Since a genuine shadow
DISCONTINUITY object should be shadow-even (matching how the physical
"jump across the shadow pole" doesn't care which side you started from),
P_nu looked like a much better-motivated candidate building block than the
product ansatz tried before.

VERIFIED FIRST (before building on them): re-checked Theorem 2.1 and
Theorem 3.1 independently at fresh points (not the paper's own test set) --
both confirmed to 1e-31 to 1e-35, essentially exact.

TESTED: K1_Pnu(lam,z) := C(lam) * z^-2 * P_nu(2/z-1), same C(lam)=1/(1+lam^2)
and z=s/(s+t) framework as kinematic_block_attempt2.py, so the comparison
is apples-to-apples with the earlier (also-negative) attempt.

RESULT: lambda-parity is clean (P_nu shadow-even by construction, confirmed
numerically to ~1e-47). But the spectral integral vs box_exact ratio is
NOT constant across kinematic points (-0.0093-0.0064j, -0.0264-0.0310j,
-0.0254-0.0211j, -0.0061-0.0045j) -- even applying the already-established
(s+t)^-2 scale-fix from kinematic_block_scaling.py made it WORSE, not
better (more scattered ratios). Honest negative, not a match.

THE REAL LESSON, not a dead end: Theorem 3.1 gives the shadow-discontinuity
of a bare Legendre-Q object -- but the physically relevant object in the
untied/residue OPE-channel construction (residue_at_coincidence.py) is
L(Delta5), the Mellin-transformed TREE amplitude with the physical s
threshold built in (a genuine Beta-function integral, not a bare conformal
block). Theorem 3.1 was applied here to the bare block k_h(z) instead --
the well-scoped next step for a future session is expressing L(Delta5)
itself (or its residue-construction analog) in terms of Legendre
functions, THEN applying Theorem 3.1's shadow-difference identity to that,
rather than to the block alone. Not attempted here -- flagged precisely
rather than guessed at further tonight.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics

mp.mp.dps = 30


def z_from_p(p):
    p0, p1, p2, p3 = [mp.mpf(str(x)) for x in p]
    denom = p0 + p3
    return (p1 + 1j * p2) / denom if abs(denom) > mp.mpf('1e-12') else None


def cross_ratio_z_of_st(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    z2, z3, z4 = z_from_p(p2), z_from_p(p3), z_from_p(p4)
    return (z3 - z4) / (z2 - z4)


def k_chiral(h, z):
    return z ** h * mp.hyp2f1(h, h, 2 * h, z)


def verify_theorems():
    print("Independent re-verification of Theorem 2.1 and 3.1, fresh points:")
    for h, z in [(mp.mpf('0.5') + 1.1j, mp.mpf('0.2') - 0.3j),
                 (mp.mpf('0.5') + 3.7j, mp.mpf('-0.4') + 0.5j)]:
        lhs = k_chiral(h, z)
        rhs = 2 * mp.gamma(2 * h) / mp.gamma(h) ** 2 * mp.legenq(h - 1, 0, 2 / z - 1, type=3)
        print(f"  Thm 2.1, h={mp.nstr(h,4)} z={mp.nstr(z,4)}: |diff|={mp.nstr(abs(lhs-rhs),4)}")
    for lam, x in [(mp.mpf('2.3'), mp.mpf('1.7') + 0.4j), (mp.mpf('5.1'), mp.mpf('3.2') - 0.9j)]:
        nu = -mp.mpf('0.5') + 1j * lam / 2
        conn = (mp.legenq(-nu - 1, 0, x, type=3) - mp.legenq(nu, 0, x, type=3)) \
            - 1j * mp.pi * mp.tanh(mp.pi * lam / 2) * mp.legenp(nu, 0, x, type=3)
        print(f"  Thm 3.1, lam={lam} x={mp.nstr(x,4)}: |diff|={mp.nstr(abs(conn),4)}")


def plancherel(lam):
    lam = mp.mpf(lam)
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def box_exact(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    return (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)


def K1_Pnu(lam, z):
    lam = mp.mpc(lam)
    nu = -mp.mpf('0.5') + 1j * lam / 2
    x = 2 / z - 1
    Pv = mp.legenp(nu, 0, x, type=3)
    C = 1 / (1 + lam ** 2)
    return C * (z ** -2) * Pv


def main():
    verify_theorems()
    print()
    print("=" * 78)
    print("lambda-parity of K1_Pnu (should be even -- P_nu is shadow-even)")
    print("=" * 78)
    s_in, t_in = mp.mpf('3.0'), mp.mpf('-2.0')
    z = s_in / (s_in + t_in)
    for lam in [mp.mpf('0.7'), mp.mpf('2.3')]:
        Kp, Km = K1_Pnu(lam, z), K1_Pnu(-lam, z)
        print(f"  lam={lam}: |K1(+lam)-K1(-lam)|={mp.nstr(abs(Kp-Km),4)}")

    print()
    print("=" * 78)
    print("spectral integral vs box_exact, with and without the (s+t)^-2 scale fix")
    print("=" * 78)
    for s_in, t_in in [(3.0, -2.0), (5.0, -1.0), (4.0, -1.5), (2.0, -1.0)]:
        s_in, t_in = mp.mpf(s_in), mp.mpf(t_in)
        z = s_in / (s_in + t_in)
        exact = box_exact(s_in, t_in)
        integrand = lambda lam: plancherel(lam) * K1_Pnu(lam, z).real / (2 * mp.pi)
        I = mp.quad(integrand, [-30, -10, -3, -1, 0, 1, 3, 10, 30])
        ratio_raw = I / exact if exact != 0 else None
        ratio_scaled = (I / (s_in + t_in) ** 2) / exact if exact != 0 else None
        print(f"  s={s_in} t={t_in}: ratio(raw)={mp.nstr(ratio_raw,6)}  ratio(with (s+t)^-2)={mp.nstr(ratio_scaled,6)}")


if __name__ == "__main__":
    main()
