"""
kinematic_block_attempt2.py

Second attempt at K_1(lambda; s,t), correcting a concrete bug identified by
reading the full OPE-residue derivation across multiple source manuscripts
this session (celestial_qg_complete_v2.tex Prop 6.1 / "Loop Measure from
Shadow Discontinuity"; ONON521.tex sec:oneloop Proposition [shadow-residue]
and the explicit box derivation in sec:scalar-box-check). Both state the
shadow-pole residue as

    R(Delta_5) = C_{Delta1,Delta2,Delta5} * C_{Delta3,Delta4,(2-Delta5)}
                 * F_4(Delta1,Delta2,Delta5; u) * F_4(Delta3,Delta4,2-Delta5; v)

with F_4(Delta_a,Delta_b,Delta;w) = w^{(Delta-Delta_a-Delta_b)/2}
     * 2F1(Delta/2,Delta/2;Delta;w)   the ordinary 4-point conformal block
(NOT the plain chiral block k_h(z)=z^h*2F1(h,h;2h;z) used in
kinematic_block_attempt.py's first, failed try).

For external dimensions Delta1=Delta2=Delta3=Delta4=1 this simplifies to
    F_4(1,1,Delta;w) = w^{-1} * k_{Delta/2}(w),
so the SECOND block -- for leg 6 at Delta6=2-Delta5 -- carries weight
h'=(2-Delta5)/2 = 1-h, NOT h. kinematic_block_attempt.py's first pass used
k_h(z)*k_h(z) (same h twice); this is wrong; the shadow-paired leg's block
must use the shadow weight 1-h. That mismatch is a very plausible cause of
the earlier finding that K1(lambda=+1) and K1(lambda=-1) were not simply
related: under lambda -> -lambda, h=(1+i lambda)/2 -> (1-i lambda)/2 = 1-h,
so k_h(z)^2 is NOT manifestly even, while k_h(z)*k_{1-h}(z) IS (the swap
h<->1-h leaves the product invariant, and the 1/(1+lambda^2) OPE-coefficient
prefactor is already manifestly even). This is a genuine, checkable
correction, not a guess -- verified below by testing the symmetry directly
before ever comparing to the box.

Everything else (the z(s,t)=s/(s+t) cross-ratio, the OPE-coefficient
product C(lambda)=1/(1+lambda^2), the Plancherel weight) is carried over
unchanged from kinematic_block_attempt.py, since those were independently
verified there and not implicated in the parity failure.

Honest scope: this is a well-motivated SECOND attempt at an open problem,
not a claim that it is solved. Report the lambda-parity check and the
spectral-integral-vs-box comparison exactly as they come out, positive or
negative.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics

mp.mp.dps = 30


def z_from_p(p):
    p0, p1, p2, p3 = [mp.mpf(str(x)) for x in p]
    denom = p0 + p3
    return (p1 + 1j * p2) / denom if abs(denom) > mp.mpf('1e-12') else None


def cross_ratio_z_of_st(s_in, t_in):
    """z(s,t) = s/(s+t), verified exactly in kinematic_block_attempt.py Part 1."""
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    z2, z3, z4 = z_from_p(p2), z_from_p(p3), z_from_p(p4)
    cross = (z3 - z4) / (z2 - z4)  # z1 -> infinity limit
    return cross


def k_chiral(h, z):
    """k_h(z) = z^h * 2F1(h,h;2h;z), the plain chiral block."""
    return z ** h * mp.hyp2f1(h, h, 2 * h, z)


def K1_v2(lam, z):
    """Corrected residue: C(lambda) * z^{-2} * k_h(z) * k_{1-h}(z),
    h = (1+i lambda)/2, matching F_4(1,1,Delta5;z)*F_4(1,1,2-Delta5;z)
    for external dimensions all equal to 1."""
    lam = mp.mpc(lam)
    h = (1 + 1j * lam) / 2
    hs = 1 - h  # shadow weight for leg 6, Delta6 = 2-Delta5
    block_product = k_chiral(h, z) * k_chiral(hs, z)
    C = 1 / (1 + lam ** 2)
    return C * (z ** -2) * block_product


def plancherel(lam):
    lam = mp.mpf(lam)
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def box_exact(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    return (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)


def main():
    print("=" * 72)
    print("PART 1: lambda-parity check of the corrected residue K1_v2")
    print("=" * 72)
    s_in, t_in = mp.mpf('3.0'), mp.mpf('-2.0')
    z = s_in / (s_in + t_in)
    print(f"z = {z}")
    for lam in [mp.mpf('0.7'), mp.mpf('1.0'), mp.mpf('2.3'), mp.mpf('4.1')]:
        Kp = K1_v2(lam, z)
        Km = K1_v2(-lam, z)
        diff = abs(Kp - Km)
        print(f"  lambda={mp.nstr(lam,4)}: K1(+lam)={mp.nstr(Kp,10)}  "
              f"K1(-lam)={mp.nstr(Km,10)}  |diff|={mp.nstr(diff,4)}  "
              f"even={diff < mp.mpf('1e-20')}")

    print()
    print("=" * 72)
    print("PART 2: spectral integral vs exact box, several (s,t) points")
    print("=" * 72)
    for s_in, t_in in [(3.0, -2.0), (5.0, -1.0), (4.0, -1.5), (2.0, -1.0)]:
        s_in, t_in = mp.mpf(s_in), mp.mpf(t_in)
        z = s_in / (s_in + t_in)
        exact = box_exact(s_in, t_in)

        def integrand(lam):
            return plancherel(lam) * K1_v2(lam, z).real / (2 * mp.pi)

        I = mp.quad(integrand, [-30, -10, -3, -1, 0, 1, 3, 10, 30])
        ratio = I / exact if exact != 0 else None
        print(f"  s={s_in} t={t_in}: box_exact={mp.nstr(exact,10)}  "
              f"spectral_integral={mp.nstr(I,10)}  ratio={mp.nstr(ratio,8)}")


if __name__ == "__main__":
    main()
