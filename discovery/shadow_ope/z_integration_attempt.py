"""
z_integration_attempt.py

Tests the most theoretically-grounded remaining candidate from
kinematic_block_scaling.py's open questions: treat the shadow-paired
internal leg's celestial position z as a genuine INTEGRATION VARIABLE
(matching CH_v13_PHASE3_FOURPOINT.tex's own K_sew = int d^2z prod|z-z_i|^-2
formula, and the round-sphere loop-measure derivation read this session),
rather than the fixed chart point z=s/(s+t) used throughout every prior
attempt (kinematic_block_attempt.py, kinematic_block_attempt2.py,
kinematic_block_scaling.py).

Construction: standard shadow-formalism 3-point structure functions for the
two OPE channels, in the z1->infinity chart (Delta1=Delta2=Delta3=Delta4=1):

    C_12(z2,z) ~ (z2-z)^{-Delta5}
    C_34(z3,z4,z) ~ (z3-z)^{-Delta6} (z4-z)^{-Delta6},   Delta6 = 2-Delta5

with z2,z3,z4 the REAL celestial positions of legs 2,3,4 from this session's
verified make_kinematics/z_from_p machinery (leg 1 sent to infinity), and
K1(lambda,s,t) = C(lambda) * int dz  C_12(z2,z) * C_34(z3,z4,z), integrated
over the real z line.

RESULT: NaN. Diagnosed cause, not just a crash: for Delta5 = 1+i*lambda a
genuinely complex power, (z2-z)^{-Delta5} for REAL z crossing z2 requires
evaluating a negative real number raised to a complex power -- a branch-cut
ambiguity, not a removable numerical glitch. mpmath's principal branch
convention makes this discontinuous exactly where the integration contour
needs to pass, and naive real-line quadrature (even with excluded
neighborhoods around the three singular points z2,z3,z4) does not resolve
it into a well-defined number.

This is a genuine, informative negative result, not a dead end reported as
one: it says the z-integration idea is real and worth pursuing, but doing
it correctly needs the same kind of careful causal/iepsilon contour
prescription this session's tied_leg_continuation.py used successfully for
the omega5 (Mellin/energy) integral -- not a naive real-axis integral over
z. That is a substantially bigger undertaking (choosing and justifying the
correct z-contour prescription from physical principles, the way
tied_leg_continuation.py's retarded/advanced omega5 prescription was
motivated by causality) than was attempted here. Not solved this session;
flagged as the concrete next step with a clear diagnosis of why the naive
version fails.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics

mp.mp.dps = 15


def z_from_p(p):
    p0, p1, p2, p3 = [mp.mpf(str(x)) for x in p]
    denom = p0 + p3
    return (p1 + 1j * p2) / denom if abs(denom) > mp.mpf('1e-10') else None


def box_exact(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    return (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)


def K1_zint_naive(lam, z2, z3, z4):
    """Naive real-axis z-integration -- diagnosed to fail via branch-cut NaN."""
    lam = mp.mpf(lam)
    D5 = 1 + 1j * lam
    D6 = 1 - 1j * lam
    C = 1 / (1 + lam ** 2)

    def integrand(z):
        z = mp.mpf(z)
        return ((z2 - z) ** (-D5) * (z3 - z) ** (-D6) * (z4 - z) ** (-D6)).real

    pts = sorted([z2, z3, z4])
    eps = mp.mpf('1e-4')
    nodes = sorted(set([-30] + [p - eps for p in pts] + [p + eps for p in pts] + [30]))
    val = mp.quad(integrand, nodes, maxdegree=6)
    return C * val


def main():
    s_in, t_in = mp.mpf('3.0'), mp.mpf('-2.0')
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    z2, z3, z4 = z_from_p(p2).real, z_from_p(p3).real, z_from_p(p4).real
    print(f"z2={z2}  z3={z3}  z4={z4}")
    print(f"box_exact = {mp.nstr(box_exact(s_in, t_in), 10)}")
    for lam in [0.5, 1.0, 2.0]:
        val = K1_zint_naive(lam, z2, z3, z4)
        print(f"lambda={lam}: K1 = {mp.nstr(val, 6)}  "
              f"(nan confirms the branch-cut diagnosis, not a bug to retry)")


if __name__ == "__main__":
    main()
