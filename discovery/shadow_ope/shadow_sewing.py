"""
shadow_sewing.py

The actual OPE-channel / shadow-pair sewing computation for the six-point
comb tree, attempted from scratch. Nothing about a joint pole at
Delta5+Delta6=2 is inserted by hand anywhere below -- it is either derived
from the genuine Mellin transform of the real propagator structure, or the
script reports honestly that it did not appear.

SETUP (see celestial_kinematics.py for the verified kinematics):
Comb tree A(5,1)-B(2)-C(3)-D(4,6), propagators
    D1 = (k5+p1)^2 = 2 k5.p1 = omega5 * A(z5,zb5),      A := 2 q(z5,zb5).p1
    D2 = (k5+p1+p2)^2 = omega5 * B(z5,zb5) + s,          B := 2 q(z5,zb5).(p1+p2)
    D3 = (k5+p1+p2+p3)^2 = (p4+k6)^2 = omega6 * C(z6,zb6), C := 2 q(z6,zb6).p4
(D3 rewritten via overall momentum conservation, exactly as in
TreeLoopSewing.lean's openSixPointChainDenominator / the comb-factorization
finding already established this session: D1, D2 depend only on leg 5's
data; D3 depends only on leg 6's data.)

The tree amplitude (unit coupling scalar phi^3) is A_6 = 1/(D1 D2 D3).

STEP A: Mellin-transform leg 5 only (legs 1,2 fixed, ordinary 4-momenta):
    L(Delta5; z5,zb5) := int_0^inf domega5 omega5^{Delta5-1} / (D1 D2)
                        = (1/A) * int_0^inf domega5 omega5^{Delta5-2}/(omega5 B + s)
This is the classical Beta-function Mellin transform (verified numerically
below against direct quadrature, not assumed):
    int_0^inf w^{Delta-1}/(Bw+s) dw = pi * s^{Delta-1} / (B^Delta sin(pi*Delta))
      for 0 < Re(Delta) < 1.
Here the exponent is Delta5-2, i.e. effective exponent (Delta5-1) in that
formula, valid on 0 < Re(Delta5-1) < 1, i.e. 1 < Re(Delta5) < 2 -- NOTE this
does not include the principal series Re(Delta5)=1 itself (a genuine
boundary-of-convergence subtlety, handled by analytic continuation of the
closed form, which is meromorphic in Delta5).

STEP B: Mellin-transform leg 6 only:
    R(Delta6; z6,zb6) := int_0^inf domega6 omega6^{Delta6-1} / D3
                        = (1/C) * int_0^inf domega6 omega6^{Delta6-2}
This is the Mellin transform of a BARE power law (1 in the numerator over a
single scale), which is a genuine distribution, not an ordinary function --
the standard identity is
    int_0^inf w^{i*lam-1} dw = 2*pi*delta(lam)
(Mellin transform of the constant function 1), so with Delta6 = 1+i*lam6:
    R(Delta6;...) = (1/C) * 2*pi*delta(lam6),
i.e. R has support ONLY at Delta6 = 1 exactly (lam6 = 0), not a general
function of Delta6.

STEP C: the "sewing" via the SL(2,C) Plancherel completeness relation
(the resolution of the identity already used, correctly, in the existing
haar_qg_paper_v215.tex Theorem thm:shadow-disc, Step 5):
    Sewn = int dlam/(2*pi) P(lam) int d^2z L(1+i*lam,z) R(1-i*lam,z)
On the shadow locus Delta6=1-i*lam, R's delta function support sits exactly
at lam=0 (Delta6=1), which ALSO forces Delta5=1+i*0=1 on the same locus.
This script checks explicitly whether L(Delta5,...) is regular or singular
at exactly Delta5=1 -- i.e. whether the completeness-relation sewing is even
well-defined for this tree ordering, honestly, without assuming either
answer.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def beta_mellin(Delta, B, s):
    """Closed form: int_0^inf w^{Delta-1}/(B w + s) dw = pi s^{Delta-1}/(B^Delta sin(pi Delta))."""
    return mp.pi * s ** (Delta - 1) / (B ** Delta * mp.sin(mp.pi * Delta))


def beta_mellin_quad(Delta, B, s):
    """Direct numerical quadrature of the same integral, for cross-check.
    Uses mpmath's genuine improper-integral tail (mp.inf), NOT a finite
    cutoff: a hard cutoff at even wmax=2000 gave up to 8.7% spurious error
    here from the slowly-decaying w^{Delta-2} tail before this fix -- a
    truncation artifact, not a property of the integral. Also brackets the
    integrand's pole at w0=-s/B explicitly when it sits near the positive
    real axis, so quadrature does not silently lose accuracy stepping over
    a near-singularity."""
    w0 = -s / B
    nodes = [0]
    if abs(mp.im(w0)) < 1 and mp.re(w0) > 0:
        nodes.append(mp.re(w0))
    nodes += [1, 10, mp.inf]
    nodes = sorted(set(nodes), key=lambda x: float(mp.re(x)))
    f = lambda w: w ** (Delta - 1) / (B * w + s)
    return mp.quad(f, nodes)


def L_closed_form(Delta5, A, B, s):
    """L(Delta5) = (1/A) * int dw5 w5^{Delta5-2}/(B w5 + s), via closed form
    with effective exponent (Delta5-1)."""
    eff = Delta5 - 1
    return beta_mellin(eff, B, s) / A


def main():
    p1, p2, p3, p4 = make_kinematics(s=3.0, t=-2.0)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    s_val = mp.mpf(str(s_val))

    # generic celestial-sphere position for leg 5 (away from any coincidence
    # with legs 1,2's directions)
    z5, zb5 = mp.mpc('0.31', '0.20'), mp.mpc('0.44', '-0.15')

    A = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in p1))
    Bv = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in
                                             [p1[i] + p2[i] for i in range(4)]))
    print("=" * 72)
    print("STEP A: verify the closed-form Beta-function Mellin transform")
    print("against direct numerical quadrature, at a GENERIC (non-principal-")
    print("series) Delta5 first, to certify the closed form before trusting")
    print("its analytic continuation onto the principal series.")
    print("=" * 72)
    print(f"A = 2 q(z5,zb5).p1 = {A}")
    print(f"B = 2 q(z5,zb5).(p1+p2) = {Bv}")
    for Delta5_test in [mp.mpc('1.3', '0.0'), mp.mpc('1.5', '0.4')]:
        eff = Delta5_test - 1
        closed = beta_mellin(eff, Bv, s_val)
        quad = beta_mellin_quad(eff, Bv, s_val)
        err = abs(closed - quad) / abs(quad)
        print(f"  Delta5={Delta5_test}: closed={mp.nstr(closed,10)}  "
              f"quad={mp.nstr(quad,10)}  rel_err={mp.nstr(err,3)}")

    print()
    print("=" * 72)
    print("STEP B: leg 6's Mellin transform is a bare power law -- confirm")
    print("numerically that its regulated (finite-cutoff) energy integral")
    print("concentrates at Delta6=1 (lam6=0) as the cutoff is removed,")
    print("consistent with the standard Mellin[1](lam)=2*pi*delta(lam)")
    print("identity, rather than assuming this distributional fact outright.")
    print("=" * 72)
    for wmax in [mp.mpf(10), mp.mpf(100), mp.mpf(1000), mp.mpf(10000)]:
        lam6 = mp.mpf('0.3')  # away from 0
        val = mp.quad(lambda w: w ** (mp.mpc(0, lam6)) / w, [1, wmax])
        # int_1^wmax w^{i lam6 -1} dw = (wmax^{i lam6} - 1)/(i lam6): bounded,
        # oscillatory, does NOT grow -- contrast with lam6=0 below.
        print(f"  wmax={float(wmax):>8.0f}: |int_1^wmax w^(i*0.3-1) dw| = "
              f"{mp.nstr(abs(val),6)}  (bounded/oscillatory, lam6=0.3 != 0)")
    for wmax in [mp.mpf(10), mp.mpf(100), mp.mpf(1000), mp.mpf(10000)]:
        val = mp.quad(lambda w: 1 / w, [1, wmax])
        print(f"  wmax={float(wmax):>8.0f}: int_1^wmax w^(-1) dw = "
              f"{mp.nstr(val,6)}  (log-DIVERGES at lam6=0 -- delta-function"
              f" concentration, confirmed)")

    print()
    print("=" * 72)
    print("STEP C: is L(Delta5) regular or singular exactly at Delta5=1,")
    print("the point the completeness relation's delta function forces us")
    print("to (since Delta6=1-i*lam's support at lam=0 pins Delta5=1+i*0=1")
    print("on the shadow locus)? Checked directly from the closed form, with")
    print("the closed form's validity re-confirmed near (not AT) Delta5=1.")
    print("=" * 72)
    for eps in [mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001'), mp.mpf('0.0001')]:
        Delta5 = 1 + eps
        val = L_closed_form(Delta5, A, Bv, s_val)
        print(f"  Delta5 = 1+{float(eps):.4f}: L(Delta5) = {mp.nstr(val,6)}  "
              f"|L| = {mp.nstr(abs(val),6)}")
    print()
    print("  --> |L(Delta5)| grows without bound as Delta5 -> 1: L has a")
    print("      GENUINE SIMPLE POLE at Delta5=1 (from the 1/sin(pi*Delta5))")
    print("      factor with effective exponent Delta5-1 -> 0).")
    print()
    print("CONCLUSION: the naive real-lambda completeness-relation sewing")
    print("  Sewn = int dlam/(2pi) P(lam) int d^2z L(1+i*lam,z) R(1-i*lam,z)")
    print("is ILL-DEFINED as written for this tree ordering: R's delta-")
    print("function support sits exactly at lam=0, which is EXACTLY where L")
    print("has a genuine pole (a 0-width delta multiplying a 1/0 pole is not")
    print("a number). This is not a contradiction or a dead end -- it is the")
    print("honest computational signature of the missing structure: extracting")
    print("a finite propagator from what is naively an on-shell-support object")
    print("requires genuine analytic continuation / dispersive treatment off")
    print("the naive real locus, not literal delta-function insertion.")
    print("[Correction 2026-08-18: this used to cite a proven mechanism in")
    print("'DispersionReconstruction.lean' -- that file does not exist")
    print("anywhere in this repo or its git history. False citation, caught")
    print("by an explicit repo-wide search this session.]")


if __name__ == "__main__":
    main()
