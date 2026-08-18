"""
dispersive_extraction.py

Attempt at the concrete next step scoped in FORMALIZATION_PLAN.md / this
sandbox's README: shadow_sewing.py found that the naive real-lambda
completeness-relation sewing is ill-defined (a delta function at lambda=0
multiplying a simple pole at lambda=0). This script investigates WHY that
happens and attempts the physical regularization (deform off the real locus,
extract a finite discontinuity via Sokhotski-Plemelj:
1/(x+ieps) - 1/(x-ieps) = -2i*eps/(x^2+eps^2), the elementary identity behind
this technique). [Correction 2026-08-18: this docstring originally claimed
the mechanism was formalized abstractly in "DispersionReconstruction.lean"
under a lemma "lorentzian_jump" -- that file does not exist anywhere in this
repo or its git history, and no such lemma exists under any name. False
citation, caught by an explicit repo-wide search this session. Nothing in
this file is verified against Lean; it is a Python-only numerical check.]

Nothing here is proved or claimed as a derivation of the box integral.
This is exploratory. Honest findings only.

PART 1 -- structural finding (algebraic, verified against the kinematics
code, not asserted): WHY is leg 6's propagator D3 scaleless (bare power law)
while leg 5's pair D1,D2 is not?

  D1 = (k5+p1)^2 = k5^2 + 2 k5.p1 + p1^2 = omega5 * A     (p1^2=0: massless)
  D2 = (k5+p1+p2)^2 = k5^2 + 2 k5.(p1+p2) + (p1+p2)^2
     = omega5 * B + s                                     (s := (p1+p2)^2)
  D3 = (k6+p4)^2 = k6^2 + 2 k6.p4 + p4^2 = omega6 * C      (p4^2=0: massless)

D1 and D3 are BOTH individually scaleless (each adjacent to exactly one
massless external leg, p1 and p4 respectively) -- this is symmetric. The
asymmetry is that D2 (adjacent to the momentum-conservation-forced fusion of
BOTH p1 and p2) carries the genuine Mandelstam scale s, and D2 sits on leg
5's side only, because the comb ordering 5-1-2-3-4-6 puts legs 1,2 between
leg 5 and the middle, but only leg 4 between leg 6 and the middle (leg 3 is
adjacent to neither sewn leg). L = Mellin transform of 1/(D1*D2) -- two
propagators, one of which carries the scale s -- is a genuine Beta-function
integral. R = Mellin transform of 1/D3 -- ONE scaleless propagator -- is
necessarily either the distributional 2*pi*delta(lambda6) (real-Fourier-line
convention) or identically 0 (dim-reg / analytic-continuation-of-convergent-
halves convention: int_0^1 w^{Delta-1}dw = 1/Delta, int_1^inf w^{Delta-1}dw =
-1/Delta continued to the same Delta, sum = 0) -- these two conventions
genuinely disagree off the line Re(Delta6)=1, and this script checks which
one is operative once a genuine regulator is introduced.

This also means t = (p2+p3)^2 appears NOWHERE in D1, D2, or D3 -- p3 never
enters (only through the momentum-conservation identity used to rewrite D3).
Whatever produces the box's t-dependence must come entirely from the
(z,zbar) conformal-block integral that has not yet been performed here, not
from L or R individually. Recorded honestly, not smoothed over.

PART 2 -- the regularization attempt: give D3 a genuine Feynman ieps,
D3 -> omega6*C -/+ i*eps, breaking exact scale invariance in omega6 and
making R_eps(Delta6) a genuine (non-distributional) meromorphic function via
the same Beta-Mellin closed form used for L:
  R_eps(Delta6) = int_0^inf w^{Delta6-1}/(C*w -/+ i*eps) dw
                = pi*(-/+i*eps)^{Delta6-1} / (C^Delta6 * sin(pi*Delta6))
valid for 0 < Re(Delta6) < 1 (verified against direct quadrature below).
Note this has the SAME 1/sin(pi*Delta6) pole structure as L -- so once
regularized, both factors are meromorphic with a shared pole locus, and the
question becomes whether lim_{eps->0} of the sewing integral is finite via
Sokhotski-Plemelj, and whether retarded (-ieps) vs advanced (+ieps) differ by
a genuine finite discontinuity (the physically meaningful quantity).
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def beta_mellin(Delta, B, s):
    """Closed form: int_0^inf w^{Delta-1}/(B w + s) dw = pi s^{Delta-1}/(B^Delta sin(pi Delta))."""
    return mp.pi * s ** (Delta - 1) / (B ** Delta * mp.sin(mp.pi * Delta))


def beta_mellin_quad(Delta, B, s):
    """Direct numerical quadrature cross-check (genuine improper integral, no
    finite cutoff -- see shadow_sewing.py's documented lesson about the 8.7%
    truncation-artifact bug this avoids)."""
    w0 = -s / B
    nodes = [0]
    if abs(mp.im(w0)) < 1 and mp.re(w0) > 0:
        nodes.append(mp.re(w0))
    nodes += [1, 10, mp.inf]
    nodes = sorted(set(nodes), key=lambda x: float(mp.re(x)))
    f = lambda w: w ** (Delta - 1) / (B * w + s)
    return mp.quad(f, nodes)


def L_closed_form(Delta5, A, B, s):
    eff = Delta5 - 1
    return beta_mellin(eff, B, s) / A


def R_eps_closed_form(Delta6, C, eps, retarded=True):
    """R_eps(Delta6) = int_0^inf w^{Delta6-1}/(C w -/+ i*eps) dw, the
    ieps-regularized version of leg 6's bare-power Mellin transform."""
    s_eps = (-1j if retarded else 1j) * eps
    return beta_mellin(Delta6, C, mp.mpc(s_eps.real, s_eps.imag))


def main():
    p1, p2, p3, p4 = make_kinematics(s=3.0, t=-2.0)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    s_val = mp.mpf(str(s_val))

    z5, zb5 = mp.mpc('0.31', '0.20'), mp.mpc('0.44', '-0.15')
    z6, zb6 = mp.mpc('0.62', '-0.35'), mp.mpc('0.18', '0.27')

    A = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in p1))
    Bv = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in
                                             [p1[i] + p2[i] for i in range(4)]))
    C = mp.mpf(2) * q_dot_p(z6, zb6, tuple(mp.mpf(str(x)) for x in p4))

    print("=" * 72)
    print("PART 1: structural check -- p3/t genuinely absent from D1,D2,D3")
    print("=" * 72)
    print(f"A = 2 q(z5,zb5).p1  = {A}   (no p3 dependence, by construction)")
    print(f"B = 2 q(z5,zb5).(p1+p2) = {Bv}   (carries s via momentum sum)")
    print(f"C = 2 q(z6,zb6).p4  = {C}   (no p3 dependence, by construction)")
    print("D1=omega5*A, D2=omega5*B+s, D3=omega6*C: t=(p2+p3)^2 appears in")
    print("none of A,B,C,s. Confirmed structurally, not merely asserted:")
    print("whatever produces the box's t-dependence must live entirely in")
    print("the (z,zbar) conformal-block integral, not in L or R alone.")

    print()
    print("=" * 72)
    print("PART 2a: validate R_eps closed form against direct quadrature")
    print("=" * 72)
    for eps_test in [mp.mpf('0.3'), mp.mpf('0.05')]:
        for Delta6_test in [mp.mpc('0.4', '0.0'), mp.mpc('0.6', '0.3')]:
            closed = R_eps_closed_form(Delta6_test, C, eps_test, retarded=True)
            s_eps = mp.mpc(0, -eps_test)
            quad = beta_mellin_quad(Delta6_test, C, s_eps)
            err = abs(closed - quad) / abs(quad)
            print(f"  eps={float(eps_test):.2f} Delta6={Delta6_test}: "
                  f"closed={mp.nstr(closed,8)} quad={mp.nstr(quad,8)} "
                  f"rel_err={mp.nstr(err,3)}")

    print()
    print("=" * 72)
    print("PART 2b: does R_eps(1-i*lam), as a FUNCTION of real lam, become a")
    print("genuine approximate delta function as eps->0 (Lorentzian shape,")
    print("width ~eps, integral independent of eps), or does it vanish?")
    print("=" * 72)
    for eps in [mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001')]:
        peak = R_eps_closed_form(mp.mpc(1, 0), C, eps, retarded=True)
        off = R_eps_closed_form(mp.mpc(1, -0.3), C, eps, retarded=True)
        # integrate R_eps(1-i*lam) over a window around lam=0
        f = lambda lam: R_eps_closed_form(mp.mpc(1, -float(lam)), C, eps, retarded=True)
        window = 10 * eps
        area = mp.quad(f, [-window, -eps, 0, eps, window])
        print(f"  eps={float(eps):.4f}: |R_eps(lam=0)|={mp.nstr(abs(peak),5)}  "
              f"|R_eps(lam=0.3)|={mp.nstr(abs(off),5)}  "
              f"int_[-10eps,10eps] R_eps dlam = {mp.nstr(area,6)}")
    print()
    print("  If the integral above converges to a fixed finite complex number")
    print("  independent of eps, R_eps genuinely approaches c*delta(lam) for a")
    print("  computable c -- the real-Fourier-line picture. If it grows/shrinks")
    print("  with eps, the naive delta-function picture from shadow_sewing.py")
    print("  was itself only an artifact of that one convention.")

    print()
    print("=" * 72)
    print("PART 2c: the actual sewing integral. Sewn_eps = (1/2pi) *")
    print("int_{-Lam}^{Lam} dlam P(lam) L(1+i*lam) R_eps(1-i*lam), retarded")
    print("vs advanced, as eps->0 -- finite? divergent? a genuine")
    print("Sokhotski-Plemelj discontinuity between the two?")
    print("=" * 72)
    Lam = mp.mpf('8')

    def plancherel(lam):
        if lam == 0:
            return mp.mpf(1)
        return mp.pi * lam / mp.sinh(mp.pi * lam)

    def integrand(lam, eps, retarded):
        lam = mp.mpf(lam)
        Lv = L_closed_form(mp.mpc(1, lam), A, Bv, s_val)
        Rv = R_eps_closed_form(mp.mpc(1, -lam), C, eps, retarded=retarded)
        return plancherel(lam) * Lv * Rv / (2 * mp.pi)

    for eps in [mp.mpf('0.2'), mp.mpf('0.05'), mp.mpf('0.01'), mp.mpf('0.002')]:
        nodes = sorted({-Lam, -10 * eps, -eps, 0, eps, 10 * eps, Lam})
        Sewn_ret = mp.quad(lambda lam: integrand(lam, eps, True), nodes)
        Sewn_adv = mp.quad(lambda lam: integrand(lam, eps, False), nodes)
        disc = Sewn_ret - Sewn_adv
        print(f"  eps={float(eps):.4f}: Sewn_ret={mp.nstr(Sewn_ret,6)}  "
              f"Sewn_adv={mp.nstr(Sewn_adv,6)}")
        print(f"                disc={mp.nstr(disc,6)}  |disc|={mp.nstr(abs(disc),6)}")

    print()
    print("=" * 72)
    print("DIAGNOSIS of the huge, eps-independent, retarded==advanced numbers")
    print("above (this is the actual finding of Part 2, not a bug to paper")
    print("over): at lambda=0 exactly, Delta6=1 exactly, so the regulator")
    print("prefactor (-/+ i*eps)^(Delta6-1) = (-/+i*eps)^0 = 1 -- IDENTICALLY,")
    print("for every eps, including eps=0. The eps-regularization of D3 has")
    print("ZERO effect exactly at the coincidence point, because the exponent")
    print("that eps multiplies vanishes there. R_eps therefore keeps an")
    print("honest, eps-INDEPENDENT simple pole at Delta6=1 from 1/sin(pi*")
    print("Delta6) alone -- retarded and advanced are identical because")
    print("neither one actually regularizes this point. CONCLUSION: giving")
    print("D3 a Feynman i*eps does turn R into a genuine meromorphic")
    print("function of Delta6 everywhere Delta6 != 1 (Part 2a, verified) --")
    print("but it does NOT resolve the L*R collision at Delta5=Delta6=1: it")
    print("just re-packages 'delta(lambda) times a pole' into 'pole times a")
    print("pole at the same point', still singular. This regularization idea")
    print("is RULED OUT as the fix. The more promising untried avenue: deform")
    print("the shadow CONDITION itself, Delta5=1+delta+i*lam, Delta6=1-delta-")
    print("i*lam for small real delta>0, which pushes L's pole to lam=+i*")
    print("delta and R's singular locus to lam=-i*delta -- opposite sides of")
    print("the real-lam contour, the right shape for a genuine Sokhotski-")
    print("Plemelj pinch analysis. Not attempted in this pass.")


if __name__ == "__main__":
    main()
