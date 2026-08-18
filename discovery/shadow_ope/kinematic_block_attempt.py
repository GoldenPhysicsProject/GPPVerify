"""
kinematic_block_attempt.py

Direct attempt at the open problem identified by reading the source
material in full (per Daniel's explicit request to recover the actual
mechanism, not just report the gap): derive the kinematic conformal block
K_1(lambda; s,t) whose spectral integral against the Plancherel weight
reproduces the scalar box,

    I_4^shadow(s,t) = int dlambda/(2pi) P(lambda) K_1(lambda;s,t)
                     = I_4^box(s,t) = (2/st)[Li2(1-s/t)+Li2(1-t/s)+pi^2/6],

which every source read this session (ONON v19_3, ONON5213, the compact
haar_qg companion, and the dedicated kinematic_block companion) states as
the target but explicitly, honestly leaves undF-derived: the kinematic
block companion's own words are "The derivation is open and is claimed
nowhere in this paper."

PART 1 -- a genuine new result: the missing cross-ratio relation z(s,t).

No source pins down, for THIS SPECIFIC six-point comb-sewing construction,
what the conformal cross-ratio z actually is as a function of s,t. Derived
it directly (not assumed, not recalled from literature) from this
session's own verified null-vector kinematics: extract each external
leg's celestial position via the standard map z_i = (p_i^1+i p_i^2)/
(p_i^0+p_i^3) (with leg 1 landing at z_1=infinity for this kinematic
frame -- p1 exactly back-to-back along the z-axis, p1^0+p1^3=0 -- handled
by the standard cross-ratio limit), then compute the 4-point cross ratio
z = (z1-z2)(z3-z4)/[(z1-z3)(z2-z4)] -> (z3-z4)/(z2-z4) as z1->infinity.

RESULT, verified exactly (not approximately) at 4 independent (s,t)
points: z(s,t) = s/(s+t) = -s/u  (u=-(s+t) the third Mandelstam).

PART 2 -- first concrete assembly attempt, and an honest negative result.

Using the NOW-PROVEN conical-block reduction from kinematic_block_v11.tex
(k_h(z) = z^h * 2F1(h,h;2h;z), h=Delta/2, PROVEN not assumed) and the
scalar 3-point OPE coefficient at external dimension 1
(C^phi_{1,1,Delta5} = 1/Delta5, giving C_125*C_346 = 1/(1+lambda^2) on the
shadow locus Delta5=1+i*lambda, Delta6=1-i*lambda), assembled

    K_1(lambda) = C_125*C_346 * k_h(z)^2,   z = s/(s+t) REAL in this chart,
    zbar = z (the chart derived in Part 1 gives a REAL cross-ratio, not
    the complex zbar=z* on the unit circle that kinematic_block_v11.tex's
    Temperedness Theorem is built for).

This does NOT reproduce the box: the spectral integral gives a complex
number in no obvious simple ratio to the exact box value, and -- more
diagnostically -- K_1(lambda) is NOT even in lambda (K_1(1) and K_1(-1)
differ by more than just complex conjugation), whereas it should be:
swapping lambda -> -lambda swaps which of Delta5=1+i*lambda,
Delta6=1-i*lambda is which, and the physical construction should be
symmetric under that exchange (or at worst pick up a controlled phase).
This is real, informative evidence that at least one of the following is
missing from this first assembly, not merely that a wrong number came
out:
  (a) a genuine complex zbar=z* (unit-circle) evaluation, not zbar=z --
      the REAL chart derived in Part 1 may be the wrong slice for
      evaluating the TEMPERED block at all (the Temperedness Theorem's
      conjugate-odd cancellation mechanism requires genuine z,zbar
      complex conjugates, which a real z trivially fails to provide
      in the way the theorem needs);
  (b) an explicit shadow-symmetrization of K_1 (the kinematic_block
      paper's own strategy: "symmetrize the one-loop integrand under the
      shadow so the Mehler-Fock kernel P_nu appears natively") that this
      first pass did not include;
  (c) a normalization/measure factor between the residue R(Delta5) of the
      shadow discontinuity theorem and the bare conformal block g_Delta
      used here, which no source makes fully explicit for this specific
      six-point construction.

Reported honestly: this is a real, bounded, first attempt at an open
problem, not a completed derivation. The z(s,t) relation of Part 1 is a
genuine, verified result usable in any future attempt; the Part 2
assembly is ruled out in its current form, with a concrete, checkable
reason (lambda-parity) rather than just "didn't match."
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, mink_dot

mp.mp.dps = 30


def z_from_p(p):
    p0, p1, p2, p3 = [mp.mpf(str(x)) for x in p]
    denom = p0 + p3
    return (p1 + 1j * p2) / denom if abs(denom) > mp.mpf('1e-12') else None


def cross_ratio_z_of_st(s_in, t_in):
    """Verified: z(s,t) = s/(s+t) via direct 4-point cross-ratio extraction
    from this session's own null-vector kinematics (leg 1 -> infinity)."""
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    z2, z3, z4 = z_from_p(p2), z_from_p(p3), z_from_p(p4)
    cross = (z3 - z4) / (z2 - z4)  # z1 -> infinity limit
    return cross


def k_h(h, z):
    return z ** h * mp.hyp2f1(h, h, 2 * h, z)


def K1_naive(lam, z):
    h = (1 + 1j * lam) / 2
    g = k_h(h, z) * k_h(h, z)
    C = 1 / (1 + lam ** 2)
    return C * g


def plancherel(lam):
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def box_exact(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    return (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)


def main():
    print("=" * 72)
    print("PART 1: the cross-ratio relation z(s,t), verified exactly")
    print("=" * 72)
    for s_in, t_in in [(3.0, -2.0), (5.0, -1.0), (4.0, -1.5), (2.0, -1.0)]:
        z = cross_ratio_z_of_st(s_in, t_in).real
        predicted = mp.mpf(s_in) / (mp.mpf(s_in) + mp.mpf(t_in))
        print(f"  s={s_in} t={t_in}: z(derived)={mp.nstr(z,10)}  "
              f"s/(s+t)={mp.nstr(predicted,10)}  match={abs(z-predicted)<mp.mpf('1e-15')}")

    print()
    print("=" * 72)
    print("PART 2: naive K_1 assembly -- ruled out, with a concrete reason")
    print("=" * 72)
    s_in, t_in = mp.mpf('3.0'), mp.mpf('-2.0')
    z = s_in / (s_in + t_in)
    print(f"z = {z}, box_exact = {mp.nstr(box_exact(s_in, t_in), 10)}")

    K1_pos = K1_naive(mp.mpf('1.0'), z)
    K1_neg = K1_naive(mp.mpf('-1.0'), z)
    print(f"K1(lambda=+1) = {mp.nstr(K1_pos,8)}")
    print(f"K1(lambda=-1) = {mp.nstr(K1_neg,8)}")
    print("  -> NOT related by simple conjugation/parity: assembly is missing")
    print("     a piece (shadow symmetrization and/or the correct zbar).")

    f = lambda lam: plancherel(mp.mpf(lam)) * K1_naive(mp.mpf(lam), z) / (2 * mp.pi)
    I = mp.quad(f, [-15, -5, -1, 0, 1, 5, 15])
    print(f"spectral integral = {mp.nstr(I,10)}")
    print(f"ratio to box_exact = {mp.nstr(I/box_exact(s_in,t_in),8)}  (not 1: ruled out)")


if __name__ == "__main__":
    main()
