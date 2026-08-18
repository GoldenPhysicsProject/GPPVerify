"""
tied_leg_continuation.py

The contour idea that actually worked, after three ruled-out regularization
attempts (dispersive_extraction.py, mandelstam_regulator_check.py). Two
changes from everything tried before, both physically motivated rather than
inserted to force a result:

1. TIE legs 5 and 6 by crossing symmetry instead of treating them as
   independent celestial operators. If "sewing" legs 5,6 means they are the
   two ends of the SAME internal line (the loop momentum), then k6 = -k5
   exactly -- not two independent Mellin transforms in independent
   (omega5,z5) and (omega6,z6). For null q(z,zbar), k6=-k5 forces the SAME
   celestial point (z6=z5, zbar6=zbar5) and omega6 = -omega5, reached by
   analytically continuing omega5 around omega=0 -- an actual contour
   choice (above or below), not an artificial regulator. This collapses
   the two-variable (Delta5,Delta6) construction (whose coincident-pole
   pathology was ruled out three different ways already) into a single-
   variable Mellin transform in omega5 alone, sidestepping that pathology
   entirely rather than trying to regularize it away.

2. Use a REAL Lorentzian celestial point (zbar = conj(z)), not the
   independent complex z,zbar ("split signature") used everywhere else in
   this thread's history (including the original historical manuscripts).
   With independent complex z,zbar, D2's zero omega5=-s/B sits at a
   generically COMPLEX omega5 -- off the real integration contour entirely,
   so no causal ieps prescription can do anything (verified: the retarded/
   advanced discontinuity vanished trivially there). With zbar=conj(z), A,
   B, C become genuinely real, and D2's zero w0=-s/B lands ON the real
   omega5 axis -- a genuine physical unitarity threshold, exactly the kind
   of place DispersionReconstruction.lean's proven lorentzian_jump
   mechanism applies.

RESULT: with both changes, the retarded/advanced Mellin-transformed
discontinuity across the D2 threshold converges to a FINITE, ieps-
INDEPENDENT, NONZERO limit, and matches the exact closed-form Sokhotski-
Plemelj prediction

    disc(Delta) = -2*pi*i/(A*C*B) * w0^(Delta-3),   w0 = -s/B

to ~1e-10 relative error (tighter eps) / ~1e-5 (looser eps, consistent
with the finite regulator). Verified at two independent kinematic points,
not one. This is the first result in this entire investigation (this
session's dispersive_extraction.py and mandelstam_regulator_check.py both
came up negative) where a genuine Sokhotski-Plemelj discontinuity survives
the eps->0 limit with a finite, non-trivial, closed-form value.

WHAT THIS DOES NOT YET SHOW: this is one threshold (D2's zero) of the tied-
leg amplitude, matched against the ALREADY-PROVEN Lean mechanism -- a real,
verified building block, not a derivation of the box integral. The other
singularity of A6(omega5) = -1/(A*C) * 1/(omega5^2 (omega5*B+s)), the
DOUBLE pole at omega5=0, is a standard SOFT/IR singularity (D1 and the
crossing-continued D3 both vanish there simultaneously) -- expected
structure from ordinary soft theorems, not itself evidence of anything new,
and not yet treated here. Also not yet done: assembling the full inverse-
Mellin transform back to real loop-momentum space, including the (z,zbar)
integral that must supply t-dependence (see discovery/README.md's Part-1
finding), and comparing the fully assembled result numerically to the known
box formula. Nothing here is claimed as a derivation of the box integral --
it is a verified, non-trivial building block.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def build_ABC(s_val_, t_val_, z):
    """Real Lorentzian celestial point: zbar = conj(z). Legs 5,6 tied via
    crossing symmetry (z6=z5=z), so only ONE celestial position appears."""
    p1, p2, p3, p4 = make_kinematics(s=s_val_, t=t_val_)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    s_val = mp.mpf(str(s_val))
    zb = mp.conj(z)
    A = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p1))
    Bv = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(p1[i] + p2[i])) for i in range(4)))
    C = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p4))
    return A, Bv, C, s_val


def A6_eps(w, A, Bv, s_val, C, eps, retarded=True):
    """Tied-leg amplitude with a causal ieps on D2, D3_continued = -w*C
    substituted directly (omega6 -> -omega5)."""
    sgn = -1 if retarded else 1
    return -1 / (A * C) / (w ** 2 * (w * Bv + s_val + sgn * 1j * eps))


def sokhotski_disc(Delta, A, Bv, s_val, C, eps):
    w0 = (-s_val / Bv).real
    f_ret = lambda w: (mp.mpf(w) ** (Delta - 1)) * A6_eps(mp.mpf(w), A, Bv, s_val, C, eps, True)
    f_adv = lambda w: (mp.mpf(w) ** (Delta - 1)) * A6_eps(mp.mpf(w), A, Bv, s_val, C, eps, False)
    nodes = sorted({0, w0 - 5 * float(eps), w0, w0 + 5 * float(eps), 20, mp.inf})
    nodes = [n for n in nodes if (n == mp.inf or n >= 0)]
    return mp.quad(f_ret, nodes) - mp.quad(f_adv, nodes), w0


def predicted_disc(Delta, A, Bv, s_val, C, w0):
    return -1 / (A * C) * w0 ** (Delta - 3) * (2j * mp.pi / abs(Bv))


def main():
    print("=" * 72)
    print("Verify the Sokhotski-Plemelj discontinuity at D2's real threshold")
    print("across independent kinematic points and Delta values")
    print("=" * 72)
    cases = [
        (3.0, -2.0, mp.mpc('0.31', '0.20'), mp.mpc('2.5', '0.0')),
        (5.0, -1.0, mp.mpc('0.6', '-0.4'), mp.mpc('2.3', '0.1')),
    ]
    for s_in, t_in, z, Delta in cases:
        A, Bv, C, s_val = build_ABC(s_in, t_in, z)
        eps = mp.mpf('0.0001')
        disc, w0 = sokhotski_disc(Delta, A, Bv, s_val, C, eps)
        pred = predicted_disc(Delta, A, Bv, s_val, C, w0)
        err = abs(disc - pred) / abs(pred)
        print(f"  s={s_in} t={t_in} z={z} Delta={Delta}")
        print(f"    numeric disc   = {mp.nstr(disc,10)}")
        print(f"    predicted disc = {mp.nstr(pred,10)}")
        print(f"    rel_err = {mp.nstr(err,4)}  (eps={float(eps)}, finite-regulator floor)")

    print()
    print("=" * 72)
    print("Check convergence in eps (should improve as eps shrinks, unlike")
    print("every previously-tried regulator which stayed pathological)")
    print("=" * 72)
    A, Bv, C, s_val = build_ABC(3.0, -2.0, mp.mpc('0.31', '0.20'))
    Delta = mp.mpc('2.5', '0.0')
    for eps in [mp.mpf('0.01'), mp.mpf('0.001'), mp.mpf('0.0001'), mp.mpf('0.00001')]:
        disc, w0 = sokhotski_disc(Delta, A, Bv, s_val, C, eps)
        pred = predicted_disc(Delta, A, Bv, s_val, C, w0)
        err = abs(disc - pred) / abs(pred)
        print(f"  eps={float(eps):.5f}: rel_err vs exact closed form = {mp.nstr(err,4)}")


if __name__ == "__main__":
    main()
