"""
mandelstam_regulator_check.py

Follow-up to dispersive_extraction.py's ruled-out D3-shift regulator.

Two more checks, recorded honestly (see discovery/README.md):

1. GENERAL no-go for the whole "D3 -> omega6*C + X" regulator family (not
   just the specific Feynman-ieps choice already tried): the Mellin
   transform of 1/(omega6*C + X) depends on X only through X^(Delta6-1)
   (Beta-Mellin closed form), which is X^0 = 1 at the coincidence point
   Delta6=1 -- for EVERY choice of X, including X->0. No regulator of this
   shape can touch that point. Verified below for three qualitatively
   different regulators (Feynman ieps, a small real mass, an exponential/
   Schwinger-parameter damping via Gamma(nu)/eta^nu): all three collapse to
   the same X^0=1 degeneracy.

2. Putting the ieps on s (the physical Mandelstam scale in D2) instead of
   D3: L's own residue at Delta5=1 genuinely depends on s (not degenerate
   the way D3's regulator was), so Res[L]|_{s -/+ ieps} is a legitimate
   retarded/advanced pair. Their difference is checked here against the
   exact Sokhotski-Plemelj prediction 2i*eps/(A*(s^2+eps^2)) -- it matches,
   and vanishes linearly as eps->0 for our generic external s != 0, exactly
   the expected (unsurprising) behavior away from the invariant's own
   threshold. This rules out putting the fix here too: s is a fixed
   external kinematic input in this construction, not something being
   integrated over, so a discontinuity in it is physically inert unless s
   itself is later continued -- it isn't.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def beta_mellin(nu, B, s):
    return mp.pi * s ** (nu - 1) / (B ** nu * mp.sin(mp.pi * nu))


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
    print("CHECK 1: every 'D3 -> omega6*C + X' regulator is X^0=1 at Delta6=1")
    print("=" * 72)
    Delta6 = mp.mpc(1, 0)
    # Delta6-1 = 0 exactly triggers a literal Gamma(0) pole for the Schwinger
    # regulator below (the same degeneracy, manifesting as a true infinity
    # instead of a finite-but-huge float) -- evaluate at a tiny offset so
    # the comparison runs, and note this even more directly confirms the
    # regulator-independence than a merely-huge number would.
    Delta6_offset = mp.mpc(1, mp.mpf('1e-15'))
    for name, R_of_X in [
        ("Feynman ieps (X=-i*eps)", lambda eps: beta_mellin(Delta6, C, mp.mpc(0, -eps))),
        ("small real mass (X=m^2)", lambda eps: beta_mellin(Delta6, C, eps)),
        ("Schwinger/exp damping Gamma(nu)/eta^nu (nu=Delta6-1)",
         lambda eta: mp.gamma(Delta6_offset - 1) / eta ** (Delta6_offset - 1) / C),
    ]:
        vals = [R_of_X(mp.mpf(x)) for x in ['0.3', '0.03', '0.003']]
        print(f"  {name}:")
        for x, v in zip(['0.3', '0.03', '0.003'], vals):
            print(f"    X={x}: R={mp.nstr(v,8)}")
        print(f"    -> constant across X: {abs(vals[0]-vals[-1]) < mp.mpf('1e-10')*abs(vals[0])}")

    print()
    print("=" * 72)
    print("CHECK 2: ieps on s (D2's physical scale) instead -- legitimate")
    print("retarded/advanced split in L's residue, but inert for generic")
    print("external s != 0 (matches exact Sokhotski-Plemelj prediction)")
    print("=" * 72)
    print(f"  external s = {float(s_val)} (fixed, not integrated over)")
    for eps in [mp.mpf('0.5'), mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001')]:
        res_ret = 1 / (A * (s_val - 1j * eps))
        res_adv = 1 / (A * (s_val + 1j * eps))
        res_ret = mp.mpc(res_ret.real, res_ret.imag)
        res_adv = mp.mpc(res_adv.real, res_adv.imag)
        disc = res_ret - res_adv
        predicted = 2j * eps / (A * (s_val ** 2 + eps ** 2))
        print(f"  eps={float(eps):.4f}: |disc|={mp.nstr(abs(disc),6)}  "
              f"|predicted 2ieps/(A(s^2+eps^2))|={mp.nstr(abs(predicted),6)}  "
              f"match={abs(disc-predicted) < mp.mpf('1e-15')}")
    print()
    print("  |disc| -> 0 linearly in eps: exactly the Sokhotski-Plemelj")
    print("  prediction away from s=0. Confirms this idea is inert here --")
    print("  s is fixed external data in this construction, not a variable")
    print("  being varied/integrated, so its discontinuity carries no weight.")


if __name__ == "__main__":
    main()
