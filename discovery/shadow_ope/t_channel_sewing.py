"""
t_channel_sewing.py

Direct answer to the "t can never appear" finding in
tied_leg_continuation.py / discovery/README.md, found by testing a
different possibility rather than assuming the full 6-point-all-celestial
rebuild was required: t doesn't need a bigger construction, it needs a
DIFFERENT comb ordering.

The original comb A(5,1)-B(2)-C(3)-D(4,6) puts legs 1,2 adjacent to the
sewn leg 5, so the middle propagator is D2=(k5+p1+p2)^2=w*B+s -- only s
can ever appear, and the exact identity p1+p2+p3=-p4 forces D3 to depend
on p4 alone, never p3/t (proved rigorously in the prior finding).

Swap which legs sit next to leg 5: comb A(5,2)-B(3)-C(1)-D(4,6), i.e. the
ordering 5-2-3-1-4-6. Now:
  D1' = (k5+p2)^2 = w*A'                          (A' = 2 q.p2)
  D2' = (k5+p2+p3)^2 = w*B'' + t                   (B''=2 q.(p2+p3), and
                                                     (p2+p3)^2 = t EXACTLY)
  D3' = (k5+p2+p3+p1)^2 = (k5-p4)^2 = -w*C         (UNCHANGED -- D3 only
                                                     ever sees p4, by the
                                                     same momentum-
                                                     conservation identity,
                                                     regardless of how
                                                     1,2,3 are ordered
                                                     among themselves)

This is the SAME tied-leg + real-Lorentzian-slice + causal-ieps-on-the-
affine-propagator + principal-series machinery as
tied_leg_continuation.py / principal_series_sewing.py, applied verbatim
with (A,B,s) -> (A',B'',t). Verified against the same two independent
checks (eps->0 discontinuity vs the exact closed form, and direct
lambda-integral quadrature vs the sech^2 closed form) -- both match to
~1e-9 / ~1e-31 respectively, same precision as the s-channel result.

RESULT: Sewn_t = -i*pi/(2*A'*C*B'') * w0_t^-2 * sech(ln(w0_t)/2)^2,
w0_t = -t/B''. Genuinely t-dependent, doubly verified, same precision as
the s-channel Sewn. Note the sign of the imaginary part is OPPOSITE the
s-channel result at the same kinematic point (checked: Sewn_s is negative
imaginary, Sewn_t is positive imaginary at s=3,t=-2) -- not yet explained,
recorded honestly rather than glossed over.

STILL NOT SHOWN: whether Sewn_s and Sewn_t combine (sum, difference, or
some other combination weighted by additional structure not yet
identified) into anything resembling the actual crossing-symmetric box
formula I_4(s,t) = (2/st)[Li2(1-s/t)+Li2(1-t/s)+pi^2/6], which is manifestly
symmetric under s<->t. Not attempted here -- would need the (z,zbar)
integral (still missing from both channels) done first, since Sewn_s and
Sewn_t as computed are each still functions of one fixed z, not
z-integrated, and comparing un-integrated quantities to the box directly
would not be a meaningful test.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def build_t_channel(s_in, t_in, z):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    t_val = mink_dot(tuple(p2[i] + p3[i] for i in range(4)),
                      tuple(p2[i] + p3[i] for i in range(4)))
    t_val = mp.mpf(str(t_val))
    zb = mp.conj(z)
    Ap = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p2))
    Bpp = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(p2[i] + p3[i])) for i in range(4)))
    C = mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p4))
    return Ap, Bpp, C, t_val


def plancherel(lam):
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def A6_eps(w, A, B, scale, C, eps, retarded=True):
    sgn = -1 if retarded else 1
    return -1 / (A * C) / (w ** 2 * (w * B + scale + sgn * 1j * eps))


def disc_closed_form(Delta, A, B, C, w0):
    return -2j * mp.pi / (A * C * B) * w0 ** (Delta - 3)


def sewn_closed_form(A, B, C, w0):
    x = mp.log(w0)
    return -1j * mp.pi / (2 * A * C * B) * w0 ** (-2) * mp.sech(x / 2) ** 2


def main():
    cases = [
        (3.0, -2.0, mp.mpc('0.31', '0.20')),
        (4.0, -1.5, mp.mpc('-0.15', '0.35')),
    ]
    for s_in, t_in, z in cases:
        A, B, C, t_val = build_t_channel(s_in, t_in, z)
        w0 = (-t_val / B).real
        if w0 <= 0:
            print(f"s={s_in} t={t_in} z={z}: w0_t<=0, not on physical branch, skip")
            continue
        print(f"s={s_in} t={t_in} z={z}: w0_t = -t/B'' = {float(w0):.6f}")

        eps = mp.mpf('0.0001')
        Delta = mp.mpc('2.5', '0.0')
        f_ret = lambda w: (mp.mpf(w) ** (Delta - 1)) * A6_eps(mp.mpf(w), A, B, t_val, C, eps, True)
        f_adv = lambda w: (mp.mpf(w) ** (Delta - 1)) * A6_eps(mp.mpf(w), A, B, t_val, C, eps, False)
        nodes = sorted({0, w0 - 5 * float(eps), w0, w0 + 5 * float(eps), 20, mp.inf})
        nodes = [n for n in nodes if (n == mp.inf or n >= 0)]
        disc_num = mp.quad(f_ret, nodes) - mp.quad(f_adv, nodes)
        disc_pred = disc_closed_form(Delta, A, B, C, w0)
        err1 = abs(disc_num - disc_pred) / abs(disc_pred)
        print(f"  disc check: numeric={mp.nstr(disc_num,8)}  closed={mp.nstr(disc_pred,8)}  rel_err={mp.nstr(err1,4)}")

        Sewn_closed = sewn_closed_form(A, B, C, w0)
        f = lambda lam: plancherel(mp.mpf(lam)) * disc_closed_form(mp.mpc(1, lam), A, B, C, w0) / (2 * mp.pi)
        Sewn_num = mp.quad(f, [-30, -5, 0, 5, 30])
        err2 = abs(Sewn_num - Sewn_closed) / abs(Sewn_closed)
        print(f"  Sewn_t (closed) = {mp.nstr(Sewn_closed,10)}   Sewn_t (quad) = {mp.nstr(Sewn_num,10)}   rel_err={mp.nstr(err2,4)}")


if __name__ == "__main__":
    main()
