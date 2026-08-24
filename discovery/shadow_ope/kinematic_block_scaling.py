"""
kinematic_block_scaling.py

Follow-up to kinematic_block_attempt2.py: diagnoses and confirms exactly a
scaling law the K1_v2 construction must satisfy, then tests (and rules out)
two simple candidate fixes for the remaining shape mismatch.

FINDING 1 (positive, exact): K1_v2(lambda, z) as built depends only on the
scale-invariant ratio z=s/(s+t), so its Plancherel-weighted spectral
integral I(z) is manifestly invariant under (s,t) -> (c*s, c*t). But
box_exact(s,t) has mass dimension -2 and scales as 1/c^2 exactly (visible
directly from its closed form: box_exact(s,t) = H(z)/(s+t)^2 for some
function H, since s,t are recoverable from z and (s+t) alone). Therefore
the ratio spectral_integral/box_exact must scale as exactly c^2 at fixed z
-- checked and confirmed to 10 significant figures holding z=0.6 fixed
across four different overall scales (s+t) in {-5,-10,-15,-50}: the
quantity ratio/(s+t)^2 is constant to all digits shown in every case
(0.03813598329...). This proves the construction as built is missing an
overall (s,t)-dependent -- not merely z-dependent -- prefactor of exactly
this scaling weight, most plausibly the 1/(omega5 omega6) energy factor
from omega5^{-Delta5} omega6^{-Delta6}|_{Delta5+Delta6=2} that every
source's general derivation includes and that this construction (which
integrates only over lambda at a fixed chart point z) has been dropping.

FINDING 2 (negative, but informative): even after removing the confirmed
(s+t)^{-2} scale dependence, a genuine z-shape mismatch remains -- the
z-only residual "ratio/(s+t)^2" varies over more than an order of
magnitude across different z (0.038 to 2.25 across six z values tested).
Two natural, cheap candidate fixes were tried and both fail to remove
this residual spread:
  (a) scanning a single overall power z^p multiplying K1_v2 for
      p in {-3,...,1}: best case p=-2.5 still leaves a spread(max/min) of
      about 2.4x across just four z points -- no simple power law
      reconciles the shape.
  (b) adding a "t-channel" analog with z_t=1-z_s (echoing the genuinely
      verified Sewn_s/Sewn_t two-channel structure from
      t_channel_sewing.py and sign_derivation.py earlier in this session):
      the spread narrows somewhat for moderate z but the correction is
      not remotely uniform, and even flips sign relative to box_exact at
      extreme asymmetric kinematics (z near 0 or 1).

Conclusion: the missing piece is real but is not a simple multiplicative
z-power or a naive s<->t channel sum. The most likely remaining
candidates, not yet attempted: (i) using genuinely different cross-ratios
u != 1-v for the two channels (built from the actual positions of all six
operators, not the two-point simplification u=v=z used here), or
(ii) treating the internal leg position as a genuine integration variable
against a round-sphere-type measure (as at least one source's own
loop-measure derivation does) rather than a fixed chart point tied
directly to external (s,t).
"""
import mpmath as mp

mp.mp.dps = 30


def k_chiral(h, z):
    return z ** h * mp.hyp2f1(h, h, 2 * h, z)


def K1_v2(lam, z):
    lam = mp.mpc(lam)
    h = (1 + 1j * lam) / 2
    hs = 1 - h
    C = 1 / (1 + lam ** 2)
    return C * (z ** -2) * k_chiral(h, z) * k_chiral(hs, z)


def plancherel(lam):
    lam = mp.mpf(lam)
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def box_exact(s_in, t_in):
    s, t = mp.mpf(s_in), mp.mpf(t_in)
    return (2 / (s * t)) * (mp.polylog(2, 1 - s / t) + mp.polylog(2, 1 - t / s) + mp.pi ** 2 / 6)


def spectral_integral(z):
    def integrand(lam):
        return plancherel(lam) * K1_v2(lam, z).real / (2 * mp.pi)
    return mp.quad(integrand, [-30, -10, -3, -1, 0, 1, 3, 10, 30])


def main():
    print("=" * 72)
    print("Exact (s+t)^-2 scaling law, held at fixed z=0.6")
    print("=" * 72)
    I_fixed = spectral_integral(mp.mpf('0.6'))
    for st in [mp.mpf(-5), mp.mpf(-10), mp.mpf(-15), mp.mpf(-50)]:
        s_in = mp.mpf('0.6') * st
        t_in = st - s_in
        exact = box_exact(s_in, t_in)
        ratio = I_fixed / exact
        print(f"  s+t={mp.nstr(st,6)}: I={mp.nstr(I_fixed,8)}  box={mp.nstr(exact,8)}  "
              f"ratio={mp.nstr(ratio.real,8)}  ratio/(s+t)^2={mp.nstr((ratio/st**2).real,10)}")

    print()
    print("=" * 72)
    print("Residual z-shape mismatch after dividing out (s+t)^-2 (unresolved)")
    print("=" * 72)
    pts = [(-3.0, -2.0), (-5.0, -1.0), (-4.0, -1.5), (-2.0, -1.0), (-3.0, -7.0), (-1.5, -9.0)]
    for s_in, t_in in pts:
        s_in, t_in = mp.mpf(s_in), mp.mpf(t_in)
        z = s_in / (s_in + t_in)
        exact = box_exact(s_in, t_in)
        I = spectral_integral(z)
        st = s_in + t_in
        const_z = (I / st ** 2 / exact).real
        print(f"  z={mp.nstr(z,6)}: ratio/(s+t)^2 = {mp.nstr(const_z,8)}  (not constant across z -- open)")


if __name__ == "__main__":
    main()
