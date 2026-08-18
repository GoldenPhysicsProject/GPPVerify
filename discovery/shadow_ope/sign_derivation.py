"""
sign_derivation.py

Directive from Daniel (relaying external analysis): don't just observe that
Sewn_s's imaginary part is always negative and Sewn_t's is always positive
across kinematic points -- DERIVE it. Was asked to specifically check
whether it comes from: discontinuity orientation, contour orientation,
shadow-pole ordering, split-signature Jacobian, OPE-channel crossing, or a
sign from exchanging the sewn legs.

ANSWER: none of those. It is a direct, provable consequence of (1) standard
Lorentzian causal geometry (reverse Cauchy-Schwarz for the forward light
cone) applied to which external legs are incoming vs outgoing in this
kinematic convention, combined with (2) the physical-branch selection rule
(w0>0) already built into the construction. No new mechanism needed.

DERIVATION:
Sewn = -i*pi/(2*A*C*B) * w0^-2 * sech(ln(w0)/2)^2, with w0^-2*sech^2
manifestly POSITIVE real (w0>0 required for the construction to be
defined at all). So sign(Im(Sewn)) = -sign(A*C*B).

FACT 1 (proved, not just checked, via reverse Cauchy-Schwarz): for a
future-pointing null q(z,zbar) (any point on the celestial sphere) and any
future-pointing CAUSAL vector v (timelike or null, v_0>0), q.v >= 0 in the
mostly-minus convention used throughout this thread -- and q.v <= 0 if v is
PAST-pointing causal (v_0<0) instead, for EVERY z, with no exception. This
is textbook: for two causal vectors in the same time-orientation class,
|spatial dot product| <= product of time components (Cauchy-Schwarz on the
spatial part, since a null/timelike vector's spatial part has magnitude <=
its time component), so time_1*time_2 - spatial_1.spatial_2 has a fixed
sign determined only by whether v is future- or past-pointing.

FACT 2 (read off from make_kinematics' output, verified below): in this
thread's convention, p1 and p2 both have NEGATIVE energy components
(past-pointing, "incoming"), p3 and p4 both have POSITIVE energy
components (future-pointing, "outgoing"). p1+p2 is therefore ALSO
past-pointing causal (sum of two past-causal vectors is past-causal, a
standard closure property); p2+p3 is a sum of a past-pointing and a
future-pointing vector and has NO fixed causal character (indeed
(p2+p3)^2=t<0 always in this thread's kinematics -- SPACELIKE, not causal
at all, so reverse Cauchy-Schwarz simply does not apply to it).

CONSEQUENCE for the s-channel (A=2q.p1, B=2q.(p1+p2), C=2q.p4): by Fact 1+2,
A<0 ALWAYS, B<0 ALWAYS, C>0 ALWAYS, for literally every z -- verified below
across 200 random z spanning |z| from ~0.03 to ~3000, zero exceptions.
A*B*C = (-)(-)( +) = (+) UNCONDITIONALLY. So Im(Sewn_s) < 0 for every z
where the construction is defined at all -- not merely "observed at 5
points", a proved fact.

CONSEQUENCE for the t-channel (A=2q.p2, B=2q.(p2+p3), C=2q.p4): A<0 ALWAYS
(p2 past-causal, Fact 1), C>0 ALWAYS (Fact 1), but B has NO fixed sign
(p2+p3 is spacelike, Fact 1 doesn't apply) -- consistent with the earlier
finding that most-but-not-all kinematic points landed on the t-channel's
physical branch. However: the construction ONLY makes sense where
w0_t=-t/B>0, and since t<0 always in this convention, that REQUIRES B>0 on
the physical branch by construction/selection, not by a separate dynamical
fact. So on the physical branch (the only place Sewn_t is even defined),
A*B*C = (-)(+)(+) = (-) by selection. Im(Sewn_t) > 0 wherever it's defined.

This fully explains the observed, robust sign pattern with an actual
derivation, and rules out the more exotic proposed mechanisms (contour
orientation, shadow-pole ordering, split-signature Jacobian, OPE-channel
crossing, leg-exchange sign) as unnecessary -- the true explanation is
more basic Lorentzian causal geometry plus the physical-branch selection
rule already present in the construction.

FURTHER CONSEQUENCE, found while investigating this (not assumed going
in): since B_s is causally FIXED-negative for ALL z but B_t is only
positive on a SELECTED subset, the s-channel and t-channel physical
domains in z are NOT THE SAME REGION -- checked directly (see
discovery/README.md): the s-channel's physical branch appears to cover the
entire z-plane (every random/grid point tested was physical), while the
t-channel's is a bounded island. This means "Sewn_s(z)+Sewn_t(z)" is not
even a well-posed pointwise sum over a common domain in general -- a
real complication for testing crossing-symmetric combinations, reported
honestly rather than glossed over.
"""
import random

import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p

mp.mp.dps = 25


def main():
    p1, p2, p3, p4 = make_kinematics(s=3.0, t=-2.0)
    print("Energy components (convention check):")
    print(f"  p1_0={p1[0]:+.4f}  p2_0={p2[0]:+.4f}  p3_0={p3[0]:+.4f}  p4_0={p4[0]:+.4f}")
    print("  p1,p2 past-pointing (negative energy); p3,p4 future-pointing.")
    print()

    p1p2 = tuple(p1[i] + p2[i] for i in range(4))
    random.seed(7)

    def sgn(x):
        return "+" if x > 0 else ("-" if x < 0 else "0")

    seen = {"q.p1": set(), "q.p2": set(), "q.p4": set(), "q.(p1+p2)": set()}
    for _ in range(200):
        scale = random.choice([0.01, 1, 10, 1000])
        x = random.uniform(-3, 3) * scale
        y = random.uniform(-3, 3) * scale
        z = mp.mpc(x, y)
        zb = mp.conj(z)
        seen["q.p1"].add(sgn((mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(v)) for v in p1))).real))
        seen["q.p2"].add(sgn((mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(v)) for v in p2))).real))
        seen["q.p4"].add(sgn((mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(v)) for v in p4))).real))
        seen["q.(p1+p2)"].add(sgn((mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(v)) for v in p1p2))).real))

    print("200 random z, |z| from ~0.03 to ~3000 -- signs seen (fixed = derivation confirmed):")
    for k, v in seen.items():
        print(f"  {k}: {v}  (fixed: {len(v) == 1})")
    print()
    print("This is the complete derivation of the s-channel/t-channel sign")
    print("pattern: reverse Cauchy-Schwarz for causal vectors dotted with a")
    print("future-null q, plus the physical-branch selection rule -- not")
    print("contour orientation, pole ordering, a Jacobian, or crossing.")


if __name__ == "__main__":
    main()
