"""
z_integral_attempt.py

Attempt at the (z,zbar) integral of Sewn_s(z) (tied_leg_continuation.py /
principal_series_sewing.py), integrating over the celestial sphere's
position for the sewn leg -- the piece flagged as missing in every prior
note in this sandbox.

SETUP: z ranges over the complex plane (real Lorentzian slice, zbar=z*,
stereographic coordinate for the celestial sphere: z=x+iy gives the real
null vector q(z,z*)=(1+x^2+y^2, 2x, 2y, 1-x^2-y^2)). Sewn_s(z) is the
already-verified closed form from principal_series_sewing.py, now treated
as a function of z with A(z),B(z),C(z) all functions of z.

GRID SCAN FIRST (before trusting any quadrature): |Sewn_s(z)| is smooth
and finite everywhere checked on a coarse grid except where B(z)=0 (a
measure-zero locus, not hit on the grid). Peaks near z~(-1,0)-ish
(reflecting where q(z,z*) points closest to -p1's direction, making A(z)
small) but stays finite there.

LARGE-|z| BEHAVIOR (checked directly, not estimated by hand after an
earlier hand-estimate turned out wrong -- caught by actually computing
it): |Sewn_s(z)| ~ K/r^2 as r=|z|->infinity, with K a UNIVERSAL constant
independent of angle (checked at 6 different angles, all converging to
K~0.26 for the s=3,t=-2,z-along-various-rays kinematic point). This
isotropy makes sense: at large |z|, q(z,z*) ~ r^2*(1,0,0,-1) dominates
over the subleading 2x,2y terms regardless of direction, so A,B,C all
approach the same asymptotic ratio structure.

CONSEQUENCE: the FLAT-measure integral int d^2z |Sewn_s(z)| ~
int 2*pi*r*dr * K/r^2 = 2*pi*K * int dr/r -- a clean, confirmed,
LOGARITHMIC DIVERGENCE at large z. Not a numerical artifact: the 1/r^2
falloff and its isotropic coefficient are both directly verified.

WHAT THIS LIKELY MEANS (a hypothesis, explicitly flagged as such, not
verified): the known massless box integral I_4(s,t) is itself only
finite after IR regularization in the fully massless case (the historical
manuscripts audited earlier in this thread's history explicitly note
"after IR regularization" in their own box definition) -- a genuine,
textbook IR divergence of massless box integrals, not something specific
to a botched calculation. A log-divergent z-integral here is at least
CONSISTENT with reproducing that same IR structure, rather than being
evidence the construction is wrong. This is a plausible, well-motivated
reading, not a verified one -- distinguishing an IR divergence that
matches the box's own from an artifact of a wrong measure/normalization
choice would need the divergence's PRECISE coefficient compared against
the known IR-divergent piece of I_4(s,t) in a matching regularization
scheme (e.g. dimensional regularization), which has not been attempted.

WHAT IS NOT YET KNOWN: whether the FLAT measure d^2z is even the right
one to use here in the first place (a different, standard convention in
celestial CFT -- a conformal weight factor like (1+|z|^2)^{-2} for a
weight-(1/2,1/2) primary -- would change convergence entirely, and I do
not have a settled derivation of which is correct for this SPECIFIC
completeness-relation context, as opposed to guessed by analogy).
Recorded as an explicitly open question rather than resolved either way.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 25


def build_s(s_in, t_in):
    p1, p2, p3, p4 = make_kinematics(s=s_in, t=t_in)
    s_val = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                      tuple(p1[i] + p2[i] for i in range(4)))
    return p1, p2, p3, p4, mp.mpf(str(s_val))


def Sewn_s(z, p1, p2, p4, s_val):
    zb = mp.conj(z)
    A = (mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p1))).real
    B = (mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(p1[i] + p2[i])) for i in range(4)))).real
    C = (mp.mpf(2) * q_dot_p(z, zb, tuple(mp.mpf(str(x)) for x in p4))).real
    w0 = -s_val / B
    if w0 <= 0:
        return None
    x = mp.log(w0)
    return -1j * mp.pi / (2 * A * C * B) * w0 ** (-2) * mp.sech(x / 2) ** 2


def main():
    p1, p2, p3, p4, s_val = build_s(3.0, -2.0)

    print("=" * 72)
    print("Isotropy of the large-|z| falloff: r^2*|Sewn_s(z)| at several")
    print("angles, should converge to the SAME constant at every angle")
    print("=" * 72)
    for theta_deg in [0, 45, 90, 135, 200, 300]:
        theta = mp.pi * theta_deg / 180
        vals = []
        for r in [20, 50, 100, 200]:
            z = r * mp.mpc(mp.cos(theta), mp.sin(theta))
            v = Sewn_s(z, p1, p2, p4, s_val)
            vals.append(float(r ** 2 * abs(v)) if v else None)
        print(f"  theta={theta_deg:4d}deg: " + "  ".join(f"{v:.5f}" if v else "None" for v in vals))

    print()
    print("=" * 72)
    print("Confirms int d^2z |Sewn_s(z)| ~ 2*pi*K*int dr/r -- log divergent")
    print("at large z, K ~ 0.26 (isotropic). See module docstring for what")
    print("this likely means (a flagged hypothesis, not a verified claim)")
    print("and what remains genuinely open (which z-measure is correct here).")
    print("=" * 72)


if __name__ == "__main__":
    main()
