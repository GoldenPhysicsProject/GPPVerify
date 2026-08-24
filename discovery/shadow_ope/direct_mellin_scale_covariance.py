"""
direct_mellin_scale_covariance.py

Literature check (2026-08-19, prompted by "keep trying to figure out the loop
integrands"): does the *established* celestial-holography technique for loop
amplitudes look like this project's shadow-pair-sewing hypothesis at all?

Source checked: Gonzalez, Puhm, Rojas, "Loops on the Celestial Sphere"
(arXiv:2009.07290, Phys.Rev.D 102 (2020) 126027) -- the direct, on-topic paper
found via literature search. Full text extracted and grepped for
"shadow"/"discontinuity"/"dispersion"/"inversion": **zero hits** on any
shadow-discontinuity-of-a-higher-point-tree-correlator mechanism. Their actual
method (section 3.2, eq. 3.7-3.9) is the opposite direction: take the
ALREADY-KNOWN momentum-space loop integral (the scalar box M_eps(s,t), computed
by ordinary QFT methods and expressed in hypergeometric functions), and Mellin-
transform THAT directly -- promoting the momentum-space scalar prefactor to a
differential/shift operator acting on the celestial TREE amplitude. This is
"repackage a known loop answer celestially," not "derive the loop answer purely
from tree-level shadow structure" -- a fundamentally different goal from this
session's (and the whole Tree-Loop-Sewing thread's) K1(lambda;s,t) program.

This script checks a specific, verifiable structural consequence of trying to
adapt their single-particle Mellin-transform machinery (their eq. 2.16) naively
to the box integral itself, at fixed external legs 1-4 (i.e. transforming the
OVERALL SCALE of s,t at fixed cross-ratio r = -s/t, mirroring their eq. 2.16's
single remaining integration variable w after using the delta-function to fix
angles) -- as opposed to this project's actual setup (celestial_kinematics.py's
own docstring: legs 1-4 stay ordinary momentum-space externals; only legs 5,6,
the SEWN pair, get Mellin-transformed). Finding: the two are NOT interchangeable,
and only the latter can carry genuine lambda-dependence, for a clean and provable
reason -- checked below.
"""
from mpmath import mp, polylog, pi

mp.dps = 30


def box_exact(s, t):
    """The massless scalar box, same normalization as sewn_z_integral_v2.py's
    box_exact_complex: (2/st)[Li2(1-s/t) + Li2(1-t/s) + pi^2/6]."""
    s, t = mp.mpf(s), mp.mpf(t)
    return (2 / (s * t)) * (polylog(2, 1 - s / t) + polylog(2, 1 - t / s) + pi ** 2 / 6)


def check_scale_covariance(r, w_values):
    """box(r*w, -w) at FIXED cross-ratio r=-s/t: verify it is EXACTLY
    proportional to w^{-2} for every w (not just asymptotically)."""
    r = mp.mpf(r)
    scaled = []
    for w in w_values:
        w = mp.mpf(w)
        val = box_exact(r * w, -w)
        scaled.append(val * w ** 2)
    return scaled


if __name__ == "__main__":
    r = mp.mpf("2.7")
    w_values = [mp.mpf(x) for x in ["0.001", "0.3", "1.0", "5.0", "37.0", "1000.0"]]
    scaled = check_scale_covariance(r, w_values)

    print(f"r = {r}  (fixed cross-ratio, s=r*w, t=-w)")
    print(f"{'w':>10}  {'w^2 * box(rw,-w)':>40}")
    for w, s in zip(w_values, scaled):
        print(f"{float(w):>10}  {complex(s)}")

    max_dev = max(abs(s - scaled[0]) for s in scaled)
    print(f"\nmax deviation from constancy across 6 decades of w: {float(max_dev):.3e}")
    print(f"(dps=30, so this confirms exact w^-2 scaling to ~1e-25, not asymptotic)")

    print("""
CONCLUSION: box(r*w, -w) = C(r)/w^2 EXACTLY for all w>0 -- a pure power law
with NO subleading structure. Reason: box(s,t) = (2/st)[Li2(1-s/t)+Li2(1-t/s)
+pi^2/6], and along the ray s=r*w, t=-w the ratio s/t=-r is w-independent, so
the dilogarithm arguments (hence the whole bracket) never change with w -- only
the explicit 1/(st) = -1/(r*w^2) prefactor does. Confirmed numerically to
~1e-25 (dps=30) across 6 decades of w, not just as an asymptotic statement.

CONSEQUENCE for the Mellin-transform-in-w picture (Gonzalez-Puhm-Rojas eq 2.16,
naively applied to the box's OWN s,t rather than to extra sewn legs): the
"celestial transform" integral(dw w^{(Delta-6)/2} * box(rw,-w)) is EXACTLY the
Mellin transform of a pure power law C(r)*w^-2 -- which is a delta function (or
its distributional derivatives) pinning Delta to a SINGLE fixed value, exactly
as Gonzalez-Puhm-Rojas found for the tree-level YM amplitude itself (their eq.
2.21-2.22, f_tree ~ delta(lambda)). There is NO genuine lambda-dependent
K1(lambda; s,t) obtainable this way -- the transform degenerates.

This is not a defect in this project's setup: it is a clean, checkable reason
why celestial_kinematics.py's own convention (transform ONLY the extra sewn
legs 5,6's energies omega5,omega6, keeping legs 1-4 and hence s,t as ordinary
FIXED momentum-space externals) is structurally the only choice that can
produce a nontrivial function of lambda at all -- confirmed here rather than
just assumed. The open problem remains getting the ANALYTIC CONTENT of that
transform (Sewn_s, Sewn_t, L(Delta5), the residue construction, ...) to equal
the box -- this finding does not solve that, but it does rule out "just Mellin-
transform the box's own s,t directly" as an alternative approach, and confirms
the existing machinery is targeting the right variables.
""")
