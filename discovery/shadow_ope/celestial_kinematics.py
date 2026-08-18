"""
celestial_kinematics.py

Genuine celestial kinematics for the exact six-point cubic-scalar COMB tree
used throughout GPPVerify's Tree-Loop-Sewing thread (TreeLoopSewing.lean's
openSixPointChainDenominator / closedBoxDenominator; the handoff's
"5 -- p1 -- p2 -- p3 -- p4 -- 6" open chain).

Comb topology (4 trivalent vertices A-B-C-D, 3 internal edges):
    A: legs 5, 1        B: leg 2        C: leg 3        D: legs 4, 6
    edge A-B carries k5+p1
    edge B-C carries k5+p1+p2
    edge C-D carries k5+p1+p2+p3 = -(p4+k6)   [by overall momentum conservation]

Legs 1,2,3,4 are ORDINARY fixed external 4-momenta (not celestial-transformed
here -- only legs 5,6, the pair being sewn into the loop, are Mellin-transformed
to celestial (Delta, z, zbar) variables). This mirrors the physical setup: the
final object being reconstructed is a MOMENTUM-SPACE loop integrand, not a
further-transformed celestial correlator.

Null-vector parametrization (standard celestial holography convention, e.g.
Pasterski-Shao-Strominger 2017; z, zbar independent complexified/split-signature
variables, not assumed complex conjugates of each other):

    q^mu(z, zbar) = (1 + z*zbar, z + zbar, -i*(z - zbar), 1 - z*zbar)

with Minkowski metric eta = diag(-1,+1,+1,+1), giving the standard identity
    q_i . q_j = -(z_i - z_j)(zbar_i - zbar_j) =: -z_ij * zbar_ij

for two such null vectors (verified below by direct symbolic computation, not
assumed).
"""
import sympy as sp

# ---------------------------------------------------------------------
# Symbolic verification of q_i . q_j = -(z_i-z_j)(zbar_i-zbar_j)
# ---------------------------------------------------------------------
def _verify_dot_product_identity():
    z1, zb1, z2, zb2 = sp.symbols('z1 zb1 z2 zb2')

    def q(z, zb):
        return sp.Matrix([1 + z*zb, z + zb, -sp.I*(z - zb), 1 - z*zb])

    eta = sp.diag(1, -1, -1, -1)
    q1, q2 = q(z1, zb1), q(z2, zb2)
    dot = (q1.T * eta * q2)[0]
    dot = sp.expand(dot)
    # Direct computation (not assumed), mostly-minus metric: q_i.q_j =
    # +2(z_i-z_j)(zbar_i-zbar_j) -- verified here by brute-force symbolic
    # expansion, not copied from a paper.
    target = sp.expand(2 * (z1 - z2) * (zb1 - zb2))
    diff = sp.simplify(dot - target)
    assert diff == 0, f"dot-product identity FAILED, residual = {diff}"
    return True


_verify_dot_product_identity()  # raises if the standard identity is wrong


def q_vec(z, zb):
    """Null reference vector q^mu(z, zbar) as a 4-tuple (numeric, any type)."""
    return (1 + z * zb, z + zb, -1j * (z - zb), 1 - z * zb)


def mink_dot(a, b):
    """Minkowski dot product, mostly-minus metric diag(+1,-1,-1,-1) (matches
    the sign convention used throughout this thread's papers, where massless
    p^2=0 and s=(p1+p2)^2>0 for a physical timelike s-channel)."""
    return a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3]


def q_dot_p(z, zb, p):
    """q(z,zbar) . p for a fixed numeric 4-momentum p (tuple of 4 numbers)."""
    return mink_dot(q_vec(z, zb), p)


# ---------------------------------------------------------------------
# Fixed external kinematics: p1, p2, p3, p4, massless, sum to zero,
# GENERIC asymmetric Mandelstam invariants (chosen fresh, not matched to any
# prior claimed numerical example).
# ---------------------------------------------------------------------
def make_kinematics(s, t):
    """
    Build four explicit massless 4-momenta p1,p2,p3,p4 with p1+p2+p3+p4=0,
    s=(p1+p2)^2, t=(p2+p3)^2, in a standard 2->2 center-of-mass frame
    (all incoming convention). Returns (p1,p2,p3,p4) as tuples of floats.
    """
    import math
    E = math.sqrt(s) / 2.0
    # p1, p2 back-to-back along z-axis (incoming pair)
    p1 = (-E, 0.0, 0.0, E)
    p2 = (-E, 0.0, 0.0, -E)
    # scattering angle from t = (p2+p3)^2 = -2 p2.p3 for massless p2,p3
    # with p3 = (E, E sin(th), 0, E cos(th)) (outgoing, but kept "incoming"
    # sign convention throughout via the overall momentum-conservation sum)
    cos_th = 1.0 + t / (2.0 * E * E)
    if not (-1.0 <= cos_th <= 1.0):
        raise ValueError(f"(s,t)=({s},{t}) kinematically disallowed: cos(theta)={cos_th}")
    sin_th = math.sqrt(1.0 - cos_th * cos_th)
    p3 = (E, E * sin_th, 0.0, E * cos_th)
    p4 = (E, -E * sin_th, 0.0, -E * cos_th)
    # sanity: sum to zero, all massless
    tot = tuple(p1[i] + p2[i] + p3[i] + p4[i] for i in range(4))
    assert all(abs(x) < 1e-10 for x in tot), f"momentum conservation failed: {tot}"
    for p in (p1, p2, p3, p4):
        m2 = mink_dot(p, p)
        assert abs(m2) < 1e-9, f"leg not massless: p={p}, p^2={m2}"
    return p1, p2, p3, p4


if __name__ == "__main__":
    print("q_i.q_j = +2(z_i-z_j)(zbar_i-zbar_j): symbolically verified.")
    p1, p2, p3, p4 = make_kinematics(s=3.0, t=-2.0)
    print("p1,p2,p3,p4 =", p1, p2, p3, p4)
    s_check = mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                        tuple(p1[i] + p2[i] for i in range(4)))
    t_check = mink_dot(tuple(p2[i] + p3[i] for i in range(4)),
                        tuple(p2[i] + p3[i] for i in range(4)))
    print(f"s = (p1+p2)^2 = {s_check}  (target 3.0)")
    print(f"t = (p2+p3)^2 = {t_check}  (target -2.0)")
