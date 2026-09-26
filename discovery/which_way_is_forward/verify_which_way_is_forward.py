#!/usr/bin/env python3
"""Independent checks for the exact finite claims in Which Way Is Forward? (22 September 2026).

The script deliberately uses only the Python standard library. It verifies the
four-lift group, the explicit Cl(2,2) intertwiner, a coordinate normal-form
signature scan, determinant-cover winding, the Compton half-period identity,
the dimension/reality arithmetic used in the Spin(10,2) audit, the
realization of the orientation algebra in Cl(3,1), the charge-conjugation
signs B Bbar for Spin(6,2) and Spin(10,2), and Feynman's phase compensation.
"""

from __future__ import annotations

import cmath
import math
from collections import Counter, deque


TOL = 2.0e-12


def eye(n: int) -> list[list[complex]]:
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def zeros(m: int, n: int) -> list[list[complex]]:
    return [[0.0j for _ in range(n)] for _ in range(m)]


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))]
            for i in range(len(a))]


def scale(z: complex, a):
    return [[z * entry for entry in row] for row in a]


def mm(a, b):
    out = zeros(len(a), len(b[0]))
    for i in range(len(a)):
        for k in range(len(b)):
            for j in range(len(b[0])):
                out[i][j] += a[i][k] * b[k][j]
    return out


def dagger(a):
    return [[a[i][j].conjugate() for i in range(len(a))]
            for j in range(len(a[0]))]


def kron(a, b):
    out = zeros(len(a) * len(b), len(a[0]) * len(b[0]))
    for i in range(len(a)):
        for j in range(len(a[0])):
            for k in range(len(b)):
                for ell in range(len(b[0])):
                    out[i * len(b) + k][j * len(b[0]) + ell] = a[i][j] * b[k][ell]
    return out


def col(v):
    return [[z] for z in v]


def from_columns(columns):
    return [[columns[j][i] for j in range(len(columns))]
            for i in range(len(columns[0]))]


def flat(a):
    return [entry for row in a for entry in row]


def close(a, b, tol=TOL):
    return len(a) == len(b) and len(a[0]) == len(b[0]) and all(
        abs(x - y) < tol for x, y in zip(flat(a), flat(b))
    )


def assert_close(a, b, label):
    if not close(a, b):
        error = max(abs(x - y) for x, y in zip(flat(a), flat(b)))
        raise AssertionError(f"{label}: max error {error:.3e}")


def matrix_key(a):
    def q(z):
        return (round(z.real, 10), round(z.imag, 10))
    return tuple(q(z) for z in flat(a))


def diag(entries):
    out = zeros(len(entries), len(entries))
    for i, value in enumerate(entries):
        out[i][i] = value
    return out


def permutation_matrix(targets):
    """Column j is sent to basis vector targets[j]."""
    out = zeros(len(targets), len(targets))
    for source, target in enumerate(targets):
        out[target][source] = 1.0
    return out


def matrix_order(a, limit=32):
    power = eye(len(a))
    for n in range(1, limit + 1):
        power = mm(power, a)
        if close(power, eye(len(a))):
            return n
    raise AssertionError("matrix order exceeded search limit")


def verify_clifford_intertwiner():
    i2 = eye(2)
    x = [[0, 1], [1, 0]]
    z = [[1, 0], [0, -1]]
    j = [[0, 1], [-1, 0]]
    gamma = [kron(x, i2), kron(z, i2), kron(j, x), kron(j, z)]
    metric = [1, 1, -1, -1]

    for mu in range(4):
        for nu in range(4):
            anticommutator = add(mm(gamma[mu], gamma[nu]), mm(gamma[nu], gamma[mu]))
            target = scale(2.0 * metric[mu] if mu == nu else 0.0, eye(4))
            assert_close(anticommutator, target, f"Clifford relation {mu},{nu}")

    a = mm(gamma[0], gamma[1])
    b = mm(gamma[2], gamma[3])
    c = mm(gamma[1], gamma[3])
    rq = gamma[0]
    rt = mm(mm(gamma[0], gamma[1]), gamma[3])
    volume = mm(mm(mm(gamma[0], gamma[1]), gamma[2]), gamma[3])
    chi = scale(-1.0, mm(a, b))

    assert_close(mm(a, a), scale(-1, eye(4)), "a^2=-1")
    assert_close(mm(b, b), scale(-1, eye(4)), "b^2=-1")
    assert_close(mm(c, c), eye(4), "c^2=1")
    assert_close(mm(a, b), mm(b, a), "[a,b]=0")
    assert_close(add(mm(c, a), mm(a, c)), zeros(4, 4), "{c,a}=0")
    assert_close(add(mm(c, b), mm(b, c)), zeros(4, 4), "{c,b}=0")
    assert_close(rt, mm(rq, c), "r_t=r_q c")
    assert_close(chi, scale(-1, volume), "chi=-volume")

    columns = []
    for q, t in [(1, 1), (1, -1), (-1, 1), (-1, -1)]:
        uq = [1 / math.sqrt(2), -1j * q / math.sqrt(2)]
        wt = [1 / math.sqrt(2), 1j * t / math.sqrt(2)]
        alpha = 1.0 if q == 1 else -1j
        columns.append([alpha * entry for entry in flat(kron(col(uq), col(wt)))])
    s = from_columns(columns)
    assert_close(mm(dagger(s), s), eye(4), "eigenbasis is unitary")

    iq = diag([1j, 1j, -1j, -1j])
    it = diag([1j, -1j, 1j, -1j])
    d = permutation_matrix([3, 2, 1, 0])
    rq_label = permutation_matrix([2, 3, 0, 1])
    rt_label = permutation_matrix([1, 0, 3, 2])
    for operator, target, label in [
        (a, iq, "a=I_q"),
        (b, it, "b=I_t"),
        (c, d, "c=D"),
        (rq, rq_label, "r_q=R_q"),
        (rt, rt_label, "r_t=R_t"),
    ]:
        assert_close(mm(mm(dagger(s), operator), s), target, label)

    chi_label = scale(-1, mm(iq, it))
    assert_close(mm(mm(dagger(s), chi), s), chi_label, "chi intertwiner")
    if close(rt_label, scale(-1, eye(4))):
        raise AssertionError("temporal half flip was incorrectly identified with the scalar deck sign")
    assert_close(mm(mm(rt_label, chi_label), rt_label), scale(-1, chi_label),
                 "R_t reverses chi and is not central")

    fixed_basis = [
        [1, 0, 0, 1],
        [0, 1, 1, 0],
    ]
    for v in fixed_basis:
        vector = col(v)
        assert_close(mm(d, vector), vector, "D-fixed vector")
        assert_close(mm(rq_label, vector), mm(rt_label, vector), "half flips agree on Fix(D)")

    print("[ok] explicit Cl(2,2) carrier and unitary four-lift intertwiner")
    return iq, it, d, chi_label


def verify_carrier_group(iq, it, d, chi):
    generators = [iq, it, d]
    elements = {matrix_key(eye(4)): eye(4)}
    queue = deque([eye(4)])
    while queue:
        g = queue.popleft()
        for generator in generators:
            product = mm(g, generator)
            key = matrix_key(product)
            if key not in elements:
                elements[key] = product
                queue.append(product)

    if len(elements) != 16:
        raise AssertionError(f"carrier group has {len(elements)} elements, expected 16")
    orders = Counter(matrix_order(g) for g in elements.values())
    if orders != Counter({1: 1, 2: 11, 4: 4}):
        raise AssertionError(f"unexpected order distribution: {dict(orders)}")

    center = []
    values = list(elements.values())
    for g in values:
        if all(close(mm(g, h), mm(h, g)) for h in values):
            center.append(g)
    expected_center = [eye(4), scale(-1, eye(4)), chi, scale(-1, chi)]
    if {matrix_key(g) for g in center} != {matrix_key(g) for g in expected_center}:
        raise AssertionError("carrier center is not {+1,-1,+chi,-chi}")
    if any(close(d, z) for z in center):
        raise AssertionError("D was incorrectly found in the center")

    print("[ok] |G_qt|=16, orders {1:1, 2:11, 4:4}, center={+1,-1,+chi,-chi}")


def blade_multiply(mask_a: int, mask_b: int, metric: list[int]):
    sign = 1
    mask = mask_a
    for i in range(len(metric)):
        if not (mask_b & (1 << i)):
            continue
        greater = sum(1 for j in range(i + 1, len(metric)) if mask & (1 << j))
        if greater % 2:
            sign *= -1
        if mask & (1 << i):
            sign *= metric[i]
            mask ^= 1 << i
        else:
            mask |= 1 << i
    return sign, mask


def verify_coordinate_signature_scan():
    bivectors = [(1 << i) | (1 << j) for i in range(4) for j in range(i + 1, 4)]
    solution_counts = {}
    for p in range(5):
        metric = [1] * p + [-1] * (4 - p)

        def product(x, y):
            return blade_multiply(x, y, metric)

        def square(x):
            return product(x, x) == (-1, 0)

        solutions = []
        for a in bivectors:
            for b in bivectors:
                if a == b or not square(a) or not square(b):
                    continue
                if product(a, b) != product(b, a):
                    continue
                for c in bivectors:
                    if product(c, c) != (1, 0):
                        continue
                    ca = product(c, a)
                    ac = product(a, c)
                    cb = product(c, b)
                    bc = product(b, c)
                    if ca[1] == ac[1] and ca[0] == -ac[0] and cb[1] == bc[1] and cb[0] == -bc[0]:
                        solutions.append((a, b, c))
        solution_counts[(p, 4 - p)] = len(solutions)

    nonempty = [signature for signature, count in solution_counts.items() if count]
    if nonempty != [(2, 2)]:
        raise AssertionError(f"coordinate normal-form scan found signatures {nonempty}")
    print(f"[ok] coordinate simple-bivector normal forms occur only in signature (2,2): {solution_counts}")


def det2(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def transpose(a):
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def winding(samples):
    total = 0.0
    for z0, z1 in zip(samples, samples[1:]):
        total += cmath.phase(z1 / z0)
    return total / (2 * math.pi)


def verify_determinant_cover():
    a = [[2 + 1j, 1 - 2j], [3 + 0.5j, -1 + 1j]]
    left = [[1 + 1j, 1], [1j, 1]]
    right = [[1, 2j], [0, 1]]
    if abs(det2(left) - 1) > TOL or abs(det2(right) - 1) > TOL:
        raise AssertionError("test matrices are not in SL(2,C)")
    transformed = mm(mm(left, a), transpose(right))
    if abs(det2(transformed) - det2(a)) > TOL:
        raise AssertionError("determinant is not invariant under L A R^T")

    n = 4096
    rho = 0.25
    determinant_loop = [rho * cmath.exp(2j * math.pi * k / n) for k in range(n + 1)]
    w = winding(determinant_loop)
    if abs(w - 1.0) > 1.0e-10:
        raise AssertionError(f"light-cone meridian winding is {w}")
    root_start = cmath.sqrt(determinant_loop[0])
    lifted_end = root_start * cmath.exp(1j * math.pi * w)
    if abs(lifted_end + root_start) > TOL:
        raise AssertionError("unit winding did not reverse the square-root lift")

    print("[ok] det(L A R^T)=det(A); explicit light-cone meridian has winding 1 and deck sign -1")


def verify_compton_and_spin102_arithmetic():
    h = 6.62607015e-34
    hbar = h / (2 * math.pi)
    electron_mass = 9.1093837139e-31
    light_speed = 299792458.0
    half_compton_time = h / (2 * electron_mass * light_speed**2)
    zitter_period = 2 * math.pi / (2 * electron_mass * light_speed**2 / hbar)
    if abs(half_compton_time / zitter_period - 1.0) > 2.0e-15:
        raise AssertionError("Compton half-period and zitter period differ")

    reality_restoring = [n for n in range(13) if (4 + n) % 8 == 0]
    if reality_restoring != [4, 12]:
        raise AssertionError(f"unexpected Majorana-Weyl extension ranks: {reality_restoring}")
    if not ((1 - 1) % 8 == 0 and (9 - 1) % 8 == 0):
        raise AssertionError("(1,1)+(9,1) factorwise Majorana-Weyl check failed")
    if not ((2 - 2) % 8 == 0 and (8 - 0) % 8 == 0):
        raise AssertionError("(2,2)+(8,0) factorwise Majorana-Weyl check failed")

    dim_parent = 12 * 11 // 2
    dim_blocks = (8 * 7 // 2) + (4 * 3 // 2) + 8 * 4
    compact_mixed = 6 * 2 * 2 + 1 * 2 * 2 + 1 * 2 * 2
    if dim_parent != 66 or dim_blocks != 66 or compact_mixed != 32:
        raise AssertionError("Spin(10,2) dimension branching failed")

    print(f"[ok] h/(2mc^2)=zitter period={half_compton_time:.12e} s")
    print("[ok] MW extension ranks n=4,12; 66=28+6+32 and 32=24+4+4")


def verify_minkowski_realization():
    """Thm Dsignaturegeneral: the same a,b,c live in Cl(3,1), as one bivector and two trivectors."""
    i2 = eye(2)
    x = [[0, 1], [1, 0]]; z = [[1, 0], [0, -1]]; j = [[0, 1], [-1, 0]]
    g22 = [kron(x, i2), kron(z, i2), kron(j, x), kron(j, z)]
    a = mm(g22[0], g22[1]); b = mm(g22[2], g22[3]); c = mm(g22[1], g22[3])
    g31 = [kron(x, i2), kron(z, i2), kron(j, j), kron(j, x)]
    metric = [1, 1, 1, -1]
    for mu in range(4):
        for nu in range(4):
            anti = add(mm(g31[mu], g31[nu]), mm(g31[nu], g31[mu]))
            target = scale(2.0 * metric[mu] if mu == nu else 0.0, eye(4))
            assert_close(anti, target, f"Cl(3,1) relation {mu},{nu}")
    assert_close(a, mm(g31[0], g31[1]), "a = G1 G2 in Cl(3,1)")
    assert_close(b, mm(mm(g31[0], g31[1]), g31[2]), "b = G1 G2 G3 in Cl(3,1)")
    assert_close(c, scale(-1, mm(mm(g31[0], g31[2]), g31[3])), "c = -G1 G3 G4 in Cl(3,1)")
    assert_close(mm(a, a), scale(-1, eye(4)), "a^2=-1")
    assert_close(mm(b, b), scale(-1, eye(4)), "b^2=-1")
    assert_close(mm(a, b), mm(b, a), "[a,b]=0")
    assert_close(mm(c, c), eye(4), "c^2=1")
    assert_close(add(mm(c, a), mm(a, c)), zeros(4, 4), "{c,a}=0")
    assert_close(add(mm(c, b), mm(b, c)), zeros(4, 4), "{c,b}=0")
    print("[ok] Cl(3,1) realizes the orientation algebra: a bivector, b and c trivectors")


def _pauli_gammas(p, q):
    s0 = eye(2); sx = [[0, 1], [1, 0]]; sy = [[0, -1j], [1j, 0]]; sz = [[1, 0], [0, -1]]
    k = (p + q) // 2
    gens = []
    for n in range(k):
        for sig in (sx, sy):
            factors = [sz] * n + [sig] + [s0] * (k - n - 1)
            m = factors[0]
            for f in factors[1:]:
                m = kron(m, f)
            gens.append(m)
    return [g if idx < p else scale(1j, g) for idx, g in enumerate(gens)]


def _conj(a):
    return [[entry.conjugate() for entry in row] for row in a]


def verify_parent_quaternionic():
    """Thm parentquaternionic: B Bbar = -1 for (6,2), +1 for (10,2), both charge conjugations."""
    results = {}
    for p, q in [(6, 2), (10, 2)]:
        gens = _pauli_gammas(p, q)
        d = len(gens[0])
        for idx, g in enumerate(gens):
            assert_close(mm(g, g), scale(1 if idx < p else -1, eye(d)), f"Cl({p},{q}) square {idx}")
        real = [g for g in gens if close(g, _conj(g))]
        imag = [g for g in gens if close(g, scale(-1, _conj(g)))]
        assert len(real) + len(imag) == len(gens)
        signs = []
        for family in (real, imag):
            b = eye(d)
            for g in family:
                b = mm(b, g)
            eps = None
            for g in gens:
                lhs = mm(b, _conj(g))
                if close(lhs, mm(g, b)):
                    e = 1
                elif close(lhs, scale(-1, mm(g, b))):
                    e = -1
                else:
                    raise AssertionError("B does not intertwine gamma^* with +-gamma")
                eps = e if eps is None else eps
                assert e == eps
            bb = mm(b, _conj(b))
            s = bb[0][0]
            assert_close(bb, scale(s, eye(d)), "B Bbar scalar")
            signs.append(int(round(s.real)))
        results[(p, q)] = signs
    if results != {(6, 2): [-1, -1], (10, 2): [1, 1]}:
        raise AssertionError(f"unexpected B Bbar signs {results}")
    print(f"[ok] B Bbar signs {results}: Spin(6,2) quaternionic, Spin(10,2) real")


def verify_feynman_phase():
    """Eq feynmanphasemonotone: with sgn E = t, E (t2-t1) = |E||t2-t1| and D_t Phi = |E|."""
    for t in (1, -1):
        for e_abs in (0.3, 1.7):
            for d_abs in (0.5, 2.25):
                e = t * e_abs; dt = t * d_abs
                if abs(e * dt - e_abs * d_abs) > TOL or abs(t * e - e_abs) > TOL:
                    raise AssertionError("phase compensation failed")
    print("[ok] sgn E = t gives E(t2-t1) = |E||t2-t1| and D_t Phi = |E| >= 0")


def main():
    iq, it, d, chi = verify_clifford_intertwiner()
    verify_carrier_group(iq, it, d, chi)
    verify_coordinate_signature_scan()
    verify_determinant_cover()
    verify_compton_and_spin102_arithmetic()
    verify_minkowski_realization()
    verify_parent_quaternionic()
    verify_feynman_phase()
    print("All exact-core checks passed.")


if __name__ == "__main__":
    main()
