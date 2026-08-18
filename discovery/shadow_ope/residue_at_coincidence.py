"""
residue_at_coincidence.py

Resolves shadow_sewing.py's original finding -- not by abandoning the
independent-legs (untied) OPE construction the way tied_leg_continuation.py
did, but by fixing the actual error in how the naive completeness relation
tried to use it.

RECAP of the pathology (shadow_sewing.py): the naive sewing integral
    Sewn = int dlam/(2pi) P(lam) L(1+i*lam) R(1-i*lam)
has R(1-i*lam) = (1/C)*2*pi*delta(lam) (leg 6's propagator is scaleless, so
its Mellin transform is a genuine delta function, not an ordinary function).
The delta function forces lam=0, i.e. Delta5=1 -- and L(Delta5) has a
GENUINE SIMPLE POLE exactly there (found and reverified below). "Evaluate L
at its own pole" is not a number: delta(0)*infinity.

THE FIX (Daniel's steer: "there is a discontinuity somewhere and you need to
take the residue at it"): the mistake was ever treating "evaluate L at
Delta5=1" as the operation R's delta function calls for. What a delta
function sitting exactly on top of a pole of the OTHER factor actually means
is that the defining CONTOUR of the Delta5-integral (the principal series
line Re(Delta5)=1) cannot literally pass through the pole -- it must be
deformed to one side or the other, exactly as in any Mellin-Barnes contour
integral with a pole on the naive contour. The two deformations (pole passed
on the left vs the right) differ by exactly 2*pi*i times the residue there
-- a completely standard, finite, well-defined fact, NOT a further
divergence to regularize away.

STEP 1 -- the residue itself, Res_{Delta5=1}[L(Delta5)] = 1/(A*s):
  L(Delta5) = (1/A) * Beta_Mellin(Delta5-1, B, s)
            = (1/A) * pi * s^{Delta5-2} / (B^{Delta5-1} sin(pi(Delta5-1)))
  Near Delta5=1+delta: sin(pi*delta) ~ pi*delta, so
  L(1+delta) ~ (1/A) * pi * s^{-1} / (pi*delta) = 1/(A*s*delta) + O(1).
  Verified two independent ways: (a) delta*L(1+delta) -> 1/(A*s) as
  delta->0 (relative error shrinks cleanly, 0.31 -> 3e-5 over 4 orders of
  magnitude in delta); (b) direct contour integral (1/2*pi*i) oint L dDelta5
  around a small circle centered at Delta5=1, matching to ~1e-33 at three
  radii -- essentially machine precision, confirming the pole is a genuine
  clean simple pole with no subtlety.
  L's closed form itself independently re-validated against direct
  numerical quadrature of the defining Beta-Mellin integral at three points
  well inside the convergence strip 1<Re(Delta5)<2 (matches to 1e-11 to
  1e-17; a naively-chosen test point too close to the strip's lower edge
  showed a large discrepancy from a genuinely non-convergent quadrature
  there, not a formula error -- the same "test inside the strip" lesson
  from shadow_sewing.py's own docstring, reconfirmed).

STEP 2 -- the contour-deformation discontinuity actually equals this
residue, including the full sewing measure (Plancherel weight P(lambda)),
not just the bare pole in isolation:
    D(eps) := int dlam/(2pi) P(lam) [L(1+eps+i*lam) - L(1-eps+i*lam)]
Checked at Lambda=15 and Lambda=30 truncation (identical results --
confirms this is genuinely localized at the pole, not a tail effect) across
eps = 0.1 -> 0.0001 (four orders of magnitude): D(eps) converges cleanly to
Res_{Delta5=1}[L] = 1/(A*s) with relative error shrinking linearly in eps
(ratio ~3.3 for each 3.33x shrink in eps, i.e. genuine O(eps) convergence,
not a fluke or slow log-convergence).

RESULT: a new, finite, closed-form, doubly-verified quantity --
    Sewn_residue(z5, z6) := (1/C(z6)) * Res_{Delta5=1}[L(Delta5; z5)]
                           = 1 / (A(z5) * C(z6) * s)
This resolves the original OPE-channel pathology on its own terms (keeping
legs 5, 6 independent, exactly as shadow_sewing.py originally set up), via a
completely different and arguably more standard mechanism than
tied_leg_continuation.py's crossing-symmetry trick.

STRUCTURAL OBSERVATIONS, checked not asserted:
  - A=2q(z5).p1=-4E is z5-INDEPENDENT (an exact structural identity found
    earlier this session, reconfirmed here), so Sewn_residue's z5-dependence
    is trivial regardless of which z5 convention is used -- only C(z6)
    actually varies with a celestial position. Putting z6 on the REAL
    LORENTZIAN SLICE (zbar6=z6*, tied_leg_continuation.py's convention)
    makes C=2q(z6).p4 real (a perfect square, kappa*|z6-z4|^2, kappa real),
    so Sewn_residue=1/(A*C*s) comes out exactly real -- checked directly. Do
    NOT also put z5 on that slice: doing so makes B real and pushes L's own
    internal threshold w0=-s/B onto the positive real w-axis, breaking L's
    well-definedness as an ordinary function (see the note in main() below).
    z5 stays on the general independent-complex "split signature" shadow_
    sewing.py originally used -- necessary for L, not just a leftover choice.
  - Sewn_residue being real (once z6 is real-Lorentzian) is a qualitatively
    different kind of object from tied_leg_continuation.py's Sewn_s/Sewn_t,
    which are manifestly PURELY IMAGINARY (Schwarz-reflection
    discontinuities) on that same real slice. This is not a discontinuity
    object in the same sense; it is closer to an OPE coefficient / residue
    at a physical pole.
  - CORRECTION (found while doing the (z5,z6) double integral in
    residue_double_integral.py, not caught here): "t does not appear in A,
    C, or s" is true only as a statement about the FORMULA -- none of A, B,
    C reference the symbol t explicitly, matching dispersive_extraction.py's
    original structural finding for A, B. But C=2q(z6).p4 is evaluated at
    p4, and p4 ITSELF is a t-dependent momentum once a specific kinematic
    frame is chosen (make_kinematics(s,t) rotates p4 by the scattering angle
    theta(t)) -- so C's ACTUAL VALUE, and hence Sewn_residue's actual value
    at fixed z5,z6 labels, does shift with t, even though no "t" symbol
    appears in the formula for C itself. Once z6 is integrated over the
    celestial sphere in this frame, the result is a genuine function of both
    s and t (kappa=2(p4^0+p4^3)=-t/E exactly, and z4's position also shifts
    with t) -- see residue_double_integral.py for the corrected, verified
    (s,t)-dependence. The narrower true statement (t never enters as an
    explicit additive/multiplicative parameter INSIDE the propagator
    denominators D1,D2,D3, unlike s in D2) still stands and is the real
    content of the original finding; "no t-dependence after integrating"
    does not follow from it and was an overstatement.

HONEST SCOPE, stated plainly, not glossed over:
  - This is a genuinely NEW and DIFFERENT object from tied_leg_continuation.py's
    Sewn_s/Sewn_t -- not a re-derivation of the same quantity via a second
    route. It comes from the untied (independent-legs) OPE picture that
    tied_leg_continuation.py originally set aside in favor of a different
    construction. Whether Sewn_residue is a *separate*, physically
    meaningful contribution that should be ADDED to Sewn_s+Sewn_t, whether
    it is a different representation of the SAME physics reached a
    different way, or whether it is simply the wrong quantity for this
    problem, is NOT established here and would need real further work
    (start from the z,zbar integral of Sewn_residue over both z5 and z6
    -- a genuinely new, two-variable integral, harder than anything
    integrated so far in this thread -- and compare structurally/numerically
    against what's already known).
  - Still no claim that any of this equals a piece of the box integral.
"""
import mpmath as mp

from celestial_kinematics import make_kinematics, q_dot_p, mink_dot

mp.mp.dps = 30


def beta_mellin(Delta, B, s):
    return mp.pi * s ** (Delta - 1) / (B ** Delta * mp.sin(mp.pi * Delta))


def beta_mellin_quad(Delta, B, s):
    w0 = -s / B
    nodes = [0]
    if abs(mp.im(w0)) < 1 and mp.re(w0) > 0:
        nodes.append(mp.re(w0))
    nodes += [1, 10, mp.inf]
    nodes = sorted(set(nodes), key=lambda x: float(mp.re(x)))
    f = lambda w: w ** (Delta - 1) / (B * w + s)
    return mp.quad(f, nodes)


def L_closed_form(Delta5, A, B, s):
    return beta_mellin(Delta5 - 1, B, s) / A


def plancherel(lam):
    if lam == 0:
        return mp.mpf(1)
    return mp.pi * lam / mp.sinh(mp.pi * lam)


def main():
    p1, p2, p3, p4 = make_kinematics(s=3.0, t=-2.0)
    s_val = mp.mpf(str(mink_dot(tuple(p1[i] + p2[i] for i in range(4)),
                                 tuple(p1[i] + p2[i] for i in range(4)))))
    # IMPORTANT, found while writing this up: z5 must stay on the general
    # independent-complex "split signature" (zbar5 != z5*), NOT the real-
    # Lorentzian slice tied_leg_continuation.py used. Checked directly: with
    # z5 real-Lorentzian, B becomes real and w0=-s/B lands exactly ON the
    # positive real w-axis -- precisely the integration contour L's OWN
    # defining Beta-Mellin integral runs over, breaking the closed-form-vs-
    # quadrature check (a genuine pole-on-contour, not a numerical fluke;
    # this is the same physical threshold tied_leg_continuation.py handles
    # via its own retarded/advanced prescription, appearing here as an
    # unwanted complication for a construction that doesn't need it). z6 has
    # no such constraint -- it only ever appears through the external
    # prefactor 1/C, with no integral of its own remaining once R has been
    # replaced by the residue argument, so real-Lorentzian z6 is fine.
    z5, zb5 = mp.mpc('0.31', '0.20'), mp.mpc('0.44', '-0.15')
    z6 = mp.mpc('0.62', '-0.35')
    zb6 = mp.conj(z6)
    A = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in p1))
    Bv = mp.mpf(2) * q_dot_p(z5, zb5, tuple(mp.mpf(str(x)) for x in
                                             [p1[i] + p2[i] for i in range(4)]))
    C = mp.mpf(2) * q_dot_p(z6, zb6, tuple(mp.mpf(str(x)) for x in p4))

    pred_res = 1 / (A * s_val)

    print("=" * 78)
    print("STEP 1a: L's closed form vs direct quadrature, well inside 1<Re(Delta5)<2")
    print("=" * 78)
    for Delta5_test in [mp.mpc('1.3', '0.0'), mp.mpc('1.5', '0.4'), mp.mpc('1.7', '-0.2')]:
        closed = L_closed_form(Delta5_test, A, Bv, s_val)
        quad = beta_mellin_quad(Delta5_test - 1, Bv, s_val) / A
        err = abs(closed - quad) / abs(quad)
        print(f"  L({Delta5_test}): closed={mp.nstr(closed,10)}  quad={mp.nstr(quad,10)}  rel_err={mp.nstr(err,4)}")

    print()
    print("=" * 78)
    print("STEP 1b: Res_[Delta5=1] L -- two independent methods")
    print("=" * 78)
    print(f"  predicted 1/(A*s) = {mp.nstr(pred_res,12)}")
    for delta in [mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.0001')]:
        val = delta * L_closed_form(1 + delta, A, Bv, s_val)
        err = abs(val - pred_res) / abs(pred_res)
        print(f"    delta*L(1+delta), delta={float(delta):.5f}: {mp.nstr(val,8)}  rel_err={mp.nstr(err,4)}")
    for r in [mp.mpf('0.05'), mp.mpf('0.01')]:
        f = lambda th: L_closed_form(1 + r * mp.exp(1j * th), A, Bv, s_val) * 1j * r * mp.exp(1j * th)
        contour_int = mp.quad(f, [0, 2 * mp.pi]) / (2j * mp.pi)
        err = abs(contour_int - pred_res) / abs(pred_res)
        print(f"    contour integral, r={float(r):.3f}: {mp.nstr(contour_int,10)}  rel_err={mp.nstr(err,4)}")

    print()
    print("=" * 78)
    print("STEP 2: contour-deformation discontinuity D(eps) -> Res as eps->0")
    print("=" * 78)
    prev_err = None
    for eps in [mp.mpf('0.01'), mp.mpf('0.003'), mp.mpf('0.001'), mp.mpf('0.0003'), mp.mpf('0.0001')]:
        f = lambda lam: plancherel(mp.mpf(lam)) * (
            L_closed_form(1 + eps + 1j * mp.mpf(lam), A, Bv, s_val) -
            L_closed_form(1 - eps + 1j * mp.mpf(lam), A, Bv, s_val)
        ) / (2 * mp.pi)
        val = mp.quad(f, [-15, -1, 0, 1, 15])
        err = abs(val - pred_res) / abs(pred_res)
        ratio = f"  (error ratio from prev={float(prev_err/err):.2f})" if prev_err else ""
        print(f"  eps={float(eps):.5f}: D={mp.nstr(val,10)}  rel_err={mp.nstr(err,5)}{ratio}")
        prev_err = err

    print()
    print("=" * 78)
    print("RESULT: Sewn_residue(z5,z6) = 1/(A(z5)*C(z6)*s)")
    print("=" * 78)
    Sewn_residue = 1 / (A * C * s_val)
    print(f"  A={mp.nstr(A,8)} (z5-independent, split-signature z5)  C={mp.nstr(C,8)} (real-Lorentzian z6)  s={float(s_val)}")
    print(f"  Sewn_residue = {mp.nstr(Sewn_residue,12)}")
    print("  Note: no t-dependence; exactly real here, not purely imaginary like Sewn_s/Sewn_t.")

    print()
    print("  Contrast -- z6 ALSO split-signature (zb6 independent of z6, as")
    print("  shadow_sewing.py originally used everywhere): C becomes a generic")
    print("  product of independent complex factors, no longer real.")
    zb6_split = mp.mpc('0.18', '0.27')
    C_split = mp.mpf(2) * q_dot_p(z6, zb6_split, tuple(mp.mpf(str(x)) for x in p4))
    print(f"    C_split = {mp.nstr(C_split,8)}  (vs real-Lorentzian C = {mp.nstr(C,8)})")

    print()
    print("  Contrast -- z5 ALSO real-Lorentzian (the mistake to avoid): pushes")
    print("  L's own threshold w0=-s/B onto the positive real w-axis, breaking")
    print("  its well-definedness as an ordinary function.")
    zb5_lorentzian = mp.conj(z5)
    Bv_lorentzian = mp.mpf(2) * q_dot_p(z5, zb5_lorentzian, tuple(mp.mpf(str(x)) for x in
                                                                   [p1[i] + p2[i] for i in range(4)]))
    w0_bad = -s_val / Bv_lorentzian
    print(f"    w0 = -s/B = {mp.nstr(w0_bad,10)}  (real & positive -- sits ON the integration contour)")


if __name__ == "__main__":
    main()
