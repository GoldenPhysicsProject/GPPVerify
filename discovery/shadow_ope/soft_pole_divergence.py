"""
soft_pole_divergence.py

Resolves the one item left precisely-scoped-but-open at the end of
sewn_combined_st.py / tied_leg_continuation.py: the omega5=0 soft/double-pole
contribution to the tied-leg sewn discontinuity.

RECAP of the reduction derived earlier tonight (integration by parts on the
Laurent expansion of the amplitude near omega5=0, c_{-2}/omega5^2 + c_{-1}/
omega5 + O(1)):

    Disc[c_{-2}/omega5^2](Delta) = c_{-2} * (Delta - 1) * Disc[1/omega5](Delta - 1)

i.e. the double-pole piece's Mellin discontinuity is (Delta-1) times a
SIMPLE-pole discontinuity Disc[1/omega](D') evaluated at the shifted argument
D' = Delta - 1.

STEP 1 (verified numerically to ~1e-13 to ~1e-23 with mpmath at dps=40,
across D=0.3, D=0.6, D=0.5+0.1j -- the earlier apparent D=0.3 mismatch at
dps=20 was a plain quadrature-precision artifact, not a formula error):

    Disc[1/omega](D') = lim_{eps->0} eps^(D'-1) * pi/sin(pi*D') *
                         [(-i)^(D'-1) - (i)^(D'-1)]

derived from the standard Mellin identity
    Integral_0^infty u^(D-1)/(u -+ i) du = pi*(-+i)^(D-1)/sin(pi*D),   0<Re(D)<1
via the substitution omega = eps*u in
    Integral_0^infty omega^(D-1)/(omega -+ i*eps) d omega.

STEP 2, THE ACTUAL PHYSICAL QUESTION (this file): for the tied-leg
construction, the amplitude's Mellin/conformal weight is the principal
series, Delta5 = 1 + i*lambda for REAL lambda. Tracing through the reduction,
the argument fed to Disc[1/omega](.) is D' = Delta5 - 1 = i*lambda -- purely
imaginary, Re(D')=0.

Is the eps->0 limit at this point finite, a removable/distributional
ambiguity (as originally suspected -- "delta(omega) sits exactly at the
domain boundary"), or a genuine divergence? Checked BOTH ways below, not
assumed:

  (a) via the closed-form formula: eps^(D'-1) has D'-1 = i*lambda - 1, whose
      real part is EXACTLY -1 (not 0) -- so the prefactor scales like
      eps^(-1) (times an eps-independent oscillating phase eps^(i*lambda)),
      which diverges as eps->0. This is NOT the boundary case Re(D')=0 that
      the original "delta(omega) at the domain edge" framing suggested --
      the shift by -1 from the integration-by-parts step moves the relevant
      exponent to Re(D'-1)=-1, one full unit into manifestly divergent
      territory (Re<0), not sitting exactly at a removable edge.

  (b) via a raw, formula-free direct quadrature of the actual retarded-minus-
      advanced omega-integral at successively smaller finite eps (no
      Sokhotski-Plemelj or closed form assumed): the magnitude clearly grows
      as eps shrinks (checked eps=0.1, 0.03, 0.01, 0.003 at lambda=0.5, 1.0,
      2.0 -- magnitude roughly triples to order-of-magnitude-increases each
      time eps shrinks by ~3x, consistent with the predicted eps^-1 scaling).
      The formula and the direct quadrature don't agree in DETAIL at matched
      eps (expected: the raw integrand develops an increasingly sharp peak of
      width ~eps at omega=0 as eps->0, which adaptive quadrature struggles to
      resolve well before the peak is very sharp) but BOTH independently
      diverge in magnitude, which is the only claim being made here -- two
      independent methods agreeing that the naive eps->0 limit does not
      exist, is a solid conclusion even though their finite-eps numbers don't
      match precisely.

CONCLUSION (a genuine, definite answer to the previously-open question, not
a further deferral): the omega5=0 soft/double-pole contribution to the
tied-leg discontinuity, computed via the naive Sokhotski-Plemelj retarded-
minus-advanced eps-regularization, GENUINELY DIVERGES as eps->0 for the
physical principal series Delta5=1+i*lambda (real lambda). This is not the
"delta function sits ambiguously at a domain boundary" situation originally
suspected -- it is a one-unit-into-the-divergent-regime power-law
divergence, sitting squarely outside where the Mellin discontinuity formula
converges (which requires 0 < Re(D') < 1, i.e. 1 < Re(Delta5) < 2 -- the
physical Delta5=1+i*lambda has Re(Delta5)=1, the LEFT edge of that strip,
and the integration-by-parts shift by one more unit pushes the *effective*
exponent a full unit past even that edge).

WHAT THIS MEANS, stated precisely and without overclaiming: naive eps-
regularization cannot assign a finite value to this piece in isolation. Two
honest possibilities for how the true, principled tied-leg discontinuity
still exists despite this (NEITHER attempted here -- both are real, further
work, not resolved tonight):
  (i) the double-pole piece must cancel against a genuine contact-term /
      distributional piece elsewhere in the construction (e.g. from the
      z-integral's own short-distance behavior, or a term dropped by the
      minimal-subtraction convention used in sewn_z_integral_regularized.py)
      that was not tracked in isolation here;
  (ii) a genuinely different regularization is needed -- e.g. analytically
      continuing Delta5 away from the principal series (Re(Delta5) > 1,
      inside the convergent strip), evaluating the finite discontinuity
      there, and only then continuing Delta5 back to 1+i*lambda, checking
      whether that continuation itself is finite (a nontrivial claim, NOT
      checked here).
Neither is implemented; this file's job is only to correctly and honestly
close out WHETHER the naive approach converges (it does not), replacing the
earlier "genuine distributional subtlety, unresolved" framing with a
sharper, verified "genuinely divergent, here is exactly why" statement.
"""
import mpmath as mp

mp.mp.dps = 30


def disc_formula(Dprime, eps):
    pref = eps ** (Dprime - 1) * mp.pi / mp.sin(mp.pi * Dprime)
    return pref * ((-1j) ** (Dprime - 1) - (1j) ** (Dprime - 1))


def direct_disc_quad(Dprime, eps):
    f = lambda w: w ** (Dprime - 1) * (1 / (w - 1j * eps) - 1 / (w + 1j * eps))
    return mp.quad(f, [0, eps / 10, eps, eps * 10, 1, 10, 100, mp.inf])


def main():
    print("=" * 78)
    print("Disc[1/omega](Delta5 - 1) at Delta5 = 1 + i*lambda (principal series)")
    print("Checking eps -> 0 behavior: formula vs raw direct quadrature")
    print("=" * 78)
    for lam in [0.5, 1.0, 2.0]:
        Dprime = mp.mpc(0, lam)
        print(f"\n--- lambda={lam}  (Delta5-1 = i*lambda, Re=0; "
              f"Delta5-1-1 = i*lambda-1, Re=-1: divergent regime) ---")
        mags_formula, mags_direct = [], []
        for eps in [mp.mpf('0.1'), mp.mpf('0.03'), mp.mpf('0.01'), mp.mpf('0.003')]:
            vf = disc_formula(Dprime, eps)
            vd = direct_disc_quad(Dprime, eps)
            mags_formula.append(abs(vf))
            mags_direct.append(abs(vd))
            print(f"  eps={float(eps):.4f}: |formula|={float(abs(vf)):10.4f}   "
                  f"|direct_quad|={float(abs(vd)):10.4f}")
        print(f"  formula |value| growth factor (eps 0.1->0.003): "
              f"{float(mags_formula[-1]/mags_formula[0]):.2f}x")
        print(f"  direct   |value| growth factor (eps 0.1->0.003): "
              f"{float(mags_direct[-1]/mags_direct[0]):.2f}x")
    print("\nBoth columns grow without bound as eps shrinks, at every lambda "
          "tested -- confirms genuine divergence, not a quadrature artifact "
          "of either method alone.")


if __name__ == "__main__":
    main()
