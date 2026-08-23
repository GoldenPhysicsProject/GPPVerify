"""
gpr_operator_reproduction.py

Direct follow-up to the literature check in the previous discovery entry
("literature check on shadow-discontinuity-from-tree loop mechanism",
commit fc20cad), which flagged as the well-scoped next step: "try
reproducing Gonzalez-Puhm-Rojas's own operator construction directly (eq
3.7-3.9) and see whether it can be re-expressed as a shadow-pair-sewing
statement after all, rather than assuming from the start that it must be."

Source: Gonzalez, Puhm, Rojas, "Loops on the Celestial Sphere"
(arXiv:2009.07290), full text extracted this session (pypdf) and read
directly (not from memory/paraphrase) -- section 3.2.1, eqs. (3.4)-(3.16).

## The actual GPR recipe, transcribed exactly from the paper

  A_1-loop = a * M_eps^(1) * A_tree                                  (3.7)

  M_eps^(1) = -(1/2)(mu^2 e^gammaE)^eps * integral d^Dp/(i pi^(D/2)) *
              st / [p^2 (p+p1)^2 (p+p1+p2)^2 (p+p4)^2]                (3.8)

i.e. M_eps^(1) IS the ordinary momentum-space scalar box integral (times
st and a normalization) -- a strictly 4-point, already-known object,
evaluated by ordinary QFT methods into hypergeometric functions (3.9).
GPR then note it factorizes as

  M_eps^(1) = (mu^2/-t)^eps * F1(r, eps),   r = -s/t                  (3.10)

The celestial 4-gluon amplitude's tree-level result comes from a *single*
Mellin transform over the overall energy scale w = -t at fixed cross-ratio
r (their eq 2.16). Multiplying the integrand by the loop's extra scalar
factor (mu^2/-t)^eps = (mu^2)^eps * w^eps means the loop's w-Mellin
integral is the SAME integral, evaluated with w^{i*lambda/2} replaced by
w^{i*lambda/2 - eps} -- i.e. the tree Mellin transform I(lambda) evaluated
at the shifted argument lambda + 2i*eps:

  I(lambda + 2i*eps) = e^{2i*eps*d/dlambda} I(lambda)                (3.13)

This file checks two things directly, not by paraphrase:

1. That (3.13) is exactly the elementary Mellin-transform shift theorem
   (multiplying a Mellin-transform integrand by w^{-eps} shifts the dual
   variable by 2i*eps) -- verified numerically to high precision on a
   generic test function with a closed-form Mellin transform, confirming
   the *mechanism* GPR use has nothing paper-specific about it: it is a
   general fact about the pair (Mellin transform, power-law multiplier),
   independent of what the loop integral or the celestial correlator
   actually are.

2. Whether ANY six-point (or higher-point) object, shadow transform, or
   discontinuity appears anywhere in the actual GPR derivation (3.4)-(3.16)
   -- checked by direct inspection of the transcribed equations above, not
   assumed. Answer recorded below.
"""
from mpmath import mp, mpf, mpc, exp, gamma, quad, inf, im, re, fabs

mp.dps = 40


# ---------------------------------------------------------------------
# Part 1: the elementary Mellin-shift identity behind GPR's eq. (3.13),
# checked on a generic test function, NOT the specific box integral --
# because the claim GPR make (and that this script verifies) is that the
# shift mechanism is generic, not particular to M_eps^(1).
#
# Mellin transform convention matching GPR's eq. (2.16)/(3.11):
#   I(lambda) := integral_0^inf (dw/w) w^{i*lambda/2} g(w)
# Claim: integral (dw/w) w^{i*lambda/2} * w^{-eps} * g(w) = I(lambda + 2i*eps)
# ---------------------------------------------------------------------
def mellin_I(g, lam, wmax=60):
    """I(lambda) = integral_0^inf (dw/w) w^{i lambda/2} g(w), g decaying."""
    f = lambda w: w ** (1j * lam / 2 - 1) * g(w)
    return quad(f, [0, wmax])


def check_mellin_shift_identity(lam, eps, label):
    """Check I(lam+2i*eps) = int (dw/w) w^{i*lam/2} w^{-eps} g(w) for
    g(w)=exp(-w), against the closed form Gamma(i*lam/2 - eps). `lam` is
    chosen per-call with enough negative imaginary part that
    Re(i*lam/2 - eps) > 0, so the defining integral genuinely converges at
    w->0 (a real Mellin transform only converges in a strip of Re(s); the
    physical principal-series lambda sits at the *boundary* of that strip,
    where the plain integral is not absolutely convergent at all -- GPR's
    own I(lambda) is implicitly a distributional/analytically-continued
    object for that reason, so testing the elementary shift identity
    itself here on a genuinely convergent contour is the correct, honest
    check, not a weakened one).
    """
    g = lambda w: exp(-w)

    # LHS: directly compute integral (dw/w) w^{i*lambda/2} * w^{-eps} * g(w)
    #    = integral (dw/w) w^{i*lambda/2 - eps} g(w)
    lhs = quad(lambda w: w ** (1j * lam / 2 - eps - 1) * g(w), [0, mp.inf])

    # RHS: I(lambda + 2i*eps) directly, i.e. w^{i*(lambda+2i*eps)/2 - 1}
    #    = w^{i*lambda/2 - eps - 1}  -- same integrand algebraically, but
    # computed via the *shifted-argument* formula to confirm the two
    # descriptions of the same object numerically agree to full precision.
    shifted_lam = lam + 2j * eps
    rhs = mellin_I(g, shifted_lam, wmax=mp.inf)

    # Independent closed-form check: for g(w)=exp(-w),
    # I(lambda) = integral w^{i*lambda/2 - 1} e^{-w} dw = Gamma(i*lambda/2).
    closed = gamma(1j * lam / 2 - eps)

    diff_lr = fabs(lhs - rhs)
    diff_closed = fabs(lhs - closed)
    print(f"[{label}] lam={complex(lam)}, eps={float(eps)}")
    print(f"  LHS                              = {complex(lhs)}")
    print(f"  RHS (shifted I)                  = {complex(rhs)}")
    print(f"  closed form Gamma(i*lam/2 - eps) = {complex(closed)}")
    print(f"  |LHS-RHS|    = {diff_lr}")
    print(f"  |LHS-closed| = {diff_closed}")
    assert diff_lr < mpf("1e-20"), "Mellin-shift identity failed numerically"
    assert diff_closed < mpf("1e-20"), "closed-form cross-check failed"
    return diff_lr, diff_closed


# ---------------------------------------------------------------------
# Part 2: does GPR's construction involve any six-point object, shadow
# transform, or discontinuity? Direct inspection of the transcribed
# equations (3.4)-(3.16), recorded as a checklist -- not a numerical
# check (there is nothing to compute; this is a structural fact about
# which symbols appear in the source equations).
# ---------------------------------------------------------------------
def structural_audit():
    findings = {
        "number of external legs in M_eps^(1) (eq 3.8)":
            "4 (p1, p2, p4, and the loop momentum p; same legs as A_tree)",
        "any 5th/6th leg (sewn pair) anywhere in (3.4)-(3.16)":
            "NO -- zero occurrences. The construction is 4-point start to finish.",
        "any shadow transform (Delta -> 1-Delta type) in (3.4)-(3.16)":
            "NO -- zero occurrences.",
        "any discontinuity / dispersion relation in (3.4)-(3.16)":
            "NO -- zero occurrences (confirms the earlier full-text grep).",
        "what IS the mechanism":
            ("M_eps^(1) is computed by ORDINARY QFT (Feynman integral, eq 3.8) "
             "at strictly 4 points, then factorized (3.10) into an overall-scale "
             "power (mu^2/-t)^eps times a cross-ratio function F1(r,eps); "
             "multiplying the tree Mellin integrand by that scale power is "
             "ALGEBRAICALLY a shift of the single Mellin (boost) variable "
             "lambda -> lambda + 2i*eps, promoted to the operator e^{2i*eps d/dlambda}. "
             "The extra P-hat operator (3.16) is a separate, unrelated device "
             "(a per-leg conformal-weight shift by 1/2 from [9]) needed only "
             "because the SAME eps also appears as an overall power of the "
             "four legs' weights in going from (3.13) to the fully covariant "
             "all-legs statement (3.14)-(3.16); it carries no six-point content "
             "either."),
    }
    for k, v in findings.items():
        print(f"- {k}:\n    {v}\n")
    return findings


if __name__ == "__main__":
    print("=" * 70)
    print("Part 1: elementary Mellin-shift identity behind GPR eq (3.13)")
    print("=" * 70)
    # Case A: lam purely imaginary -> s = i*lam/2 - eps is real, a plain
    # Gamma-function check.
    check_mellin_shift_identity(mpc(0, -3), mpf("0.13"), "real-s case")
    # Case B: lam has a nonzero real part too (genuine oscillatory
    # integrand in w), still with enough negative imaginary part for
    # absolute convergence at w->0.
    check_mellin_shift_identity(mpc("0.7", -3), mpf("0.31"), "oscillatory case")
    print()
    print("=" * 70)
    print("Part 2: structural audit of GPR's actual (3.4)-(3.16) recipe")
    print("=" * 70)
    structural_audit()
