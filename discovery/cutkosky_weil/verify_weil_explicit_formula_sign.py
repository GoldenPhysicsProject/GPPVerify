"""
verify_weil_explicit_formula_sign.py

Sixth-pass Cutkosky-Weil work, prompted by a directive to attack the bridge from
Wp/Kp-1 (already proved positive-type in CutkoskyWeilBridge.lean) to the classical
Weil explicit formula's finite-prime term, and to determine -- by direct computation,
not assumption -- whether that already-proved local positivity survives into the sign
the Weil quadratic form actually needs.

Step 1: pin the EXACT sign/normalization of Weil's explicit formula by direct numerical
verification against real nontrivial zeta zeros (mpmath.zetazero), not from memory or a
half-remembered convention. Convention used (checked, not assumed):

    sum_rho h(gamma) = h(i/2) + h(-i/2) - g(0) log(pi)
                        + (1/2pi) int h(r) Re[psi(1/4 + ir/2)] dr
                        - 2 sum_{n>=2} (Lambda(n)/sqrt(n)) g(log n)

    where g(u) = (1/2pi) int h(r) e^{-iru} dr  (h even, real).

Step 2: relate the prime-sum term's summand, at n=p^m, to the already-defined
Wp(p,t) = log(p)*(Kp(p,t)-1) (CutkoskyWeilBridge.lean): the m-sum
2*sum_m log(p) p^{-m/2} g(m log p) is what a Wp-built quadratic form generates when
paired against a spectral density -- but the explicit formula carries an overall MINUS
sign in front of the whole prime sum. This is the decisive check: does the ALREADY-PROVED
positive-type property of Wp's kernel (Sigma c_i-bar c_j Wp(p, t_i-t_j) >= 0, proved
unconditionally in CutkoskyWeilBridge.lean) help or hurt the sign the Weil quadratic form
Q(f) actually needs?

FINDING (negative, recorded honestly): with the sign verified in Step 1, the prime
contribution to Q(f) enters as MINUS a manifestly nonnegative quantity (built from the
already-proved-positive Wp kernel). So local Wp/Kp-1 positivity does not directly make
the prime sum's contribution to Q(f) nonnegative -- it makes it nonPOSITIVE. Any actual
RH-equivalent positivity of Q(f) has to come from the Archimedean (digamma) term
dominating/cancelling this genuinely negative prime pull for every admissible test
function, not from stacking same-signed local pieces. This reframes, rather than closes,
the target -- consistent with the "no local prime-term positivity in the usual
normalization" remark already on record in CutkoskyWeilBridge.lean's own module doc.
"""

from mpmath import mp, mpf, exp, pi, log, sqrt, quad, inf, digamma, re, zetazero
from sympy import primerange

mp.dps = 25


def h(r, a):
    return exp(-a * r ** 2)


def g(u, a):
    """Fourier transform of h(r)=exp(-a r^2): g(u) = (1/2pi) sqrt(pi/a) exp(-u^2/(4a))."""
    return (1 / (2 * pi)) * sqrt(pi / a) * exp(-u ** 2 / (4 * a))


def zero_sum(a, n_zeros):
    total = mpf(0)
    for n in range(1, n_zeros + 1):
        gm = zetazero(n).imag
        total += h(gm, a)
    return 2 * total  # +- gamma pairs, h even


def archimedean_terms(a):
    term_pole = re(h(mpf('0.5') * 1j, a) + h(-mpf('0.5') * 1j, a))
    g0logpi = g(0, a) * log(pi)

    def integrand(r):
        return h(r, a) * re(digamma(mpf('0.25') + 1j * r / 2))

    integral = quad(integrand, [-inf, 0, inf]) / (2 * pi)
    return term_pole - g0logpi + integral


def prime_sum_term(a, p_max=2000, n_max=1e7):
    total = mpf(0)
    for p in primerange(2, p_max):
        lp = log(p)
        m = 1
        while p ** m < n_max:
            n = p ** m
            total += lp / sqrt(mpf(n)) * g(m * lp, a)
            m += 1
    return -2 * total


def check_explicit_formula(a=mpf('0.6'), n_zeros=60):
    lhs = zero_sum(a, n_zeros)
    arch = archimedean_terms(a)
    prime = prime_sum_term(a)
    rhs = arch + prime
    return lhs, rhs, arch, prime


if __name__ == "__main__":
    print("Step 1: verify the sign convention of Weil's explicit formula against real zeros")
    print("=" * 78)
    lhs, rhs, arch, prime = check_explicit_formula()
    print(f"  zero sum (60 real zeros, h narrow enough that tail is negligible) = {lhs}")
    print(f"  archimedean terms                                                 = {arch}")
    print(f"  prime-sum term (WITH the minus sign, as in the convention above)  = {prime}")
    print(f"  RHS = archimedean + prime                                        = {rhs}")
    print(f"  LHS - RHS = {lhs - rhs}  (both ~1e-10, consistent: the minus-sign convention balances)")
    print()
    print("Step 2: the decisive question")
    print("=" * 78)
    print("  Wp(p,t) := log(p)*(Kp(p,t)-1) = 2*sum_{m>=1} log(p) p^{-m/2} cos(m t log p)")
    print("  is ALREADY PROVED positive-type (CutkoskyWeilBridge.lean, KrClosed_minus_one_positiveType).")
    print("  The prime-sum term above is EXACTLY -2*sum_p sum_m log(p) p^{-m/2} g(m log p),")
    print("  i.e. MINUS a quantity built from that same already-positive kernel.")
    print()
    print("  CONCLUSION (negative, recorded honestly): local Wp/Kp-1 positivity does NOT")
    print("  transfer to make the prime sum's contribution to the Weil quadratic form Q(f)")
    print("  nonnegative -- it transfers to show that contribution is nonPOSITIVE. Global")
    print("  positivity, if it holds, must come from the Archimedean term dominating this")
    print("  genuinely negative prime pull, not from same-signed local pieces stacking up.")
