"""
verify_euler_factor_logderiv.py

Sixth-pass Cutkosky-Weil work: numerically verify Wp(p,t) = 2*Re(-zeta_p'/zeta_p(1/2+it))
exactly, where zeta_p(s) = (1-p^{-s})^{-1} is the local Euler factor and
Wp(p,t) = log(p)*(Kp(p,t)-1) is already defined and used in CutkoskyWeilBridge.lean.
Checked via direct numerical differentiation of zeta_p (not from the closed-form
geometric-series shortcut), across four primes and three t values, at dps=40.
"""

from mpmath import mp, mpf, mpc, log, cos, diff, re

mp.dps = 40


def Kp(p, t):
    p, t = mpf(p), mpf(t)
    return (1 - 1 / p) / (1 - 2 * p ** mpf('-0.5') * cos(t * log(p)) + 1 / p)


def Wp(p, t):
    return log(mpf(p)) * (Kp(p, t) - 1)


def zeta_p(s, p):
    return 1 / (1 - mpf(p) ** (-s))


def minus_zeta_p_logderiv(s, p):
    """-zeta_p'(s)/zeta_p(s), via direct numerical differentiation of log(1-p^-s)."""
    return diff(lambda s_: mp.log(1 - mpf(p) ** (-s_)), s)


if __name__ == "__main__":
    worst = mpf(0)
    for p in [2, 3, 5, 7]:
        for t in [mpf('0.7'), mpf('1.3'), mpf('3.9')]:
            s = mpc(mpf('0.5'), t)
            lhs = Wp(p, t)
            rhs = 2 * re(minus_zeta_p_logderiv(s, p))
            diff_val = abs(lhs - rhs)
            worst = max(worst, diff_val)
            print(f"p={p}, t={float(t)}: Wp={lhs}  2Re(-zeta_p'/zeta_p)={rhs}  diff={diff_val}")
    print()
    print(f"worst-case discrepancy across all (p,t): {worst}")
