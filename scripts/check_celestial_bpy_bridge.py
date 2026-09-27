"""Cross-manuscript numerical diagnostics; no zero ordinates used.
Requires mpmath. Numerical checks, not interval-certified proofs.
"""
import json
import mpmath as mp

mp.mp.dps = 60

def xi(s):
    if s == 0 or s == 1:
        return mp.mpf("0.5")
    return s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2

def log_F(z):
    return mp.log(xi(mp.mpf("0.5")+z)/xi(mp.mpf("0.5")))

t1 = mp.diff(log_F, 0, 2)/2
t2 = -mp.diff(log_F, 0, 4)/12

# X=sum Gamma(2,1)/n^2. Its Laplace transform is
# (pi*sqrt(t)/sinh(pi*sqrt(t)))^2.
def one_minus_laplace_log_coordinate(y):
    t = mp.exp(y)
    if y < -30:
        return 2*mp.zeta(2)*t - (2*mp.zeta(2)**2+mp.zeta(4))*t*t
    if y > 10:
        return mp.mpf(1)  # discarded Laplace term < exp(-900)
    v = mp.pi*mp.sqrt(t)
    return -mp.expm1(-2*mp.log(mp.sinh(v)/v))

def fractional_moment(q):
    fun = lambda y: one_minus_laplace_log_coordinate(y)*mp.exp(-q*y)
    integral = mp.quad(fun, [-160, -30, 0, 10, 160])
    # Leading analytic tails; omitted lower tail is O(exp(-(2-q)*160)).
    integral += mp.exp(-q*160)/q
    integral += 2*mp.zeta(2)*mp.exp(-(1-q)*160)/(1-q)
    return q*integral/mp.gamma(1-q)

checks = []
for q in map(mp.mpf, ["0.1", "0.25", "0.5", "0.7"]):
    observed = fractional_moment(q)
    target = 2*mp.pi**q*xi(2*q)
    checks.append({"q": str(q), "relative_error": mp.nstr(abs(observed/target-1), 12)})

out = {
    "xi_required_trace_A": mp.nstr(t1, 45),
    "xi_required_trace_A2": mp.nstr(t2, 45),
    "xi_trace_ratio": mp.nstr(t2/t1**2, 45),
    "circle_trace_ratio": "0.4",
    "normalized_HS_distance_lower_bound": mp.nstr(mp.sqrt(mp.mpf("0.4"))-mp.sqrt(t2/t1**2), 30),
    "fractional_moment_checks": checks,
    "cesaro_delta_0.1_epsilon_0.1_analytic_continuation": "-1/3; defining positive integral diverges",
}
print(json.dumps(out, indent=2))
