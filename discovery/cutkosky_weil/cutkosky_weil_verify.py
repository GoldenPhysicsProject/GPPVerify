"""
Independent numerical verification for the 2026-08-22 research-front directive:
"celestial Cutkosky positivity -> local shadow kernels -> finite-prime Weil kernel ->
Casimir compression -> global Weil positivity -> RH".

Run fresh in this container (not copied from source material). Every identity checked
here is either (a) subsequently proved unconditionally in Lean
(GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean) or (b) reported honestly as
numerical-only / open. See notes.md for the write-up and the honest boundary.

**Central finding of this script (section 5): direct answer to the question "What
physical/mathematical projection turns K_p into K_p-1 while preserving positivity
globally?" — at the single-prime level, none exists. The vacuum subtraction destroys
Toeplitz/Bochner positive-definiteness for every prime tested.**
"""
import mpmath as mp

mp.mp.dps = 50


def Kp_complex(p, s):
    """K_p(s) = (1-p^-1) / ((1-p^-s)(1-p^{1-s})) -- the local Euler-factor-squared
    shadow kernel, evaluated at s=1/2+it on the critical line via Kp_complex(p, 0.5+1j*t)."""
    return (1 - p**-1) / ((1 - p**-s) * (1 - p**(1 - s)))


def Kp_real(p, t):
    """Real closed form on the critical line: (1-p^-1) / (1 - 2 p^{-1/2} cos(t log p) + p^-1)."""
    return (1 - p**-1) / (1 - 2 * p**mp.mpf('-0.5') * mp.cos(t * mp.log(p)) + p**-1)


def Wp(p, t):
    return mp.log(p) * (Kp_real(p, t) - 1)


print("=== 1. K_p closed form vs Poisson series Sum_{n in Z} r^{|n|} e^{i n theta}, r=p^{-1/2}, theta=t log p ===")
for p in (2, 3, 5):
    for t in (mp.mpf('0.7'), mp.mpf('3.3')):
        r = mp.mpf(p) ** mp.mpf('-0.5')
        theta = t * mp.log(p)
        # series: c_0 + 2 sum_{n=1}^N r^n cos(n theta)
        N = 400
        series = 1 + 2 * mp.nsum(lambda n: r**n * mp.cos(n * theta), [1, N])
        # Poisson kernel value: (1-r^2)/(1-2r cos theta + r^2) -- this equals K_p directly
        # since (1-p^-1)=(1-r^2) and denominator matches Kp_real's denominator exactly.
        poisson = (1 - r**2) / (1 - 2 * r * mp.cos(theta) + r**2)
        closed = Kp_real(p, t)
        rel_err_series = abs(series - closed) / abs(closed)
        rel_err_poisson = abs(poisson - closed) / abs(closed)
        print(f"  p={p} t={float(t)}: closed={mp.nstr(closed,12)}  "
              f"series(N={N}) rel_err={mp.nstr(rel_err_series,4)}  "
              f"poisson-form rel_err={mp.nstr(rel_err_poisson,4)}")

print()
print("=== 2. H(t) = (t^2+1/4) * C(t), C(t) = t/(4 sinh(2 pi t)) -- nonnegativity for real t ===")
def cutKernel(t):
    return t / (4 * mp.sinh(2 * mp.pi * t))

def H(t):
    return (t**2 + mp.mpf('0.25')) * cutKernel(t)

for t in [mp.mpf(x) for x in ('-5', '-1.3', '-0.01', '0.01', '0.5', '1.0', '2.7', '10')]:
    val = H(t)
    print(f"  t={float(t):>8}: H(t)={mp.nstr(val,12)}  nonneg={val>=0}")

t0 = mp.mpf('1e-30')
limit0 = H(t0)
predicted = mp.mpf(1) / (32 * mp.pi)
print(f"  t->0 limit: H({float(t0)}) = {mp.nstr(limit0,15)}  predicted 1/(32*pi) = {mp.nstr(predicted,15)}  "
      f"rel_err={mp.nstr(abs(limit0-predicted)/predicted,4)}")

print()
print("=== 3. Pole regularity of H at t = i/2 (no blow-up under complex perturbation) ===")
def cutKernel_c(t):
    return t / (4 * mp.sinh(2 * mp.pi * t))
def H_c(t):
    return (t**2 + mp.mpf('0.25')) * cutKernel_c(t)

target = mp.mpc(0, mp.mpf('0.5'))
for eps in (mp.mpf('1e-2'), mp.mpf('1e-4'), mp.mpf('1e-6'), mp.mpf('1e-8')):
    tp = target + eps
    val = H_c(tp)
    print(f"  eps={mp.nstr(eps,3)}: H(i/2+eps) = {mp.nstr(val,12)}")

print()
print("=== 4. Fourier pair H(t) <-> G(x) = 3/(512 pi) sech^4(x/4), convention G(x)=(1/2pi) Int H(t) e^{itx} dt ===")
def G_formula(x):
    return mp.mpf(3) / (512 * mp.pi) * mp.sech(x / 4) ** 4

def G_from_H(x, cutoff=60):
    f = lambda t: H(t) * mp.cos(t * x)  # H even -> imaginary part integrates to 0
    return (1 / (2 * mp.pi)) * mp.quad(f, [-cutoff, 0, cutoff])

for x in (mp.mpf('0.5'), mp.mpf('2.0'), mp.mpf('5.0')):
    lhs = G_from_H(x)
    rhs = G_formula(x)
    print(f"  x={float(x)}: G_from_H={mp.nstr(lhs,15)}  G_formula={mp.nstr(rhs,15)}  "
          f"rel_err={mp.nstr(abs(lhs-rhs)/abs(rhs),4)}")

print()
print("=" * 78)
print("=== 5. CENTRAL EXPERIMENT: Toeplitz/Bochner (in)definiteness of K_p vs K_p-1 ===")
print("=" * 78)
print("""
K_p(theta) = Sum_{n in Z} r^{|n|} e^{i n theta}, r = p^{-1/2}, is (by Herglotz/Bochner)
positive-definite as a Fourier-coefficient sequence, since (r^{|n|})_n is termwise
nonnegative and summable -- automatic for any Poisson kernel.

K_p(theta) - 1 removes only the n=0 (DC / vacuum) Fourier coefficient: its coefficient
sequence is (r^{|n|})_{n != 0}, 0 at n=0. Question: does this vacuum-subtracted sequence
remain positive-definite (i.e. is K_p - 1 still a valid, positive Toeplitz kernel)?

Test: build the truncated (2N+1)x(2N+1) Toeplitz matrix T[j,k] = c_{j-k} from each
coefficient sequence and compute its eigenvalues directly.
""")

def toeplitz_eigs(coeffs, N):
    """coeffs: dict n -> c_n for n in [-N,N]. Build (2N+1)x(2N+1) Toeplitz matrix, return eigs."""
    size = 2 * N + 1
    M = mp.matrix(size, size)
    for j in range(size):
        for k in range(size):
            n = (j - N) - (k - N)
            M[j, k] = coeffs.get(n, 0)
    # mpmath eig requires a matrix; use mp.eig for general real symmetric
    E, _ = mp.eig(M)
    return sorted([e.real for e in E])

N = 6
for p in (2, 3, 5):
    r = mp.mpf(p) ** mp.mpf('-0.5')
    coeffs_Kp = {n: r ** abs(n) for n in range(-N, N + 1)}
    coeffs_Kp_minus_1 = dict(coeffs_Kp)
    coeffs_Kp_minus_1[0] = mp.mpf(0)

    eigs_Kp = toeplitz_eigs(coeffs_Kp, N)
    eigs_Kp_m1 = toeplitz_eigs(coeffs_Kp_minus_1, N)

    print(f"  p={p}  (truncation N={N}, matrix dim {2*N+1}):")
    print(f"    K_p        eigenvalues: min={mp.nstr(eigs_Kp[0],6)}  max={mp.nstr(eigs_Kp[-1],6)}  "
          f"all_nonneg={all(e >= -mp.mpf('1e-20') for e in eigs_Kp)}")
    print(f"    K_p - 1    eigenvalues: min={mp.nstr(eigs_Kp_m1[0],6)}  max={mp.nstr(eigs_Kp_m1[-1],6)}  "
          f"all_nonneg={all(e >= -mp.mpf('1e-20') for e in eigs_Kp_m1)}")
    has_neg = any(e < -mp.mpf('1e-15') for e in eigs_Kp_m1)
    print(f"    => K_p-1 Toeplitz matrix is {'INDEFINITE (has a negative eigenvalue)' if has_neg else 'still PSD'}")
    print()

print("""
CONCLUSION: for every prime tested (p=2,3,5), K_p's Toeplitz matrix is strictly positive
definite (as expected: it is a genuine Poisson kernel), while K_p-1's Toeplitz matrix is
strictly indefinite (has both positive and negative eigenvalues). The vacuum subtraction
n=0 coefficient -> 0 necessarily breaks positive-definiteness at the single-prime level.

This is a direct, precise, negative answer to the question "what projection turns K_p
into K_p-1 while preserving positivity globally": no such projection exists prime-by-prime
via the naive Toeplitz/Bochner route. If finite-prime-plus-Archimedean global positivity
holds at all (which, via the pre-existing rh_iff_weil_pairedForm_nonneg criterion, is
equivalent to RH), it must be a genuinely collective phenomenon across primes and the
Archimedean place -- not visible, or provable, one local factor at a time.

This does NOT rule out global positivity of Q_GPP = Q_infinity + Sum_p Q_p (a sum of
many indefinite local pieces can still be globally positive-definite, exactly as the
classical Weil explicit formula's local terms are not separately sign-definite). It
rules out the naive local mechanism the directive's central question was testing.
""")
