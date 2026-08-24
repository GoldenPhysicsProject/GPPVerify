"""
Independent numerical verification for the 2026-08-22 research-front directive:
"celestial Cutkosky positivity -> local shadow kernels -> finite-prime Weil kernel ->
Casimir compression -> global Weil positivity -> RH".

Run fresh in this container (not copied from source material). Every identity checked
here is either (a) subsequently proved unconditionally in Lean
(GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean) or (b) reported honestly as
numerical-only / open. See notes.md for the write-up and the honest boundary.

**SELF-CORRECTED VERSION.** The first pass of section 5 below tested the wrong positivity
notion (see notes.md "Self-correction" section for the full account): it built a Toeplitz
matrix T[j,k] = c_{j-k} treating the Fourier-coefficient sequence itself as if it indexed a
new kernel on the integers, and found that matrix indefinite. That is a real computation,
but it does not test whether K_r - 1 is a positive-definite KERNEL on the circle (the
physically relevant question). The corrected test (section 5 below) builds the Gram matrix
M_{jk} = (K_r-1)(theta_j - theta_k) from point evaluations at arbitrary finite angle
configurations -- the actual definition of kernel positive-definiteness -- and confirms it
IS positive semidefinite, exactly as the finite Fourier/Gram-square identity predicts.
"""
import mpmath as mp
import random

mp.mp.dps = 50


def Kp_complex(p, s):
    return (1 - p**-1) / ((1 - p**-s) * (1 - p**(1 - s)))


def Kp_real(p, t):
    return (1 - p**-1) / (1 - 2 * p**mp.mpf('-0.5') * mp.cos(t * mp.log(p)) + p**-1)


def Wp(p, t):
    return mp.log(p) * (Kp_real(p, t) - 1)


def KrClosed(r, theta):
    """General closed form: (1-r^2)/(1-2r cos(theta)+r^2). Kp p t = KrClosed(p^{-1/2}, t log p)."""
    return (1 - r**2) / (1 - 2 * r * mp.cos(theta) + r**2)


print("=== 1. K_p closed form vs Poisson series Sum_{n in Z} r^{|n|} e^{i n theta}, r=p^{-1/2}, theta=t log p ===")
for p in (2, 3, 5):
    for t in (mp.mpf('0.7'), mp.mpf('3.3')):
        r = mp.mpf(p) ** mp.mpf('-0.5')
        theta = t * mp.log(p)
        N = 400
        series = 1 + 2 * mp.nsum(lambda n: r**n * mp.cos(n * theta), [1, N])
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
    f = lambda t: H(t) * mp.cos(t * x)
    return (1 / (2 * mp.pi)) * mp.quad(f, [-cutoff, 0, cutoff])

for x in (mp.mpf('0.5'), mp.mpf('2.0'), mp.mpf('5.0')):
    lhs = G_from_H(x)
    rhs = G_formula(x)
    print(f"  x={float(x)}: G_from_H={mp.nstr(lhs,15)}  G_formula={mp.nstr(rhs,15)}  "
          f"rel_err={mp.nstr(abs(lhs-rhs)/abs(rhs),4)}")

print()
print("=" * 78)
print("=== 5. CENTRAL EXPERIMENT (CORRECTED): Gram-matrix positivity of K_r - 1 as a KERNEL ===")
print("=" * 78)
print("""
CORRECTED test. K_r(theta) - 1 is a function on the circle; the question "is it a positive
kernel" means: for ANY finite set of angles theta_1,...,theta_N (not necessarily equally
spaced) and ANY complex weights c_1,...,c_N,

    Sum_{j,k} conj(c_j) c_k (K_r - 1)(theta_j - theta_k) >= 0   ?

This is the Gram matrix M_{jk} = (K_r-1)(theta_j - theta_k) being positive semidefinite --
exactly GppHaarPositivityWeil.PositiveType applied to K_r - 1. This is NOT the same as
asking whether the Fourier-coefficient sequence (c_n) is itself a positive-definite
sequence on Z (that was the earlier, wrong test).

The finite Fourier/Gram-square identity (proved in Lean, KrClosed_minus_one_positiveType):

    Sum_{j,k} conj(c_j) c_k (K_r-1)(theta_j-theta_k) = Sum_{n != 0} r^{|n|} |Sum_j c_j e^{-i n theta_j}|^2 >= 0

manifestly a sum of nonnegative terms. Verify this numerically for RANDOM (non-equally-spaced)
finite point configurations and RANDOM complex weights, by (a) building the Gram matrix
directly from the closed-form K_r - 1 and checking its eigenvalues are all >= 0, and
(b) cross-checking the quadratic form against the truncated Fourier-square sum.
""")

random.seed(20260822)


def gram_matrix(r, thetas):
    N = len(thetas)
    M = mp.matrix(N, N)
    for j in range(N):
        for k in range(N):
            M[j, k] = KrClosed(r, thetas[j] - thetas[k]) - (1 if j != k or True else 0)
            # (K_r - 1) evaluated at theta_j - theta_k; at j=k this is K_r(0)-1 = r-dependent, not special-cased
            M[j, k] = KrClosed(r, thetas[j] - thetas[k]) - 1
    return M


def hermitian_eigs(M):
    N = M.rows
    # mpmath needs Hermitian eig via eigsy is for symmetric real; our matrix is complex Hermitian
    # (K_r-1)(theta_j-theta_k) is real and symmetric in j,k here since it only depends on the
    # cosine of the angle difference -- so M is real symmetric.
    E, _ = mp.eig(M)
    return sorted([e.real for e in E])


for p in (2, 3, 5):
    r = mp.mpf(p) ** mp.mpf('-0.5')
    for trial, N in enumerate([5, 9], start=1):
        thetas = [mp.mpf(random.uniform(-10, 10)) for _ in range(N)]
        M = gram_matrix(r, thetas)
        eigs = hermitian_eigs(M)
        min_eig = eigs[0]
        all_nonneg = all(e >= -mp.mpf('1e-25') for e in eigs)
        print(f"  p={p} (r={mp.nstr(r,6)}), trial {trial}, N={N} random (non-equally-spaced) points: "
              f"min eigenvalue={mp.nstr(min_eig,8)}  all_nonneg={all_nonneg}")

print()
print("--- Cross-check: quadratic form value vs the Fourier-square sum, one configuration ---")
p = 3
r = mp.mpf(p) ** mp.mpf('-0.5')
N = 4
thetas = [mp.mpf(random.uniform(-10, 10)) for _ in range(N)]
weights = [mp.mpc(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(N)]

quad_form = mp.mpc(0)
for j in range(N):
    for k in range(N):
        quad_form += mp.conj(weights[j]) * weights[k] * (KrClosed(r, thetas[j] - thetas[k]) - 1)

fourier_sum = mp.mpc(0)
NMAX = 300
for n in range(-NMAX, NMAX + 1):
    if n == 0:
        continue
    Sn = sum(weights[j] * mp.e ** (-1j * n * thetas[j]) for j in range(N))
    fourier_sum += r ** abs(n) * abs(Sn) ** 2

print(f"  quadratic form (from closed-form K_r-1): {mp.nstr(quad_form, 15)}")
print(f"  Fourier-square sum (truncated at |n|<={NMAX}):  {mp.nstr(fourier_sum, 15)}")
print(f"  agreement: {mp.nstr(abs(quad_form - fourier_sum), 6)}")
print(f"  quad_form.real >= 0: {quad_form.real >= 0}   quad_form.imag ~ 0: {mp.nstr(quad_form.imag, 4)}")

print("""
CONCLUSION (corrected): for every prime tested (p=2,3,5), and for random, non-equally-spaced
finite point configurations, the Gram matrix M_{jk}=(K_r-1)(theta_j-theta_k) is positive
semidefinite -- all eigenvalues >= 0 (to numerical precision). This is the mathematically
correct answer to "does K_r - 1 remain positive after vacuum subtraction": YES, as a kernel /
convolution operator, trivially -- dropping the n=0 Fourier eigenvalue to zero cannot make
the (already nonnegative) remaining eigenvalues negative. The earlier finding (Toeplitz
matrix of the coefficient sequence itself being indefinite) was a correctly-computed answer
to a DIFFERENT, less relevant question, and should not have been reported as "no positivity-
preserving projection exists" -- see notes.md for the full self-correction.

This does NOT by itself establish global Weil positivity (that requires assembling
Q_GPP = Q_inf + Sum_p Q_p across all primes plus the Archimedean place, and bridging to the
classical Weil explicit formula -- both open, honestly scoped in notes.md). It establishes
that the single-prime local mechanism is positivity-COMPATIBLE, reversing the earlier
negative claim.
""")
