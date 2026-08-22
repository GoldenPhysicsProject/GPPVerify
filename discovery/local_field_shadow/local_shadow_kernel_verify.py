"""
Independent numerical verification for "Local-field shadow kernels, celestial unitarity,
and the adelic principal series" (Toupin, 2026).

Every check here is run fresh in this container against mpmath, not copied from the paper.
Results in Section 12 (archKernel reflection + principal-series positivity) and the diagonal
lift are also formalized in Lean (GppVerify/QuantumGravity/{LocalShadowKernel,
DiagonalConformalLift}.lean); everything else here is numerical-only and NOT claimed as a
Lean theorem -- see local_shadow_kernel_notes.md for what is and is not established.
"""
import mpmath as mp

mp.mp.dps = 40


def rel(a, b):
    a, b = mp.mpc(a), mp.mpc(b)
    if abs(b) == 0:
        return abs(a)
    return abs(a - b) / abs(b)


print("=== 1. Archimedean K_{inf,d}(a) = Gamma(a)Gamma(d-a)/Gamma(d), integral vs closed form ===")
def K_inf_integral(d, a):
    f = lambda x: x**(a - 1) / (1 + x)**d
    return mp.quad(f, [0, mp.inf])

def K_inf_closed(d, a):
    return mp.gamma(a) * mp.gamma(d - a) / mp.gamma(d)

for d, a in [(mp.mpf(3), mp.mpf('1.3')), (mp.mpf(4), mp.mpc(1.5, 0.4)),
             (mp.mpf(2), mp.mpf('0.7'))]:
    num = K_inf_integral(d, a)
    closed = K_inf_closed(d, a)
    print(f"  d={d}, a={a}: rel err = {mp.nstr(rel(num, closed), 4)}")

print("=== 2. Shadow reflection K(a) = K(d-a) ===")
for d, a in [(mp.mpf(3), mp.mpc(1.1, 0.6)), (mp.mpf(5), mp.mpc(2.3, -1.1))]:
    lhs = K_inf_closed(d, a)
    rhs = K_inf_closed(d, d - a)
    print(f"  d={d}, a={a}: rel err = {mp.nstr(rel(lhs, rhs), 4)}")

print("=== 3. Principal-series positivity: K(d/2+it) = |Gamma(d/2+it)|^2/Gamma(d) > 0 ===")
for d, t in [(mp.mpf(2), mp.mpf('1.7')), (mp.mpf(3), mp.mpf('0.4')), (mp.mpf(1), mp.mpf('3.2'))]:
    a = d / 2 + 1j * t
    val = K_inf_closed(d, a)
    target = abs(mp.gamma(a))**2 / mp.gamma(d)
    print(f"  d={d}, t={t}: K={mp.nstr(val.real,10)} target={mp.nstr(target,10)} "
          f"im={mp.nstr(val.imag,4)}  rel err = {mp.nstr(rel(val, target), 4)}  positive={val.real > 0}")

print("=== 4. d=1 Euler reflection specialization: K_{inf,1}(s) = Gamma(s)Gamma(1-s) = pi/sin(pi s) ===")
for s in [mp.mpf('0.3'), mp.mpc(0.5, 1.2), mp.mpf('0.9')]:
    lhs = K_inf_closed(1, s)
    rhs = mp.pi / mp.sin(mp.pi * s)
    print(f"  s={s}: rel err = {mp.nstr(rel(lhs, rhs), 4)}")

print("=== 5. d=2 celestial-cut specialization: K_{inf,2}(1+i*lam) = lam/(8*sinh(pi*lam)) * 8pi ===")
# Phi_cut(1+i*lam) = (1/8pi) K_{inf,2}(1+i*lam) should equal lam/(8 sinh(pi*lam))
for lam in [mp.mpf('0.6'), mp.mpf('2.1'), mp.mpf('5.0')]:
    a = 1 + 1j * lam
    Phi_cut = K_inf_closed(2, a) / (8 * mp.pi)
    target = lam / (8 * mp.sinh(mp.pi * lam))
    print(f"  lam={lam}: Phi_cut={mp.nstr(Phi_cut.real,10)} target={mp.nstr(target,10)} "
          f"rel err = {mp.nstr(rel(Phi_cut, target), 4)}")

print("=== 6. Delta=2s and shadow commutation (trivial algebra, sanity check) ===")
for s in [mp.mpf('0.37'), mp.mpc(0.5, 2.4)]:
    Delta = 2 * s
    lhs = 2 * (1 - s)
    rhs = 2 - Delta
    print(f"  s={s}: 2(1-s)={mp.nstr(lhs,10)} 2-Delta={mp.nstr(rhs,10)} rel err={mp.nstr(rel(lhs,rhs),4)}")

print("=== 7. Finite-place kernel K_{q,d}(a): shell sum vs closed form ===")
def K_q_shell_sum(q, d, a, N=4000):
    # K_{q,d}(a) = int_{F^x} |x|^a / max(1,|x|)^d d^x x, with d^x x normalized so vol(O^x)=1.
    # Multiplication by the uniformizer pi^v is a translation of the multiplicative group, so
    # by translation-invariance of d^x x every valuation-v shell {v(x)=v} = pi^v O^x has the
    # SAME volume as O^x itself, i.e. exactly 1 -- not (1-1/q) (that factor belongs to the
    # different, additive-Haar-derived normalization, which is NOT the one specified: "the
    # unit group has volume 1"). |x| = q^{-v} on that shell.
    total = mp.mpf(0)
    for v in range(-N, N):
        absx = q**(-v)
        total += absx**a / max(1, absx)**d
    return total

def K_q_closed(q, d, a):
    return (1 - q**(-d)) / ((1 - q**(-a)) * (1 - q**(-(d - a))))

for q, d, a in [(2, mp.mpf(3), mp.mpf('1.4')), (3, mp.mpf(2), mp.mpf('0.6')),
                (5, mp.mpf(4), mp.mpf('2.5'))]:
    shell = K_q_shell_sum(q, d, a)
    closed = K_q_closed(q, d, a)
    print(f"  q={q}, d={d}, a={a}: shell={mp.nstr(shell,15)} closed={mp.nstr(closed,15)} "
          f"rel err = {mp.nstr(rel(shell, closed), 4)}")

print("=== 8. Finite-place reflection K_{q,d}(a) = K_{q,d}(d-a) ===")
for q, d, a in [(2, mp.mpf(3), mp.mpf('1.4')), (7, mp.mpf(5), mp.mpf('2.1'))]:
    lhs = K_q_closed(q, d, a)
    rhs = K_q_closed(q, d, d - a)
    print(f"  q={q}, d={d}, a={a}: rel err = {mp.nstr(rel(lhs, rhs), 4)}")

print("=== 9. Finite-place principal-series modulus-square: K_{q,d}(d/2+it) = (1-q^-d)/|1-q^(-d/2-it)|^2 ===")
for q, d, t in [(2, mp.mpf(3), mp.mpf('0.9')), (5, mp.mpf(2), mp.mpf('1.7'))]:
    a = d / 2 + 1j * t
    lhs = K_q_closed(q, d, a)
    rhs = (1 - q**(-d)) / abs(1 - q**(-d / 2 - 1j * t))**2
    print(f"  q={q}, d={d}, t={t}: rel err = {mp.nstr(rel(lhs, rhs), 4)}  "
          f"positive={lhs.real > 0 if hasattr(lhs,'real') else lhs>0}")

print("=== 10. Gamma_C(s) = Gamma_R(s) Gamma_R(s+1) (complex/real Archimedean factors) ===")
def Gamma_R(s):
    return mp.pi**(-s / 2) * mp.gamma(s / 2)

def Gamma_C(s):
    return 2 * (2 * mp.pi)**(-s) * mp.gamma(s)

for s in [mp.mpf('1.3'), mp.mpc(0.8, 0.5), mp.mpf('3.7')]:
    lhs = Gamma_C(s)
    rhs = Gamma_R(s) * Gamma_R(s + 1)
    print(f"  s={s}: rel err = {mp.nstr(rel(lhs, rhs), 4)}")

print("=== 11. Eisenstein scattering coefficient c(Delta) = Lambda(2-Delta)/Lambda(Delta), unit modulus on Delta=1+i*lam ===")
def Lambda(s):
    return mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

for lam in [mp.mpf('1.1'), mp.mpf('4.3'), mp.mpf('9.0')]:
    Delta = 1 + 1j * lam
    c = Lambda(2 - Delta) / Lambda(Delta)
    print(f"  lam={lam}: |c(Delta)|={mp.nstr(abs(c),12)} (target 1), "
          f"rel err from 1 = {mp.nstr(abs(abs(c)-1),4)}")
    # also check Lambda(s) = Lambda(1-s), the functional equation this rests on
    s = Delta - 1  # arbitrary complex point to sanity-check completed zeta functional eqn
    print(f"       Lambda(s)=Lambda(1-s) check at s={s}: "
          f"rel err = {mp.nstr(rel(Lambda(s), Lambda(1 - s)), 4)}")

print("=== 12. Product vs ratio: N_v(s)=A(s)A(1-s) is |A(s)|^2 on Re(s)=1/2, S_v(s)=A(1-s)/A(s) is unit modulus ===")
def A_example(s):
    # any concrete local analytic factor for the sanity check; use A(s) = Gamma(s)
    return mp.gamma(s)

for t in [mp.mpf('0.6'), mp.mpf('2.4')]:
    s = mp.mpf('0.5') + 1j * t
    N = A_example(s) * A_example(1 - s)
    S = A_example(1 - s) / A_example(s)
    target_N = abs(A_example(s))**2
    print(f"  t={t}: N(s) rel err from |A(s)|^2 = {mp.nstr(rel(N, target_N), 4)}, "
          f"|S(s)| = {mp.nstr(abs(S), 10)} (target 1)")

print("=== 13. Sec.9 resolution (2026-08-22): the naive common-local-factor conjecture fails ===")
print("--- Archimedean: C_inf(Delta) = pi^2 * Gamma_C(Delta) * Gamma_C(2-Delta), now in Lean ---")
def GammaR(s):
    return mp.pi**(-s/2) * mp.gamma(s/2)
def GammaC(s):
    return 2*(2*mp.pi)**(-s) * mp.gamma(s)
def C_inf(Delta):
    return mp.gamma(Delta)*mp.gamma(2-Delta)
def c_inf_weyl(s):
    return mp.sqrt(mp.pi)*mp.gamma(s - mp.mpf(1)/2)/mp.gamma(s)
for Delta in [mp.mpc(1,1.3), mp.mpc(0.7,0), mp.mpc(1,4.2)]:
    lhs = C_inf(Delta)
    rhs = mp.pi**2 * GammaC(Delta) * GammaC(2-Delta)
    print(f"  Delta={Delta}: rel err = {mp.nstr(rel(lhs,rhs),4)}")
print("--- two-sector decomposition: C_inf(Delta) = pi^2*GammaR(D)*GammaR(D+1)*GammaR(2-D)*GammaR(3-D), now in Lean ---")
for Delta in [mp.mpc(1,1.3), mp.mpc(1,4.2)]:
    lhs = C_inf(Delta)
    rhs = mp.pi**2 * GammaR(Delta)*GammaR(Delta+1)*GammaR(2-Delta)*GammaR(3-Delta)
    print(f"  Delta={Delta}: rel err = {mp.nstr(rel(lhs,rhs),4)}")
print("--- distinctness: c_inf_weyl(s) (Weyl coeff) vs C_inf(Delta) (physical kernel) are NOT proportional ---")
for s in [mp.mpc(0.5,1.1), mp.mpc(0.5,2.3)]:
    Delta = 2*s
    weyl, cut = c_inf_weyl(s), C_inf(Delta)
    print(f"  s={s}: |c_inf_weyl(s)|={mp.nstr(abs(weyl),8)}  |C_inf(Delta)|={mp.nstr(abs(cut),8)}  "
          f"ratio={mp.nstr(abs(weyl)/abs(cut),8)} (varies -> distinct objects, not forced equal)")
print("--- finite places: Gindikin-Karpelevich (ratio) vs derived positive kernel (product) are NOT equal ---")
def GK(q, z):
    return (1 - z/q) / (1 - z)
def K_q1(q, s):
    return (1 - mp.mpf(1)/q) / ((1-q**(-s))*(1-q**(-(1-s))))
for q, s in [(2, mp.mpf('0.5')), (3, mp.mpf('0.7')), (5, mp.mpf('0.3'))]:
    z = q**(-s)
    gk, kq = GK(q, z**2), K_q1(q, s)
    print(f"  q={q}, s={s}: GK={mp.nstr(gk,8)}  K_q1={mp.nstr(kq,8)}  equal={rel(gk,kq)<mp.mpf('1e-10')} (correctly NOT equal)")
print("--- global: phi(Delta)=Lambda(Delta-1)/Lambda(Delta)=Lambda(2-Delta)/Lambda(Delta), now in Lean via completedRiemannZeta ---")
def Lambda(s):
    return mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)
def phi(Delta):
    return Lambda(Delta-1)/Lambda(Delta)
for lam in [mp.mpf('1.7'), mp.mpf('3.3')]:
    Delta = 1+1j*lam
    print(f"  lam={lam}: phi(2-D)*phi(D)={mp.nstr(phi(2-Delta)*phi(Delta),10)} (target 1, now in Lean), "
          f"|phi(1+i*lam)|={mp.nstr(abs(phi(Delta)),10)} (target 1, numerical only -- needs Lambda's "
          f"conjugation symmetry, not directly in Mathlib -- NOT evidence toward RH)")

print("\nDone. See local_shadow_kernel_notes.md for which of the above are formalized in Lean")
print("(items 2, 3 -> LocalShadowKernel.lean; item 6 -> DiagonalConformalLift.lean; item 13's")
print("Archimedean decomposition -> LocalShadowKernel.lean, global reflection ->")
print("GlobalEisensteinCoefficient.lean) and which are numerical-only research targets (items")
print("1, 4, 5, 7-12, and item 13's finite-place distinctness + unit-modulus check -- none of")
print("these are Lean claims, and 11/12/13's global piece in particular are NOT evidence for")
print("anything about RH).")
