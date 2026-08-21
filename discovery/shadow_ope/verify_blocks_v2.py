from mpmath import mp, mpf, mpc, gamma, sinh, pi, quad, exp, cosh, hyp2f1, legenq, legenp, psi, zeta, tanh, inf, zetazero, mpmathify, im, re
mp.dps=40
print("=== D-retry: conical reduction with Legendre type=3 (argument x>1) ===")
for (h,z) in [(mpc('0.5','0.7'), mpf('0.3')), (mpc('0.5','1.4'), mpf('0.15')), (mpf('0.8'), mpf('0.25')), (mpc('0.5','2.3'), mpf('0.42'))]:
    lhs=z**h*hyp2f1(h,h,2*h,z)
    x=2/z-1
    for t in (2,3):
        rhs=(2*gamma(2*h)/gamma(h)**2)*legenq(h-1,0,x,type=t)
        print(f"  h={h}, z={z}, type={t}: rel={abs(lhs-rhs)/abs(rhs)}")

print("=== H-retry: half-line convention M1 = (1/2pi) int_0^inf P dlam ===")
M1=quad(lambda l: pi*l/sinh(pi*l), [0,inf])/(2*pi)
print("  M1 =", M1, "  vs 1/8 =", mpf(1)/8, " rel=", abs(M1-mpf(1)/8)/(mpf(1)/8))

print("=== I. Mellin bridge vanishing at first zeta zeros (claimed 29 digits) ===")
def bridge(s):
    return (1-2**(-s))*gamma(s)*zeta(s)
for k in [1,2,3]:
    rho=zetazero(k)
    print(f"  rho_{k}={mp.nstr(rho,15)}  |bridge(rho)| = {mp.nstr(abs(bridge(rho)),5)}")

print("=== J. temperedness envelope: |k_h| ~ e^{-pi lambda} decay? spot check ===")
for lam in [mpf('1'), mpf('3'), mpf('6')]:
    h=mpc('0.5',0)+1j*lam/2
    z=mpf('0.4')
    val=abs(z**h*hyp2f1(h,h,2*h,z))
    print(f"  lam={lam}: |k_h(0.4)|={mp.nstr(val,8)}   e^{{-pi lam/2}}={mp.nstr(exp(-pi*lam/2),8)}  ratio={mp.nstr(val/exp(-pi*lam/2),8)}")

print("=== K. M2 = 1/90? two-fold iterated moment candidates ===")
# candidate: (1/2pi)^2 double integral of P(l1)P(l2)P(l1-l2)? or product form
A=quad(lambda l: (pi*l/sinh(pi*l))**2, [0,inf])/(2*pi)
print("  (1/2pi)int_0^inf P^2 =", mp.nstr(A,20), " 1/90=", mp.nstr(mpf(1)/90,20))
from mpmath import mp, mpf, mpc, gamma, pi, hyp2f1, exp, sqrt, coth, sinh, cosh, quad, psi, inf, mp as MP
mp.dps=30
print("=== Prefactor modulus: |c|^2 = (2 lam/pi) coth(pi lam/2), c=2Gamma(2h)/Gamma(h)^2, h=(1+i lam)/2 ===")
for lam in [mpf('0.5'), mpf('2'), mpf('7')]:
    h=(1+1j*lam)/2; c=2*gamma(2*h)/gamma(h)**2
    lhs=abs(c)**2; rhs=(2*lam/pi)*coth(pi*lam/2)
    print(f"  lam={lam}: rel={abs(lhs-rhs)/rhs}")

print("=== Temperedness: |g_{1+i lam}(z,zbar)| -> |1-z|^{-1/2} on |z|=1 ===")
def k(h,z): return z**h*hyp2f1(h,h,2*h,z)
for phi in [mpf('1.0'), mpf('2.2')]:
    z=mpf('0.999')*exp(1j*phi); zb=mpf('0.999')*exp(-1j*phi)
    tgt=abs(1-z)**mpf('-0.5')
    print(f"  phi={phi}, target |1-z|^-1/2 = {mp.nstr(tgt,10)}")
    for lam in [mpf('4'), mpf('12'), mpf('30')]:
        h=(1+1j*lam)/2
        g=abs(k(h,z)*k(h,zb))
        print(f"     lam={lam}: |g|={mp.nstr(g,10)}  ratio={mp.nstr(g/tgt,10)}")

print("=== Coincidence check: does 1/8 in the digamma moment equal M1 structurally? ===")
P=lambda l: pi*l/sinh(pi*l)
full=quad(lambda l: P(l)*psi(0,mpc('0.5',0)+1j*l/2).real, [-inf,0,inf])/(2*pi)
psi_half=psi(0,mpf('0.5'))
constpart=quad(lambda l: P(l), [-inf,0,inf])/(2*pi)*psi_half
deviation=full-constpart
print(f"  full-line moment       = {mp.nstr(full,20)}")
print(f"  (1/2pi)int_R P * psi(1/2) = {mp.nstr(constpart,20)}  [= (1/4)psi(1/2)]")
print(f"  deviation piece        = {mp.nstr(deviation,20)}   vs 1/8 = 0.125")
print(f"  M1 (half-line)         = {mp.nstr(quad(P,[0,inf])/(2*pi),20)}")
print("  => the two '1/8's use DIFFERENT integration conventions (full vs half line).")
from mpmath import mp, mpf, pi, sinh, cosh, tanh, sech, quad, inf, exp, psi, mpc
mp.dps=30
P=lambda l: pi*l/sinh(pi*l)
print("Step 1: Fourier inversion (1/2pi)int_R P cos(lam t/2) dlam = 1/(4 cosh^2(t/4))")
for t in [mpf('0.7'), mpf('3.0')]:
    lhs=quad(lambda l: P(l)*mp.cos(l*t/2), [-inf,0,inf])/(2*pi); rhs=1/(4*cosh(t/4)**2)
    print(f"  t={t}: rel={abs(lhs-rhs)/rhs}")
print("Step 2: moment = int_0^inf dt [1/(2 sinh(t/2))] * (1/4)[1 - sech^2(t/4)]")
m2=quad(lambda t: (1/(2*sinh(t/2)))*(1-sech(t/4)**2)/4, [0,inf])
print(f"  = {mp.nstr(m2,25)}")
print("Step 3: substitution u=t/4 gives (1/4) int_0^inf tanh u sech^2 u du = (1/4)(1/2) = 1/8")
m3=quad(lambda u: tanh(u)*sech(u)**2, [0,inf])/4
print(f"  = {mp.nstr(m3,25)}   [exact 1/8 = 0.125]")
print("Cross-check vs direct digamma moment:")
direct=quad(lambda l: P(l)*psi(0,mpc('0.5',0)+1j*l/2).real, [-inf,0,inf])/(2*pi) - psi(0,mpf('0.5'))/4
print(f"  {mp.nstr(direct,25)}")
from mpmath import mp, mpf, pi, sinh, quad, inf
mp.dps=25
P=lambda l: pi*l/sinh(pi*l) if l>0 else mpf(1)
print("M2 = (1/(2pi)^2) int_0^inf int_0^inf P(l1)P(l2)P(|l1-l2|) dl1 dl2  =? 1/90")
f=lambda a,b: P(a)*P(b)*P(abs(a-b))
M2=quad(lambda a: quad(lambda b: f(a,b), [0,a,inf]), [0,inf])/(2*pi)**2
print("  numeric M2 =", mp.nstr(M2,18), "   1/90 =", mp.nstr(mpf(1)/90,18), "  rel=", mp.nstr(abs(M2-mpf(1)/90)/(mpf(1)/90),5))
print("  zeta(4)/pi^4 =", mp.nstr(mpf(1)/90,18))
from mpmath import mp, mpf, mpc, pi, sinh, quad, inf, gamma, zeta, exp, cosh, sech, nprod, mpmathify, limit
mp.dps=30
P=lambda l: pi*l/sinh(pi*l)
print("=== Stefan-Boltzmann family: m_s = (1/2pi)int_0^inf lam^{s-1} P dlam =? pi^{-(s+1)}(1-2^{-(s+1)})Gamma(s+1)zeta(s+1) ===")
for s in [mpf('1'), mpf('2'), mpf('3'), mpf('0.7'), mpf('4.5')]:
    lhs=quad(lambda l: l**(s-1)*P(l), [0,inf])/(2*pi)
    rhs=pi**(-(s+1))*(1-2**(-(s+1)))*gamma(s+1)*zeta(s+1)
    print(f"  s={s}: lhs={mp.nstr(lhs,18)} rhs={mp.nstr(rhs,18)} rel={mp.nstr(abs(lhs-rhs)/abs(rhs),4)}")
print("  special values: m_1 =", mp.nstr(quad(lambda l: P(l),[0,inf])/(2*pi),18), " (claim 1/8)")
m3=quad(lambda l: l**2*P(l), [0,inf])/(2*pi)
print("  m_3 =", mp.nstr(m3,18), " (claim 1/16 =", mp.nstr(mpf(1)/16,18),")")
print("=== Weierstrass product: 1/P = prod (1+lam^2/n^2) ===")
for lam in [mpf('0.8'), mpf('2.5')]:
    prod=nprod(lambda n: 1+lam**2/n**2, [1, inf])
    print(f"  lam={lam}: prod={mp.nstr(prod,15)}  1/P={mp.nstr(1/P(lam),15)}  rel={mp.nstr(abs(prod-1/P(lam))/(1/P(lam)),4)}")
print("=== Matsubara residues: Res_{lam=i n} P = i(-1)^n n ===")
for n in [1,2,3]:
    eps=mpf("1e-12"); r=(pi*(mpc(0,n)+eps)/sinh(pi*(mpc(0,n)+eps)))*eps
    print(f"  n={n}: residue={mp.nstr(r,12)}   claim i(-1)^n n = {mp.nstr(mpc(0,1)*(-1)**n*n,12)}")
print("=== Fourier transform of P: hat P(k) = (pi/2) sech^2(k/2)? ===")
for k in [mpf('0.6'), mpf('2.0')]:
    lhs=quad(lambda l: P(l)*mp.cos(l*k), [0,inf])*2
    rhs=(pi/2)*sech(k/2)**2
    print(f"  k={k}: int_R P e^{{-ikl}}dl={mp.nstr(lhs,15)}  (pi/2)sech^2(k/2)={mp.nstr(rhs,15)}  rel={mp.nstr(abs(lhs-rhs)/rhs,4)}")
