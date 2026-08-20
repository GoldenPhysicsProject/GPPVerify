from mpmath import mp, mpf, mpc, pi, sinh, cosh, tanh, sech, exp, quad, inf, diff, psi, gamma, zeta, log, mpmathify
mp.dps=30
P   = lambda l: pi*l/sinh(pi*l)
phat= lambda x: 1/(4*cosh(x/2)**2)

print("=== 1. Is phat the Fourier transform of P? (already known, recheck) ===")
for x in [mpf('0.6'), mpf('2.4')]:
    lhs=quad(lambda l: P(l)*mp.cos(l*x), [-inf,0,inf])/(2*pi)
    print(f"   x={x}: FT={mp.nstr(lhs,20)}  phat={mp.nstr(phat(x),20)}  rel={mp.nstr(abs(lhs-phat(x))/phat(x),3)}")

print("=== 2. CONJECTURED ODE:  (1/2) sinh(x) phat'(x) = phat(x) - phat(0) ===")
for x in [mpf('0.3'), mpf('1.1'), mpf('2.7'), mpf('5.0')]:
    lhs=sinh(x)*diff(phat,x)/2
    rhs=phat(x)-phat(0)
    print(f"   x={x}: lhs={mp.nstr(lhs,20)}  rhs={mp.nstr(rhs,20)}  absdiff={mp.nstr(abs(lhs-rhs),5)}")

print("=== 3. Therefore integrand is an exact total derivative: [phat(0)-phat(x)]/sinh x = -(1/2) phat'(x) ===")
for x in [mpf('0.8'), mpf('3.3')]:
    lhs=(phat(0)-phat(x))/sinh(x); rhs=-diff(phat,x)/2
    print(f"   x={x}: rel={mp.nstr(abs(lhs-rhs)/abs(rhs),5)}")
val=quad(lambda x: (phat(0)-phat(x))/sinh(x), [0,inf])
print(f"   integral = {mp.nstr(val,25)}   (1/2)phat(0) = {mp.nstr(phat(0)/2,25)}   M1 = 0.125")

print("=== 4. Does the ODE come from the Gamma shift relations? P(lam-i) = (1+i lam)/(-i lam) P(lam) ===")
Pc = lambda l: gamma(1+1j*l)*gamma(1-1j*l)
for l in [mpc('0.7','0'), mpc('2.1','0')]:
    lhs=Pc(l-1j); rhs=(1+1j*l)/(-1j*l)*Pc(l)
    print(f"   lam={l.real}: rel={mp.nstr(abs(lhs-rhs)/abs(rhs),5)}")
print("   second-order combination: -i(l-i)P(l-i) + i(l+i)P(l+i) =? 4 P(l)")
for l in [mpf('0.7'), mpf('2.1'), mpf('4.4')]:
    comb=-1j*(l-1j)*Pc(l-1j)+1j*(l+1j)*Pc(l+1j)
    print(f"   lam={l}: comb={mp.nstr(comb,18)}  4P={mp.nstr(4*P(l),18)}  rel={mp.nstr(abs(comb-4*P(l))/(4*P(l)),4)}")

print("=== 5. Uniqueness: solve ODE (1/2)sinh(x) f' = f - c, f(inf)=0  =>  f = c*sech^2(x/2)? ===")
c=mpf(1)/4
f=lambda x: c-c*tanh(x/2)**2
for x in [mpf('0.9'), mpf('2.2')]:
    print(f"   x={x}: solution={mp.nstr(f(x),18)}  phat={mp.nstr(phat(x),18)}  rel={mp.nstr(abs(f(x)-phat(x))/phat(x),4)}")

print("=== 6. phat = -n_F'(x), derivative of Fermi-Dirac at unit temperature? ===")
nF=lambda x: 1/(exp(x)+1)
for x in [mpf('0.5'), mpf('2.0')]:
    print(f"   x={x}: -nF'={mp.nstr(-diff(nF,x),18)}  phat={mp.nstr(phat(x),18)}")

print("=== 7. Higher deviation moments A_k = (1/2pi) int_R P(lam) D(lam)^k dlam ===")
D=lambda l: psi(0,mpc('0.5',0)+1j*l/2).real - psi(0,mpf('0.5'))
for k in [0,1,2,3]:
    Ak=quad(lambda l: P(l)*D(l)**k, [-inf,0,inf])/(2*pi)
    print(f"   A_{k} = {mp.nstr(Ak,20)}")
from mpmath import mp, mpf, mpc, pi, sinh, cosh, quad, inf, psi, zeta, log, identify, exp, diff
mp.dps=40
P=lambda l: pi*l/sinh(pi*l)
D=lambda l: psi(0,mpc('0.5',0)+1j*l/2).real - psi(0,mpf('0.5'))
print("high-precision deviation moments A_k = (1/2pi) int_R P D^k dlam")
A=[]
for k in range(5):
    v=quad(lambda l: P(l)*D(l)**k, [-inf,0,inf], maxdegree=10)/(2*pi)
    A.append(v); print(f"  A_{k} = {mp.nstr(v,30)}")
print()
print("A_2 - 1/8 =", mp.nstr(A[2]-mpf(1)/8,10))
print("identify A_3:", identify(A[3], ['zeta(3)','pi**2','log(2)','zeta(3)/pi**2']))
print("A_3 - 1/8 =", mp.nstr(A[3]-mpf(1)/8,20), " identify:", identify(A[3]-mpf(1)/8,['zeta(3)/pi**2','zeta(3)','log(2)']))
print("7*zeta(3)/(2*pi**2)*? test:", mp.nstr(7*zeta(3)/(2*pi**2),20))
print("A_4:", mp.nstr(A[4],25))
from mpmath import mp, mpf, mpc, pi, sinh, quad, inf, psi, zeta, log, identify, gamma
mp.dps=40
Dc=lambda l: (psi(0,mpc('0.5',0)+1j*l/2)+psi(0,mpc('0.5',0)-1j*l/2))/2 - psi(0,mpf('0.5'))
print("=== check my derived shift identities for D ===")
for l in [mpf('0.9'), mpf('2.3')]:
    d1=Dc(l-1j)-Dc(l+1j); print(f"  D(l-i)-D(l+i) = {mp.nstr(d1,15)}   -2i/l = {mp.nstr(-2j/l,15)}")
    d2=Dc(l-1j)+Dc(l+1j); tgt=2*((psi(0,1j*l/2)+psi(0,-1j*l/2))/2 - psi(0,mpf('0.5')))
    print(f"  D(l-i)+D(l+i) = {mp.nstr(d2,15)}   2[Re psi(i l/2)-psi(1/2)] = {mp.nstr(tgt,15)}")
print("=== identify A_4 ===")
P=lambda l: pi*l/sinh(pi*l)
D=lambda l: psi(0,mpc('0.5',0)+1j*l/2).real - psi(0,mpf('0.5'))
A4=quad(lambda l: P(l)*D(l)**4, [-inf,0,inf], maxdegree=12)/(2*pi)
print("  A_4 =", mp.nstr(A4,30))
for basis in (['log(2)','zeta(3)'],['log(2)','zeta(3)','log(2)**2'],['log(2)','zeta(3)/pi**2','pi**2']):
    print("   basis",basis,"->",identify(A4,basis))
print("=== normalized law of D under 4P dlam/2pi ===")
A=[quad(lambda l: P(l)*D(l)**k,[-inf,0,inf],maxdegree=10)/(2*pi) for k in range(3)]
print(f"  mean={mp.nstr(A[1]/A[0],20)}  E[D^2]={mp.nstr(A[2]/A[0],20)}  var={mp.nstr(A[2]/A[0]-(A[1]/A[0])**2,20)}")
from mpmath import mp, mpf, pi, sinh, cosh, tanh, sech, quad, inf, log, psi, mpc, exp
mp.dps=30
phat=lambda x: 1/(4*cosh(x/2)**2)
# CLOSED FORM DERIVED BY HAND for f1 = -Lp (generator of Levy process, Levy density 1/(2 sinh|x|))
def f1_closed(x):
    c=tanh(x/2)**2
    if c<mpf('1e-20'): return mpf(1)/8
    return (1-c)/8*(2+(1+c)*log(1-c)/c)
def f1_num(x):   # f1(x) = int_0^inf [2 phat(x) - phat(x+y) - phat(x-y)]/(2 sinh y) dy
    return quad(lambda y: (2*phat(x)-phat(x+y)-phat(x-y))/(2*sinh(y)), [0,inf])
print("1. closed form for f_1 (NEW):  f1(x) = (1-c)/8 * [2 + (1+c)ln(1-c)/c],  c=tanh^2(x/2)")
for x in [mpf('0.4'), mpf('1.3'), mpf('3.0'), mpf('6.0')]:
    a,b=f1_closed(x),f1_num(x)
    print(f"   x={x}: closed={mp.nstr(a,18)}  direct={mp.nstr(b,18)}  rel={mp.nstr(abs(a-b)/abs(b),4)}")
print(f"   f1(0)={mp.nstr(f1_closed(mpf('1e-30')),18)}  = A_1 = 1/8")
print()
print("2. A_2 by my reduced integral:  A_2 = (1/16) int_0^1 [-1+2c-(1-c^2)ln(1-c)/c] dc/c   [should be 2/16]")
I=quad(lambda c: (-1+2*c-(1-c**2)*log(1-c)/c)/c, [0,1])
print(f"   inner integral = {mp.nstr(I,20)}   (hand-computed series value: 2)")
print(f"   A_2 = {mp.nstr(I/16,20)}   vs 1/8")
print()
print("3. A_2 by the earlier double-integral route: (1/16) int int [(u+v)(uv-3)+4]/(1-uv)^2 du dv = 2 ?")
J=quad(lambda u: quad(lambda v: ((u+v)*(u*v-3)+4)/(1-u*v)**2, [0,1]), [0,1])
print(f"   = {mp.nstr(J,20)}    A_2 = {mp.nstr(J/16,20)}")
print()
print("4. A_3 reduced to a DOUBLE integral of elementary functions using b = f1(0)-f1:")
b=lambda x: mpf(1)/8 - f1_closed(abs(x))
A3=mpf(0)
print("   (A_3 check deferred)")
from mpmath import mp, mpf, quad, log, tanh, sinh, cosh
mp.dps=15
# clean series form of route-2 integrand (cancellation removed by hand)
g=lambda c: mpf(5)/2 + (-log(1-c)-c-c**2/2)/c**2 + log(1-c)
orig=lambda c: (-1+2*c-(1-c**2)*log(1-c)/c)/c
print("route-2 integrand, hand-simplified vs original:")
for c in [mpf('0.01'),mpf('0.3'),mpf('0.9')]:
    print(f"   c={c}: clean={mp.nstr(g(c),12)} orig={mp.nstr(orig(c),12)}")
print("   int_0^1 clean =", mp.nstr(quad(g,[0,1]),15), "  (hand series: 5/2 + 1/2 - 1 = 2)")
# KEY IDENTITY enabling the next step: 1 - tanh^2((x+y)/2) = (1-p^2)(1-q^2)/(1+pq)^2
p,q=mpf('0.31'),mpf('0.57')
lhs=1-((p+q)/(1+p*q))**2; rhs=(1-p**2)*(1-q**2)/(1+p*q)**2
print(f"log-splitting identity: lhs={mp.nstr(lhs,15)} rhs={mp.nstr(rhs,15)}")
# A_3 as 2D integral over phi,psi in (0,1) with measure dphi dpsi/(phi psi), b = f1(0)-f1
def f1c(c):
    if c<mpf('1e-12'): return mpf(1)/8
    if c>1-mpf('1e-12'): c=1-mpf('1e-12')
    return (1-c)/8*(2+(1+c)*log(1-c)/c)
b=lambda t: mpf(1)/8-f1c(t*t)     # t = tanh(arg/2), even in t
def add(p,q): return (p+q)/(1+p*q)
def sub(p,q): return (p-q)/(1-p*q) if abs(1-p*q)>1e-30 else mpf(1)
F=lambda p,q: b(p)+b(q)-(b(add(p,q))+b(abs(sub(p,q))))/2
A3=quad(lambda p: quad(lambda q: F(p,q)/(p*q), [0,p,1], maxdegree=5), [0,1], maxdegree=5)
print("A_3 (2D reduction) =", mp.nstr(A3,12), "   target (1/2)ln2-3/16 =", mp.nstr(log(2)/2-mpf(3)/16,12))
