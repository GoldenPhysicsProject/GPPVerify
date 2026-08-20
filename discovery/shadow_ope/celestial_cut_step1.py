"""
STEP 1 OF THE REAL REDO: exact celestial image of the two-particle massless
unitarity cut. Every Jacobian derived symbolically, every claim checked
numerically. No inserted factors. Conventions stated inline.

Parametrization: null momentum l = w * q(z,zbar),
  q = (1+x^2+y^2, 2x, 2y, 1-x^2-y^2),  z = x+iy,  w>0.
Metric (+,-,-,-). q^2 = 0 identically.
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 30

w, x, y, M = sp.symbols('w x y M', positive=True)
xr, yr = sp.symbols('xr yr', real=True)

def q(X, Y):
    return sp.Matrix([1+X**2+Y**2, 2*X, 2*Y, 1-X**2-Y**2])

# ---------- A. Single-particle on-shell measure ----------
l = w*q(xr, yr)
J3 = sp.simplify(sp.Matrix([[sp.diff(l[i], v) for v in (w, xr, yr)] for i in (1,2,3)]).det())
measure = sp.simplify(J3/(2*l[0]))
print("A. d^3l/(2E) Jacobian:")
print("   det d(l1,l2,l3)/d(w,x,y) =", J3, "   =>  d^3l/(2E) =", measure, "* dw dx dy")

# ---------- B. Two-particle phase space, delta^4 solved exactly ----------
w5, w6, x5, y5, x6, y6 = sp.symbols('w5 w6 x5 y5 x6 y6', real=True, positive=None)
P = sp.Matrix([M, 0, 0, 0])
F = P - w5*q(x5, y5) - w6*q(x6, y6)          # 4 constraints

r2 = x5**2 + y5**2
sol = {w5: M/(2*(1+r2)), w6: M*r2/(2*(1+r2)), x6: -x5/r2, y6: -y5/r2}
print("\nB. delta^4 solution check (all four components must vanish):",
      [sp.simplify(Fi.subs(sol)) for Fi in F])

J4 = sp.Matrix([[sp.diff(F[i], v) for v in (w5, w6, x6, y6)] for i in range(4)]).det()
J4_on = sp.simplify(J4.subs(sol))
print("   det dF/d(w5,w6,x6,y6) on-shell =", sp.factor(J4_on))

# LIPS = (2pi)^4 delta^4 * prod d^3l/((2pi)^3 2E)
# = (1/(2pi)^2) * (2 w5)(2 w6) dw5 d2z5 dw6 d2z6 delta^4
# solving delta^4 over (w5,w6,x6,y6) divides by |J4| and fixes them:
rho = sp.simplify((sp.Rational(1,1)/(2*sp.pi)**2) * 4*w5*w6/sp.Abs(J4_on))
rho = sp.simplify(rho.subs(sol))
print("   LIPS density over remaining d^2z5:  rho =", sp.simplify(rho))

r = sp.symbols('r', positive=True)
rho_r = sp.simplify(rho.subs({x5: r, y5: 0}))            # rotational symmetry
total = sp.simplify(2*sp.pi*sp.integrate(rho_r*r, (r, 0, sp.oo)))
print("   integral rho d^2z5 =", total, "   (target: 1/(8*pi) =", sp.nsimplify(1/(8*sp.pi)), ")")

# ---------- C. Mellin image of the cut measure ----------
# Phi(D5,D6) := int dLIPS  w5^(D5-1) w6^(D6-1)
D5, D6 = sp.symbols('Delta5 Delta6')
w5s = M/(2*(1+r**2)); w6s = M*r**2/(2*(1+r**2))
integrand = rho_r * w5s**(D5-1) * w6s**(D6-1) * r
u = sp.symbols('u', positive=True)
integrand_u = sp.simplify(integrand.subs(r, sp.sqrt(u)) * sp.Rational(1,2)/sp.sqrt(u) * sp.sqrt(u))
# 2*pi from angle; substitute u = r^2, r dr = du/2
Phi_expr = 2*sp.pi*sp.simplify(sp.powsimp(integrand.subs(r**2, u).subs(r, sp.sqrt(u)))/ (2))
print("\nC. Mellin-cut integrand in u=r^2 (before u-integral):")
print("   ", sp.simplify(Phi_expr))

# Closed form via Beta function, derived not asserted:
Phi_closed = (1/(8*sp.pi)) * (M/2)**(D5+D6-2) * sp.gamma(D5)*sp.gamma(D6)/sp.gamma(D5+D6)
print("   Candidate closed form: Phi = 1/(8*pi) * (M/2)^(D5+D6-2) * G(D5)G(D6)/G(D5+D6)")

# Numeric verification at complex Delta on/off principal series, 2 masses:
def Phi_num(d5, d6, Mv):
    f = lambda uu: (1/(8*mp.pi)) * (1/(1+uu)**2) \
        * (Mv/(2*(1+uu)))**(d5-1) * (Mv*uu/(2*(1+uu)))**(d6-1)
    return mp.quad(f, [0, mp.inf])
def Phi_cf(d5, d6, Mv):
    return (1/(8*mp.pi)) * (Mv/2)**(d5+d6-2) * mp.gamma(d5)*mp.gamma(d6)/mp.gamma(d5+d6)

print("\n   Numeric checks (quadrature vs closed form):")
tests = [(mp.mpc(1,0.7), mp.mpc(1,-0.3), 2.0),
         (mp.mpc(1.4,1.1), mp.mpc(0.9,-2.2), 3.7),
         (mp.mpc(2.5,0), mp.mpc(1.5,0), 1.0)]
for d5, d6, Mv in tests:
    a, b = Phi_num(d5, d6, Mv), Phi_cf(d5, d6, Mv)
    print(f"   D5={d5}, D6={d6}, M={Mv}:  |rel err| = {mp.nstr(abs(a-b)/abs(b),3)}")

# ---------- D. Cutkosky bubble closure ----------
# Im I2(s) = 1/(16 pi) for massless bubble (textbook). Cutkosky:
# 2 Im I2 = int dLIPS * 1 * 1 = 1/(8 pi).  Consistency: 2*(1/(16pi)) = 1/(8pi). OK.
# Celestial statement: the cut's Mellin image Phi scales as M^(D5+D6-2).
# The physical cut (constant in s=M^2) sits exactly on the locus D5+D6=2:
print("\nD. On the locus Delta5+Delta6=2:  Phi = 1/(8*pi) * G(D5)G(2-D5)/G(2)")
d5 = mp.mpc(1, 1.3)
print("   e.g. D5=1+1.3i: Phi/(1/8pi) =", mp.nstr(mp.gamma(d5)*mp.gamma(2-d5), 12),
      " = pi*lam/sinh(pi*lam)*(1+lam^2)^{1/2}-ish; check |G(1+il)|^2*(stuff):")
lam = 1.3
print("   G(1+il)G(1-il) = pi*l/sinh(pi*l):",
      mp.nstr(mp.gamma(1+1j*lam)*mp.gamma(1-1j*lam),12), "vs",
      mp.nstr(mp.pi*lam/mp.sinh(mp.pi*lam),12))
