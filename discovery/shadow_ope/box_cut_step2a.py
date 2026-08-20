"""
STEP 2a: s-channel cut of the (mu-regulated) box, three independent ways.
  (1) CM angular integral (momentum space, direct)
  (2) Celestial z5-plane integral using Step-1 derived measure/antipode
  (3) Exact closed form via Feynman parameter (derived symbolically here)
All three must agree. Conventions: metric (+,-,-,-), l = w q(z),
q=(1+|z|^2, 2x, 2y, 1-|z|^2), all-incoming box with legs k1..k4,
propagators l^2, (l-k1)^2, (l-k1-k2)^2, (l-k1-k2-k3)^2.
s-cut: l^2 and (l-k1-k2)^2 on shell. Uncut lines get mass mu (regulator),
cut lines stay massless -> Step-1 phase space applies verbatim.
Cut integral (normalization = pure dLIPS, Cutkosky 2*pi*i bookkeeping
deferred to the dispersion step, stated openly):
  C(s,t,mu^2) = int dLIPS  1/[((l5-k1)^2-mu^2)((l5+k4)^2-mu^2)]
"""
import mpmath as mp
import sympy as sp
mp.mp.dps = 25

# ---------------- kinematics builder ----------------
def kin(Mv, ct_star):
    E = Mv/2; st_star = mp.sqrt(1-ct_star**2)
    p1 = [E,0,0,E]; p2 = [E,0,0,-E]                      # incoming
    p3 = [E, E*st_star, 0, E*ct_star]                    # outgoing
    p4 = [E,-E*st_star, 0,-E*ct_star]                    # outgoing
    dot = lambda a,b: a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3]
    s = dot([p1[i]+p2[i] for i in range(4)],[p1[i]+p2[i] for i in range(4)])
    t = dot([p1[i]-p3[i] for i in range(4)],[p1[i]-p3[i] for i in range(4)])
    u = dot([p1[i]-p4[i] for i in range(4)],[p1[i]-p4[i] for i in range(4)])
    return p1,p2,p3,p4,s,t,u,dot

# ---------------- (1) CM angular integral ----------------
def C_CM(Mv, ct_star, mu2):
    p1,p2,p3,p4,s,t,u,dot = kin(Mv, ct_star)
    E = Mv/2
    def integrand(ct, ph):
        stq = mp.sqrt(1-ct**2)
        l5 = [E, E*stq*mp.cos(ph), E*stq*mp.sin(ph), E*ct]
        A = -2*dot(l5,p1) - mu2            # (l5-k1)^2 - mu^2, k1=p1
        B = -2*dot(l5,p4) - mu2            # (l5+k4)^2 - mu^2, k4=-p4
        return 1/(A*B)
    val = mp.quad(lambda ct: mp.quad(lambda ph: integrand(ct,ph),[0,2*mp.pi]),
                  [-1,1])
    return val/(32*mp.pi**2)

# ---------------- (2) celestial z5-plane integral ----------------
def C_celestial(Mv, ct_star, mu2):
    p1,p2,p3,p4,s,t,u,dot = kin(Mv, ct_star)
    def qvec(x,y):
        return [1+x*x+y*y, 2*x, 2*y, 1-x*x-y*y]
    def integrand(r, ph):
        x, y = r*mp.cos(ph), r*mp.sin(ph); uu = r*r
        w5 = Mv/(2*(1+uu))
        l5 = [w5*c for c in qvec(x,y)]
        A = -2*dot(l5,p1) - mu2
        B = -2*dot(l5,p4) - mu2
        return (1/(A*B)) * r/(8*mp.pi**2*(1+uu)**2)
    val = mp.quad(lambda r: mp.quad(lambda ph: integrand(r,ph),[0,2*mp.pi]),
                  [0, 1, 10, mp.inf])
    return val

# ---------------- (3) exact closed form (symbolic derivation) ----------------
xs, cs, ds = sp.symbols('x c d', positive=True)
I = sp.integrate(1/(cs + ds*xs*(1-xs)), (xs, 0, 1))
I_simpl = sp.simplify(I)
print("Symbolic Feynman-parameter integral  int_0^1 dx/(c+d x(1-x)) =")
print("   ", I_simpl)
# expected equivalent: 4/sqrt(d(d+4c)) * atanh(sqrt(d/(d+4c)))
f_closed = sp.lambdify((cs, ds), I_simpl, modules='mpmath')

def C_exact(Mv, ct_star, mu2):
    p1,p2,p3,p4,s,t,u,dot = kin(Mv, ct_star)
    # Derived in-session: xD_A+(1-x)D_B = -(a - b.n), a=s/2+mu2,
    # a^2-|b|^2 = mu2(s+mu2) + s(s+t) x(1-x)  [with t=(p1-p3)^2 from vectors]
    c = mu2*(s+mu2); d = s*(s+t)
    return f_closed(c, d)/(8*mp.pi)

# ---------------- run the three-way check ----------------
print("\nThree-way verification of the box s-cut  C(s,t,mu^2):")
print("-"*74)
cases = [(2.0, -0.3, 0.5), (mp.sqrt(10), 0.5, 0.2), (2.0, 0.7, 0.05), (3.0, -0.8, 1.0)]
for Mv, ctst, mu2 in cases:
    Mv, ctst, mu2 = mp.mpf(Mv), mp.mpf(ctst), mp.mpf(mu2)
    p1,p2,p3,p4,s,t,u,dot = kin(Mv, ctst)
    a = C_CM(Mv, ctst, mu2); b = C_celestial(Mv, ctst, mu2); e = C_exact(Mv, ctst, mu2)
    print(f" s={mp.nstr(s,6)}, t={mp.nstr(t,6)}, u={mp.nstr(u,6)}, mu2={mp.nstr(mu2,4)}")
    print(f"   CM        = {mp.nstr(a, 18)}")
    print(f"   celestial = {mp.nstr(b, 18)}")
    print(f"   exact     = {mp.nstr(e, 18)}")
    print(f"   |CM-exact|/exact = {mp.nstr(abs(a-e)/abs(e),3)},  "
          f"|cel-exact|/exact = {mp.nstr(abs(b-e)/abs(e),3)}")

# ---------------- structure checks ----------------
print("\nStructure checks:")
# q(z).q(w) = 2|z-w|^2
import random
random.seed(7)
def qv(z):
    x,y = mp.re(z), mp.im(z)
    return [1+x*x+y*y, 2*x, 2*y, 1-x*x-y*y]
dotf = lambda a,b: a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3]
z, w = mp.mpc(0.3,-1.2), mp.mpc(-2.1,0.4)
print("  q(z).q(w) - 2|z-w|^2 =", mp.nstr(dotf(qv(z),qv(w)) - 2*abs(z-w)**2, 5))
# collinear log at small mu: C -> log(s(s+t)/(mu^2(s+mu^2)))/(4 pi s(s+t))
Mv, ctst = mp.mpf(2), mp.mpf('-0.3')
p1,p2,p3,p4,s,t,u,dot = kin(Mv,ctst)
for mu2 in [mp.mpf('1e-3'), mp.mpf('1e-5')]:
    exact = C_exact(Mv,ctst,mu2)
    approx = mp.log(s*(s+t)/(mu2*(s+mu2)))/(4*mp.pi*s*(s+t))
    print(f"  mu2={mp.nstr(mu2,2)}: exact={mp.nstr(exact,10)} "
          f" leading-log={mp.nstr(approx,10)}  ratio={mp.nstr(exact/approx,8)}")
print("\nCelestial integrand in closed z-form (z1=0 for p1; K1 source object):")
print("  C = int d^2z/(8 pi^2 (1+|z|^2)^2) * 1/[(M^2|z|^2/(1+|z|^2)+mu^2)")
print("        * (4 w5 w4 |z-z4|^2 + mu^2)],  w5=M/(2(1+|z|^2)),")
print("  z4 = -cot(theta*/2), w4 = (M/2) sin^2(theta*/2)   [p4 leg]")
