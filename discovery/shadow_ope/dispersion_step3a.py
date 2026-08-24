"""
STEP 3a: reconstruct the full box from its cut. ZERO free parameters.
Box: I4 = (i/16pi^2) J,  J(s,u) = int_simplex [dx] / Delta^2,
  Delta = mu^2(x2+x4) - s x1 x3 - u x2 x4    (>0 for s,u<0: Euclidean).
Cutkosky (derived, bubble-anchored): Im J(s',u) = 8 pi^2 C(s',u,mu^2).
Unsubtracted fixed-u dispersion (only the s-cut exists for u < 4mu^2... u<0):
  J(s,u) = (1/pi) int_0^inf ds' Im J / (s'-s) = 8 pi int_0^inf ds' C(s',u)/(s'+|s|).
Verify J_direct == J_disp at multiple Euclidean points. Then the Mellin form:
  M_J(sigma) = (8 pi^2 / sin(pi sigma)) M_C(sigma),  0 < Re sigma < 1
(the celestial dispersion relation: loop Mellin amplitude = cut Mellin
amplitude times the universal Stieltjes kernel).
"""
import mpmath as mp
mp.mp.dps = 20

# ---- exact inner kernel G(c,d) = int_0^1 dy/(c+d y(1-y))^2  (hand-derived) ----
def G(c, d):
    if d < mp.mpf('1e-25')*c:
        return 1/c**2
    w = d + 4*c
    return 8*mp.atanh(mp.sqrt(d/w))/(mp.sqrt(d)*w**mp.mpf(1.5)) + 2/(c*w)

# cross-check G against direct quadrature
c0, d0 = mp.mpf('0.37'), mp.mpf('2.9')
g_num = mp.quad(lambda y: 1/(c0+d0*y*(1-y))**2, [0, 0.5, 1])
print("G(c,d) closed form vs quad: rel err =", mp.nstr(abs(G(c0,d0)-g_num)/g_num, 3))

# ---- direct box (Euclidean s,u<0): reduce x1,x3 -> exact y-integral ----
def J_direct(s, u, mu2):
    S, U = -s, -u          # positive
    def inner(x2, x4):
        rho = 1 - x2 - x4
        if rho <= 0: return mp.mpf(0)
        c = mu2*(x2+x4) + U*x2*x4
        d = S*rho**2
        return rho * G(c, d)
    # x4 = (1-x2)*v, jacobian (1-x2)
    f = lambda x2, v: (1-x2) * inner(x2, (1-x2)*v)
    return mp.quad(lambda x2: mp.quad(lambda v: f(x2, v), [0, 0.5, 1]),
                   [0, 0.01, 0.5, 0.99, 1])

# ---- cut (closed form from Step 2a), at fixed u: d' = -s'u = s'|u| ----
def C_cut(sp, u, mu2):
    c = mu2*(sp+mu2); d = sp*(-u)
    w = d + 4*c
    return (1/(8*mp.pi))*(4/mp.sqrt(d*w))*mp.atanh(mp.sqrt(d/w))

def J_disp(s, u, mu2):
    S = -s
    return 8*mp.pi*mp.quad(lambda sp: C_cut(sp,u,mu2)/(sp+S),
                           [0, mu2, 1, 10, 100, 1000, mp.inf])

print("\nLoop reconstruction from its cut (no fitted constants):")
print("-"*66)
pts = [(-3.0,-2.0,0.5), (-1.0,-5.0,0.2), (-10.0,-1.0,1.0), (-0.3,-0.7,0.05)]
for s,u,m2 in pts:
    s,u,m2 = mp.mpf(s), mp.mpf(u), mp.mpf(m2)
    jd = J_direct(s,u,m2); jp = J_disp(s,u,m2)
    print(f" s={float(s)}, u={float(u)}, mu2={float(m2)}:")
    print(f"   J_direct = {mp.nstr(jd,14)}   J_disp = {mp.nstr(jp,14)}"
          f"   rel err = {mp.nstr(abs(jd-jp)/jd,3)}")

# ---- Mellin-space (celestial) dispersion relation ----
print("\nCelestial dispersion:  M_J(sigma) = (8 pi^2/sin(pi sigma)) M_C(sigma)")
u, m2 = mp.mpf(-2), mp.mpf('0.5')
def M_C(sigma):
    return mp.quad(lambda sp: sp**(sigma-1)*C_cut(sp,u,m2),
                   [0, m2, 1, 10, 100, mp.inf])
def M_J(sigma):
    return mp.quad(lambda S: S**(sigma-1)*J_disp(-S,u,m2),
                   [0, m2, 1, 10, 100, mp.inf])
for sigma in [mp.mpf('0.5'), mp.mpc('0.4','1.1')]:
    lhs = M_J(sigma)
    rhs = 8*mp.pi**2/mp.sin(mp.pi*sigma)*M_C(sigma)
    print(f"  sigma={sigma}:  rel err = {mp.nstr(abs(lhs-rhs)/abs(lhs),3)}")
