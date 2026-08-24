"""
STEP 2c FINAL: Mellin image of the box s-cut, poles extracted rigorously.
Exact tail (hand-derived, verified numerically below):
  T(sigma) = (1/(4 pi kappa)) * s0^(sigma-2) * [ (L+ln s0)/(2-sigma) + 1/(2-sigma)^2 ]
  with L = log(kappa/mu^2).
Laurent at sigma = 2-eps:
  T = (1/(4 pi kappa)) [ 1/eps^2 + L/eps + (ln^2 s0/2 - (L+ln s0) ln s0) + O(eps) ]
=> DOUBLE pole coeff 1/(4 pi kappa)   [universal, mu-independent]
   SIMPLE pole coeff L/(4 pi kappa)   [carries the collinear log; s0 cancels]
"""
import mpmath as mp
mp.mp.dps = 25

def C_of_s(s, kappa, mu2):
    c = mu2*(s+mu2); d = s*s*kappa
    x = mp.sqrt(d/(d+4*c))
    return (1/(8*mp.pi))*(4/mp.sqrt(d*(d+4*c)))*mp.atanh(x)

def Casy(s, kappa, mu2):
    return (mp.log(s) + mp.log(kappa/mu2))/(4*mp.pi*kappa*s*s)

def T_exact(sigma, s0, kappa, mu2):
    L = mp.log(kappa/mu2)
    return (1/(4*mp.pi*kappa)) * s0**(sigma-2) * ((L+mp.log(s0))/(2-sigma) + 1/(2-sigma)**2)

def M_direct(sigma, kappa, mu2):
    return mp.quad(lambda s: s**(sigma-1)*C_of_s(s,kappa,mu2),
                   [0, mu2, 1, 10, 100, 1000, mp.inf])

def M_cont(sigma, kappa, mu2, s0=50):
    A = mp.quad(lambda s: s**(sigma-1)*C_of_s(s,kappa,mu2), [0, mu2, 1, 10, s0])
    B = mp.quad(lambda s: s**(sigma-1)*(C_of_s(s,kappa,mu2)-Casy(s,kappa,mu2)),
                [s0, 10*s0, 100*s0, mp.inf])
    return A + B + T_exact(sigma, s0, kappa, mu2)

kappa, mu2 = mp.mpf('0.35'), mp.mpf('0.5')

print("0. Verify hand-derived tail vs direct quadrature (sigma=1.5):")
sig = mp.mpf('1.5'); s0 = mp.mpf(50); L = mp.log(kappa/mu2)
t_num = mp.quad(lambda s: s**(sig-3)*(mp.log(s)+L), [s0, 10*s0, 100*s0, mp.inf])/(4*mp.pi*kappa)
t_ex  = T_exact(sig, s0, kappa, mu2)
print(f"   |T_num - T_exact|/|T| = {mp.nstr(abs(t_num-t_ex)/abs(t_ex),3)}")

print("\n1. Validate continuation inside strip (must match direct quadrature):")
for sigma in [mp.mpf('1.2'), mp.mpf('1.5'), mp.mpf('1.9'), mp.mpc(1,1.5), mp.mpc(1,3)]:
    a, b = M_direct(sigma,kappa,mu2), M_cont(sigma,kappa,mu2)
    print(f"   sigma={sigma}:  rel diff = {mp.nstr(abs(a-b)/abs(a),3)}")

print("\n2. Pole extraction (exact tail carries the poles; eps can be tiny now):")
target2 = 1/(4*mp.pi*kappa)
target1 = mp.log(kappa/mu2)/(4*mp.pi*kappa)
print(f"   predicted double-pole coeff = {mp.nstr(target2,12)}")
print(f"   predicted simple-pole coeff = {mp.nstr(target1,12)}")
for eps in [mp.mpf('1e-3'), mp.mpf('1e-5'), mp.mpf('1e-7')]:
    M = M_cont(2-eps, kappa, mu2)
    c2 = eps**2 * M
    c1 = eps*(M - target2/eps**2)
    print(f"   eps={mp.nstr(eps,2)}: eps^2*M = {mp.nstr(c2,10)} | eps*(M - c2pred/eps^2) = {mp.nstr(c1,10)}")

print("\n3. s0-independence of continuation (sigma=1.7, s0=30 vs 200):")
v1 = M_cont(mp.mpf('1.7'), kappa, mu2, s0=30)
v2 = M_cont(mp.mpf('1.7'), kappa, mu2, s0=200)
print(f"   rel diff = {mp.nstr(abs(v1-v2)/abs(v1),3)}")

print("\n4. Second kinematics (kappa=0.75, mu2=0.1):")
kappa2, mu22 = mp.mpf('0.75'), mp.mpf('0.1')
eps = mp.mpf('1e-6')
M = M_cont(2-eps, kappa2, mu22)
print(f"   eps^2*M = {mp.nstr(eps**2*M,10)}  vs 1/(4 pi kappa) = {mp.nstr(1/(4*mp.pi*kappa2),10)}")
print(f"   eps*(M-dp/eps^2) = {mp.nstr(eps*(M-1/(4*mp.pi*kappa2)/eps**2),10)}  vs L/(4 pi kappa) = {mp.nstr(mp.log(kappa2/mu22)/(4*mp.pi*kappa2),10)}")
