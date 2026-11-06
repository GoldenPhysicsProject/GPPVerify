# Numerical normalization check for GppArithmeticReflection.weilForm (Claude Code, 2026-11-06).
# pole - prime + A_inf vs sum over zeta zeros of ghat(gamma). Evidence, not proof.
import mpmath as mp, numpy as np
from scipy import integrate
a=0.6
def F(x): x=np.asarray(x,float); return np.where(np.abs(x)<a, np.cos(np.pi*x/(2*a))**2, 0.0)
xs=np.linspace(-a,a,20001); fx=F(xs)
def g(u):
    u=abs(u)
    if u>=2*a: return 0.0
    ys=np.linspace(-a+u,a,20001); return np.trapezoid(F(ys)*F(ys-u),ys)
def ghat(t): return np.trapezoid(fx*np.cos(t*xs),xs)**2
zs=[float(mp.zetazero(k).imag) for k in range(1,600)]
Z=sum(2*ghat(t) for t in zs)
us=np.linspace(-2*a,2*a,4001); gu=np.array([g(u) for u in us])
pole=np.trapezoid(gu*2*np.cosh(us/2),us)
prime=sum(np.log(p)/np.sqrt(n)*2*g(np.log(n)) for n,p in [(2,2),(3,3),(4,2)])
I1,_=integrate.quad(lambda t: ghat(t)*float(mp.re(mp.digamma(0.25+0.5j*t))),0,300,limit=2000)
arch1=2*I1/(2*np.pi)-g(0)*np.log(np.pi)
g0=g(0)
ci=lambda u:(np.exp(-2*u)*g0-np.exp(-u/2)*g(u))/(1-np.exp(-2*u))
I2a,_=integrate.quad(ci,1e-9,2*a,limit=400); I2b,_=integrate.quad(ci,2*a,80,limit=200)
arch2=-(float(mp.euler)+np.log(np.pi))*g0+2*(I2a+I2b)
print("zeros(599)",Z,"tail est",2*ghat(zs[-1]))
print("pole",pole,"prime",prime,"arch_digamma",arch1,"arch_codex",arch2)
print("W_digamma",pole-prime+arch1,"W_codex",pole-prime+arch2)
