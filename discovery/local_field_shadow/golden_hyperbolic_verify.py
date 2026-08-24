"""
Supplementary numerical verification for the golden-ratio-as-minimal-hyperbolic-sector
package (GppVerify/NumberTheory/GoldenRatioHyperbolicSector.lean). The Lean proofs are the
primary artifact; this is a cross-check, run fresh, not a substitute.
"""
import mpmath as mp

mp.mp.dps = 50
phi = (1 + mp.sqrt(5)) / 2

print("=== 1. Fixed point of F(x) = 1 + 1/x ===")
x = mp.mpf(1)
for _ in range(60):
    x = 1 + 1 / x
print(f"  iterate -> {x}  phi = {phi}  diff = {mp.nstr(abs(x - phi), 4)}")

print("=== 2-3. Matrix identities: A = M^2, det A = 1, tr A = 3 ===")
M = mp.matrix([[1, 1], [1, 0]])
A = M * M
print(f"  A = {[[A[i,j] for j in range(2)] for i in range(2)]}")
print(f"  det A = {A[0,0]*A[1,1]-A[0,1]*A[1,0]}  tr A = {A[0,0]+A[1,1]}  det M = {M[0,0]*M[1,1]-M[0,1]*M[1,0]}")

print("=== 6-7. Eigenvalues and discriminant ===")
tr, det = 3, 1
disc = tr**2 - 4*det
e1 = (tr + mp.sqrt(disc)) / 2
e2 = (tr - mp.sqrt(disc)) / 2
print(f"  discriminant = {disc}")
print(f"  eigenvalues: {e1}, {e2}")
print(f"  phi^2 = {phi**2}  phi^-2 = {phi**-2}")
print(f"  match: {mp.nstr(abs(e1-phi**2),4)}, {mp.nstr(abs(e2-phi**-2),4)}")

print("=== 8. Mobius fixed points of x -> (2x+1)/(x+1) ===")
x1, x2 = phi, -1/phi
for x in (x1, x2):
    lhs = (2*x+1)/(x+1)
    print(f"  x={x}: (2x+1)/(x+1)-x = {mp.nstr(lhs-x,4)}")

print("=== 9-10. Finite-place kernel at q=5, s=1/2 ===")
def K(q, s):
    return (1 - q**-1) / ((1 - q**-s) * (1 - q**-(1-s)))
k5 = K(5, mp.mpf('0.5'))
print(f"  K_5,1(1/2) = {k5}  phi^2 = {phi**2}  rel err = {mp.nstr(abs(k5-phi**2)/phi**2, 4)}")

print("=== 11. Convergence: both routes give the same real number ===")
print(f"  eigenvalue route: {e1}")
print(f"  kernel route:     {k5}")
print(f"  agree to: {mp.nstr(abs(e1-k5), 4)}")

print("\nAll checks are supplementary to the Lean proofs in")
print("GppVerify/NumberTheory/GoldenRatioHyperbolicSector.lean, not a substitute for them.")
