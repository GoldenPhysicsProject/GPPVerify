# Co-Poisson calculation in the intrinsic Möbius basis

2026-09-14. Analytical calculation, not Lean-certified. No RH claim.
This tests the proposed boundary reduction of intrinsic_gcd_mobius_generator_2026-09-14.md.

## 1. Fix the actual co-Poisson normalization

Take nonzero g in C_c^infinity(0,infinity). Use the right Mellin transform
g_hat(s)=integral_0^infinity g(x)x^(-s) dx.
Let V_n g(x)=n^(-1/2)g(x/n), unitary on L2(dx).
Then (V_n g)_hat(s)=n^(1/2-s)g_hat(s).

The classical co-Poisson operator is
C g(x)=sum_(k>=1)g(x/k)/k - g_hat(1).
On 0<Re(s)<1 its Mellin transform is zeta(s)g_hat(s).
The two constants in the co-Poisson/cosine-transform pair are controlled
by g_hat(1) and g_hat(0). See Burnol, formulae (6) and (9):
https://arxiv.org/pdf/math/0203120
These classical identities are inputs, not claimed as new.

## 2. Explicit image of every intrinsic basis vector

At sigma=1/2 the intrinsic orthonormal vector is
w_d=phi(d)^(-1/2) sum_(n|d) sqrt(n) mu(d/n)e_n,
where phi denotes Euler's totient, not the golden ratio.

Test the arithmetic synthesis map e_n -> V_n g on finite sequences.
Its image of w_d is

    g_d(x)=phi(d)^(-1/2) sum_(n|d) mu(d/n)g(x/n).

Therefore

    (g_d)_hat(s)=H_d(s)g_hat(s),
    H_d(s)=phi(d)^(-1/2) sum_(n|d)mu(d/n)n^(1-s)
          =d^(1-s)/sqrt(phi(d)) product_(p|d)(1-p^(s-1)),

and

    (C g_d)_hat(s)=zeta(s)H_d(s)g_hat(s).

These are finite divisor identities followed by the classical co-Poisson
identity. There is no exchange of uncontrolled infinite sums.

## 3. The two cusp moment rows become explicit

The divisor identities give

    H_d(0)=sqrt(phi(d)),
    H_d(1)=1 if d=1, and 0 otherwise.

For f_a=sum_(d<=N)a_d g_d, assuming g_hat(0) and g_hat(1) are nonzero,
the two zero-moment conditions are exactly

    a_1=0,
    sum_(d=2..N) sqrt(phi(d)) a_d=0.

For a nonnegative nonzero bump g both seed moments are positive.
If a seed moment is zero, its corresponding constraint is already satisfied
and must not be counted as an independent row.

These conditions remove the constants in the co-Poisson pair. Compact
support of the input supplies the corresponding gaps near zero; the gap
sizes depend on the support and cutoff. This is not yet a uniform limiting
Sonine-space construction.

## 4. Calculate the finite projection in the intrinsic metric

The w_d are orthonormal in H_(1/2). After removing w_1, let

    L_N=diag(log 2,...,log N),
    v_N=(sqrt(phi(2)),...,sqrt(phi(N))),
    S_N=sum_(d=2..N)phi(d), u_N=v_N/sqrt(S_N).

The intrinsic orthogonal projection enforcing the second row is
P_N=I-u_N u_N*. The two-row projection on the whole finite space is
I-e_1 e_1*-u_N u_N* (with u_N padded by zero in the first coordinate).

For every fixed d>=2, |<e_d,u_N>|^2=phi(d)/S_N ->0.
Since ||u_N||=1, density of finite sequences gives u_N ->0 weakly.
Thus u_N u_N* ->0 strongly, despite having trace one at every cutoff.
On the full sequence space the cutoff two-row projections tend strongly
to I-e_1e_1*: the second constraint disappears in this topology.

This is an explicit escaped-rank phenomenon. It is not identified with K_B.
The unbounded moment functional cannot be retained by merely taking
the ordinary intrinsic-norm closure of its finite-support kernel.

## 5. Calculate the compressed determinant, retaining all factors

Let A_N be the compression of L_N to u_N-perp. For z away from log d,

    det(A_N-zI)
      = product_(d=2..N)(log d-z)
        * [1/S_N sum_(d=2..N) phi(d)/(log d-z)].

Proof: complete u_N to an orthonormal basis, and use the cofactor formula
for the u_N,u_N entry of (L_N-zI)^(-1). Both sides extend as the same
polynomial after cancellations.

The rational factor has positive residues in the convention
1/(log d-z). Its derivative on each pole-free real interval is positive,
and it changes from -infinity to +infinity between successive poles.
Thus the N-2 compressed eigenvalues strictly interlace log 2,...,log N.
They retain the original counting density up to one state.

This compression is NOT the same as exact Feshbach elimination.
If L_N is written in the splitting u_N-perp plus span(u_N),

    L_N = [[A_N,b_N],[b_N*,c_N]],

then the exact energy-dependent reduced pencil is

    F_N(z)=A_N-zI-b_N(c_N-z)^(-1)b_N*,
    det(L_N-zI)=(c_N-z)det F_N(z).

Discarding either c_N-z or the self-energy term changes the spectral problem.
A Schur elimination with all factors retained cannot manufacture a new
zero divisor from the log-integer spectrum.

Numerical cross-check, N=80 and z=-0.7:
compressed dimension 78; log-determinant identity residual 1.43e-14.
Lowest compressed eigenvalue 0.6947075284 lies between log 2 and log 3.
For N=20,80,320,1280, the second-constraint squared projection of w_2 is
0.0078740, 0.00050891, 0.000032019, 0.0000020066 respectively.
These floating-point checks support the algebra; they do not prove RH.

## 6. The actual co-Poisson Gram matrix is different

Mellin Plancherel gives the explicit positive finite matrix

    G_de=(1/(2pi)) integral_R
         |zeta(1/2+it) g_hat(1/2+it)|^2
         conjugate(H_d(1/2+it)) H_e(1/2+it) dt.

The integral converges for the chosen smooth compactly supported seed.
It is positive definite on a finite cutoff: a nonzero finite combination
of the independent divisor polynomials cannot vanish on almost every t,
and the scalar multiplier is nonzero almost everywhere.

This matrix is NOT the identity matrix of the intrinsic basis.
For the moment matrix C_N with the two rows above, the finite projection
orthogonal in this actual Gram metric is instead

    P_N^G=I-G_N^(-1) C_N*
               (C_N G_N^(-1) C_N*)^(-1) C_N,

for N>=2 and independent rows. This is an explicit formula, but no uniform
infinite-cutoff bound for these inverses has been proved.

If a Hermitian arithmetic form has coefficient matrix H_N, its operator
in this metric is G_N^(-1)H_N and its spectral pencil is H_N-zG_N.
One must derive H_N from the intended completed boundary dynamics.
Keeping diag(log d) after changing the metric would require proving
G_N L_N=L_N G_N, which is not automatic.

Inserting the standard completion multiplier
a(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2 replaces zeta by xi in the Gram integrand.
That gives another positive Gram matrix, but supplies no determinant
identity: a modulus-square boundary Gram does not by itself establish
where the complex zeros of xi lie.

## 7. A direct topology check on the proposed identification

No normalized vector g in any strongly continuous unitary real-dilation
representation can realize the unchanged GCD kernel as
< V_m g,V_n g > for all positive integers.

Indeed m=n+1 has gcd(m,n)=1, so its GCD overlap tends to zero:
K_sigma(n,n+1)=[n(n+1)]^(-sigma)->0.
But log((n+1)/n)->0 and strong continuity forces the corresponding
dilation overlap to tend to ||g||^2=1.

Thus the finite synthesis map used above is an algebraic test map,
not a proved isometric embedding of the intrinsic completion into the
Archimedean dilation space. The Gram change in section 6 is essential.

## Outcome

The requested calculation is explicit through the co-Poisson basis images,
both cusp rows, the intrinsic finite projection, the compressed determinant,
and the actual finite boundary Gram/projection formula.

It does not produce the Riemann Fredholm operator. It identifies precisely
why the naive reduction fails: a cusp constraint escapes in the intrinsic
topology, and the actual Archimedean pairing changes the Gram matrix.
The remaining task is to control that actual completed matrix and derive
its dynamics and determinant identity, not to infer them from finite positivity.

Verification: cold run 34848423834 at 060ca12... confirms the repaired
finite moment Gram, finite heat Gram, and positive-square odd-sector modules
compiled. RiemannCayleyUnitarityBoundary still had one algebraic proof failure.
Whole-project CI remains failed. No merge/close action.
