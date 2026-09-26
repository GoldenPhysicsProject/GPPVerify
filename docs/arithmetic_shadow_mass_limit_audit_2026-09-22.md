# Arithmetic shadow boundary: mass-limit and leakage audit
Date: 2026-09-22. Status: analytical proofs and elementary numerical checks; no RH proof and no Lean certification.

Read against uploaded arithmetic_shadow_boundary_v1.tex and the arithmetic/quarter-turn portions of Which_Way_Is_Forward_v23-2.tex. Live PR173 is open, draft, currently mergeable at d642339799d3ec1f2cd05431461d05af03fddebd. This is not a CI-success claim.

## 1. What the new note usefully isolates
The incoming defect identity T* T + H* H = I is exact for a unimodular multiplier compressed to a Hardy space. Incoming isometry, rather than two-sided unitarity, is the right target. The outgoing model space need not vanish.

The compressed quarter-turn calculation also checks algebraically:
P_+(J^2+I)P_+ = 2 H*H.
Vanishing compressed defect implies J^2 f=-f for causal f: zero leakage makes Kf lie in the opposite Hardy half, after which K^2=I proves the assertion. This is more precise than invoking a generic order-four symmetry.

An actual arithmetic intertwiner with the geometric quarter-turn is still unconstructed. Doubling an arbitrary contraction already gives a unitary Julia colligation, so existence of that completion cannot itself eliminate leakage.

## 2. Exact cost of the optimal massive tail
Use q_0=c and q_k=c r^k for k>=1, with 0<r<1 and
mu^2=(1-r)^2/r,
r=exp(-2 asinh(mu/2)).
This is the stationary solution for the tail functional
E_tail=sum_(k>=1)|q_k-q_(k-1)|^2 + mu^2 sum_(k>=1)|q_k|^2
with q_0 fixed. Strict convexity at mu>0 makes it the unique minimizer.

Summing geometric series gives
E_tail=(1-r)|c|^2,
sum_(k>=1)|q_k|^2 = r^2/(1-r^2) |c|^2.
Therefore as mu decreases to zero,
E_tail ~ mu |c|^2,
||q_tail||_2^2 ~ |c|^2/(2mu).

For c=1:
mu=1: E=.618033988750, squared norm=.170820393250;
mu=.1: E=.095124921973, squared norm=4.51873050286;
mu=.01: E=.009950124999, squared norm=49.5018749805;
mu=.001: E=.000999500125, squared norm=499.500187500.

Thus arbitrarily cheap energy can hide arbitrarily large ordinary Hilbert norm. The positive-mass no-ghost theorem cannot be passed to zero mass without an additional estimate.

## 3. A finite-support counterexample to homogeneous boundary continuity
Take q_0=0 and
q_n=min(n,2N-n)/N for 1<=n<=2N,
q_n=0 for n>2N.
Then, exactly,
E_0(q)=sum_(n>=1)|q_n-q_(n-1)|^2=2/N,
B(q):=sum_(n>=1)q_n/n=2(H_(2N)-H_N) -> 2 log 2.
Hence B is not continuous in the homogeneous Casimir energy norm even on finite-support sequences. No estimate
|B(q)| <= C sqrt(E_0(q))
can hold on that full test space.

These tents are NOT arithmetic ghosts: they do not obey the simultaneous equations B(U_m q)=q_1. The counterexample rules out a generic energy argument, not an estimate exploiting all ghost constraints. That distinction is essential.

## 4. Sharp massive boundary-functional norm
This sharpens the preceding obstruction quantitatively.

Let L=2I-S-S* on l2 indexed by n>=1, with Dirichlet boundary q_0=0; b_n=1/n. Put
C_mu=||B||_(E_mu dual)^2
     =<b,(L+mu^2 I)^(-1)b>.
The discrete sine transform is unitary to L2(0,pi), diagonalizes L by
4 sin^2(theta/2), and sends b to
sqrt(2/pi) sum_(n>=1)sin(n theta)/n
= (pi-theta)/sqrt(2pi).
The Fourier series identity follows by taking the imaginary part of
-log(1-r exp(i theta)), then r increasing to 1; equivalently use Abel summation of -log(1-r exp(i theta)) directly.

Thus the exact formula is
C_mu = (1/(2pi)) integral_0^pi
       (pi-theta)^2/[mu^2+4 sin^2(theta/2)] dtheta.

Splitting at fixed small delta, scaling theta=mu u in the first part, and then sending delta to zero gives
lim_(mu->0+) mu C_mu = pi^2/4.
Indeed the numerator tends to pi^2, sin(theta/2)~theta/2, and integral_0^infinity du/(1+u^2)=pi/2. The part theta>=delta contributes zero after multiplication by mu; the local comparison bounds justify the limit.

Therefore
||B||_(E_mu dual) ~ pi/(2 sqrt(mu)).
Equivalently the best coefficient in
E_mu(q) >= c_mu |B(q)|^2
is c_mu=C_mu^(-1) ~ 4mu/pi^2.
Equality is attained up to scalar by q=(L+mu^2 I)^(-1)b. There is no uniform coercive bound for this observable on the full massive form domain.

This identifies both the escaping observable and the exact rate of loss. A proof must gain something beyond the bare Casimir form, specifically on the arithmetic subspace or from the completed Archimedean pairing.

## 5. A one-pole calibration of the Hardy defect
In the disk Hardy realization let B_b be a single Blaschke factor, |b|<1, and let I be inner with I(b) nonzero. Set theta=I conjugate(B_b) on the circle and T=T_(B_b)* T_I.

Let e_b(z)=sqrt(1-|b|^2)/(1-conjugate(b)z).
The model space for B_b is span(e_b). Evaluation gives
T_I* e_b=conjugate(I(b))e_b.
Consequently
I-T*T = T_I* P_(e_b) T_I = |I(b)|^2 P_(e_b).

Thus one uncancelled bad factor produces an explicit positive rank-one leakage defect. Its Hankel norm is |I(b)|. For example I(z)=z and b=1/2 gives squared defect eigenvalue 1/4; the normalized quarter-turn compression -I+2H*H has eigenvalue -1/2 on that vector, not -1.

The Julia unitary completion exists in this example too. It adds the leakage channel rather than proving that channel absent. This is a direct test for proposed uses of the global colligation.

## 6. Corrections and scope cautions for the new draft
- For kappa>0 the operator A_kappa is boundedly invertible, so its Fredholm index is zero. The rank-one self-commutator remembers the unilateral shift defect, but should not be called a nonzero Fredholm index of A_kappa.
- The finite cylinder proof is valid with natural-order sums and common integer cutoffs before finite inclusion-exclusion. If h_1=0, dividing by h_1 is unavailable; a nonzero ghost carrying a nonzero vacuum charge must be separately justified by the precise duality/cyclicity construction.
- Finite-variation no-ghost and the massive implication are sound under their stated domains.
- Positive energy differences on a zero-mass completion must be defined as quadratic forms. Writing a difference of two individually divergent massive energies is not legitimate.
- The golden value is an exact unit-mass normalization in this family. It does not provide a mass bound that stays positive when the RH construction requires the zero-mass boundary.
- The geometric v23 paper itself correctly limits its arithmetic conclusion to a fixed-locus architecture. No operator/domain-preserving identification with the completed arithmetic Hardy channel is supplied there.

## 7. Consequence for the next proof attempt
The new paper materially sharpens the object to study: incoming Hardy leakage and the arithmetic divisibility boundary functional. It does not yet rule out the singular completion.

A useful next theorem would control the boundary functional on the constrained arithmetic space with the full prime–Archimedean form, or prove zero incoming leakage directly from that completed form. It must survive the tent-sequence and optimal-tail tests above. A general homogeneous-energy estimate and a positive-mass argument with constants depending on mu do not suffice.

The present calculations are obstructions to particular shortcuts, not counterexamples to RH. They identify where an additional arithmetic estimate must enter.
