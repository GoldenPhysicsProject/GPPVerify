# Critical boundary and divisor audit — 2026-09-14

Status: analytical proofs, not Lean-certified. Continuation of the September 13 coherent-state work. No RH claim.

## Critical GCD form is not closable on ordinary l2

On finitely supported sequences indexed by positive integers let
q_sigma(c)=sum conjugate(c_m)c_n (gcd(m,n)^2/(mn))^sigma.
Finite positivity follows from the prime Poisson kernels.

For a finite prime set P let r_p=p^(-sigma), S_P=sum_P r_p^2,
x_P=sum_P (r_p/S_P)e_p. The restricted matrix has entries
K(1,p)=r_p, K(p,p)=1, K(p,q)=r_p r_q for distinct primes. Consequently

    ||x_P||_2^2 = 1/S_P,
    q_sigma(x_P) = 1+E_P,
    q_sigma(x_P-e_1) = E_P,
    E_P = sum_P r_p^2(1-r_p^2)/S_P^2,
    0 <= E_P <= 1/S_P.

For 0<sigma<=1/2, Euler's divergence sum_p 1/p implies S_P -> infinity.
Thus x_P -> 0 in ordinary l2, q_sigma(x_P) -> 1, and
q_sigma(x_P-x_Q)<=2E_P+2E_Q -> 0. This violates the sequential
criterion for closability. No closed nonnegative form on ordinary l2 can
extend this unchanged finite form.

The intrinsic GNS completion does exist: in it x_P -> e_1.
The same sequence has incompatible limits in the two topologies.
This is stronger than an unbounded first column. It does NOT identify this
defect with the Hardy bad-zero space K_B.

## Three coherent-state boundary limits

Put epsilon=2sigma-1 and C_epsilon(v)=zeta(1+epsilon+iv)/zeta(1+epsilon).

1. Since |C_epsilon|<=1 and it tends to zero almost everywhere,
C_epsilon -> 0 in tempered distributions, NOT a Dirac delta.

2. Removing normalization gives zeta(1+epsilon)C_epsilon -> Fourier(nu),
where nu=sum_n n^(-1) delta_(log n), with Fourier convention exp(-ivx).
This is a positive tempered measure since nu([0,R])=R+O(1).
Dominated convergence against a Schwartz Fourier transform proves the limit.
Locally at zero its Fourier transform is
pi delta_0 - i PV(1/v) + h(v), where h(v)=zeta(1+iv)-1/(iv) is regular at zero.
Positive definiteness of this distribution is not pointwise positivity.

3. Rescaling v=epsilon w gives C_epsilon(epsilon w)->1/(1+iw).
Equivalently epsilon log N converges in law to Exp(1) under the zeta Gibbs law.
This universal scaling limit alone does not encode the arithmetic divisor.

With beta=2sigma and L=log zeta:
d_sigma log C=2[L'(beta+iv)-L'(beta)],
d_sigma^2 log C=4[L''(beta+iv)-L''(beta)],
d_v^2 log C at zero=-L''(beta).
The sigma Fisher information is 4L''(beta), and the coherent-state
Fubini–Study metric is L''(beta)(d_sigma^2+d_t^2).
The pure-state quantum Fisher metric is four times this metric.

The Laurent expansion yields
L''(1+epsilon)=epsilon^(-2)-2gamma_1-gamma_0^2+O(epsilon).
The finite constant is numerically about -0.18755.
Merely subtracting the universal Fisher divergence therefore does not
produce a positive metric. The expansion is exact; the decimal is not
an interval-certified computation.

The logarithmic derivative boundary corresponds to
sum Lambda(n)/n delta_(log n), already anticipated by the Discovery2
pole-subtraction/discrepancy notes. The Weil weight Lambda(n)/sqrt(n)
requires an exponential tilt exp(x/2). That operation is not continuous
on tempered distributions. The stronger test space and completed
prime–Archimedean pairing must be specified.

## Exact counterexample to an unrestricted Pick denominator inference

The Drive note cvs_loewner_pick_bridge-1.md constructs a positive Pick
kernel from a Loewner matrix Q, its lowest eigenvalue epsilon, and a
ground eigenvector c. Its rational function is R=N/D.

Take nodes (-1,0,1), Q=0, b_i=0, and c=(1,-1,1). Then epsilon=0,
P=Q-epsilon I=0, and

    D(z)=1/(z+1)-1/z+1/(z-1)=(z^2+1)/(z(z^2-1)),
    N(z)=0, R(z)=0.

The Pick kernel is zero and positive semidefinite, while D has nonreal
zeros at +/-i. All c_i are nonzero. The general finite Pick argument
therefore does not establish real-rootedness of the unreduced denominator.
Additional CvS-specific cancellation control is essential.
Separately, interpolation at a node by dividing by c_i requires c_i!=0.

## Domain correction to the prolate leakage archive

The semilocal_prolate_leakage-1.md note establishes an upper Hilbert-norm
leakage estimate. Its subsequent equality exp(-2pi lambda^2+O(lambda))
requires a lower bound not supplied by that argument and should remain
an upper bound.

The radical identity q(Pr,Pr)=q((I-P)r,(I-P)r) is valid on the appropriate
form domain. Small Hilbert norm of the tail alone does not bound its Weil
energy. A form-norm continuity estimate is necessary.

Sources:
- https://drive.google.com/file/d/1_NmeOc-6ua811I2kUxaZW9Ol9EVGqnTD/view
- https://drive.google.com/file/d/1aif_PAFzgDrDSoJZvvhrdGc3aapQKQmS/view
- https://drive.google.com/file/d/1WtcYcATUmj4R3kGb0HeAsN9N6AhB8UZZ/view
- v34 manuscript read from GPP/Everything PDF.

Working inference: control the completed form domain and preserve the
divisor through the limit. The positive intrinsic prime space is useful,
but its metric cannot be moved unchanged to ordinary l2 at criticality.

## Verification status

Initial head 7851e18424c1ceee740d4b47e54f13a28cf5724b was verified live.
Root wiring added 199 imports. Cold workflow 34789851671 checked out
fc7397562c09f84b91b75e03a651d49f7a684b33 and FAILED, producing diagnostics
in 79 source files including dependent bad imports. The whole project and
all newest RH modules must not be called machine checked. PR173 remains
open and draft. Local workspace became unavailable; connector-based
repairs continue with explicit verification limitations.
