# Cross-manuscript synthesis: thermal circle, BPY, and physical-time transfer
Date: 2026-09-14. Author: Codex. Status: analytical derivations plus numerical checks, not a proof of RH or the Yang–Mills existence/mass-gap problem.

## Sources actually compared
Targeted proof-bearing sections, not a claim to have read every archived version:
- ONON-5-2-1-3.tex: celestial thermal/blackbody section (labels sec:blackbody-law, thm:det-zeta), number-theory bridge, all five RH pathways, and YM spectral-transfer/RG passages.
- rh_cesaro_v2.tex, rh_physics-2-4_edited.tex (including its explicit conditional Bridge Claim), wightman_paper.tex, YM_PAPER-3-5.tex, haar_positivity_weil_wightman.tex.
- Drive arithmetic-field paper: https://drive.google.com/file/d/1pBV0881IZ3BXMqscaIf85hbHQHRgx-nM/view
- Drive patched Haar positivity paper: https://drive.google.com/file/d/19diaTG8Zqnx4OBsmbWJZpUAYgJ3Qf1uN/view
- Drive Haar-square trace-gap research note: https://drive.google.com/file/d/1wpV3P29VZWbUZBeIS1iUTS3tDd7WJOWZ/view
- Current September 12–14 branch notes, including the intrinsic GCD generator and co-Poisson cusp/Schur calculation.

The Drive trace-gap note is secondary research, not a verified theorem. In particular its displayed expressions involving zeta(1) without a regularization cannot be used as literal identities.

## 1. A precise usable combination: celestial thermal circle → BPY → xi

Let A0 on l2(N) have eigenvalues 1/n^2. It is positive trace class, and
D0(z)=det(I+z^2 A0)=sinh(pi z)/(pi z).
The book's thermal weight P(z)=pi z/sinh(pi z) is D0(z)^(-1).

Let independent G_n have Gamma(shape=2, rate=1) laws, and define
X=sum_(n>=1) G_n/n^2.
This is finite almost surely because E X=2 zeta(2)<infinity. Independence and monotone convergence give, for t>=0,
E exp(-tX)=product_n (1+t/n^2)^(-2)=P(sqrt(t))^2.

The classical BPY identity identifies Y=sqrt(X/pi) in distribution with sqrt(2/pi) times the standard Brownian-bridge range. Thus
E X^q = 2 pi^q xi(2q).
Source: Biane–Pitman–Yor, https://arxiv.org/pdf/math/9912170, Proposition 1 and Table 1. This is prior art, recovered here as an explicit cross-manuscript connection.

Consequently, with q=1/4+z/2,
F(z)=xi(1/2+z)/xi(1/2)
    =pi^(-z/2) E[X^(1/4+z/2)]/E[X^(1/4)].
Equivalently F is the moment-generating function of (log X-log pi)/2 under the X^(1/4)-tilted law. Functional-equation symmetry makes this tilted log-variable symmetric.

For 0<Re(q)<1 the conversion can be implemented without zeros:
E X^q = q/Gamma(1-q) integral_0^infinity
        [1-P(sqrt(t))^2] t^(-q-1) dt.
For real q this follows from the fractional-power integral and Tonelli; extension to the strip follows by domination. The full Mellin identity extends further by BPY's tail estimates.

Numerical check in scripts/check_celestial_bpy_bridge.py: q=0.1,0.25,0.5,0.7 agree with 2 pi^q xi(2q), relative errors approximately 4.8e-39,8.4e-37,1.7e-33,5.0e-31. These are floating-point checks with explicit tail approximations, not interval certificates.

Why this is useful: there really is one stochastic object connecting the book's circle determinant and BPY's completed xi. Why it is not RH: the two functions arise through different transforms. Laplace positivity of X is not preservation of imaginary-axis zeros under taking fractional Mellin moments and a log-variable tilt. A separate theorem is needed for this particular distribution. The September BPY Hankel/Fredholm problem is exactly where that conversion must earn its positivity.

This construction is a useful archimedean/reference model. The Möbius/von-Mangoldt connection supplies arithmetic differential data, and the co-Poisson/Eisenstein identities supply candidate ways to couple them. An actual coupling must reproduce the completed arithmetic form, with its boundary terms, rather than merely reproduce the scalar xi moment identity.

## 2. Quantitative obstruction to using the circle operator itself

Write L(z)=log F(z). Any proposed positive trace-class A with F(z)=det(I+z^2 A) must satisfy
Tr A=L''(0)/2,
Tr A^2=-L''''(0)/12.
These derivative requirements use xi near 1/2, not its zeros.

Numerically:
Tr A = 0.0231049931154189707889338104303390140033817604,
Tr A^2 = 0.0000371725992852696861648662624717405784536508897,
R_xi=Tr A^2/(Tr A)^2 = 0.0696323806096908694918244157068877628375368683.

For every scalar rescaling c A0:
R_circle=zeta(4)/zeta(2)^2=2/5.
Therefore no rescaling of the circle inverse Laplacian gives the required xi determinant. Analytically its determinant zeros are already the wrong set, z=+/- i n/sqrt(c); the moment check provides a zero-independent diagnostic.

More generally, if such A exists and A0 is compared on the same Hilbert space (allowing any unitary conjugation), the reverse triangle inequality gives
|| A/Tr A - U(A0/Tr A0)U* ||_HS
 >= sqrt(2/5)-sqrt(R_xi)
 approximately 0.368576050812246.
The inequality is exact; the displayed constant is numerical. The required normalized spectral change cannot be arbitrarily small in Hilbert–Schmidt norm. This does not exclude a substantial arithmetic modification.

Distinguish three operations throughout:
- arithmetic gas: zeta(s)=Tr(exp(-s diag(log n))), Re(s)>1;
- circle: zeta(2s)=Tr((diag(n^2))^(-s)), Re(s)>1/2;
- RH target: xi(1/2+z)/xi(1/2)=det(I+z^2 A).
Self-adjointness in either of the first two does not settle zeros of the third.

## 3. Exact obstruction in the proposed Yang–Mills Euclidean kernel

YM_PAPER-3-5.tex defines K_Delta(x;z)=|x-X(z)|^(-2 Delta), X(z)=(0,n_hat(z)), and correctly observes
K_Delta(theta x;z)=K_Delta(x;z).
Its resulting S2 therefore has the stronger property
S2((-t,x),(s,y))=S2((t,x),(s,y)),
with reflection of only the first argument. Any regulator used in the displayed integral must preserve this identity for the following conclusion.

Lemma. A two-time kernel C(t,s) which is invariant under simultaneous time translation and under reflection of its first argument separately is constant.
Proof: translation invariance gives C(t,s)=f(t-s). Reflection gives f(-t-s)=f(t-s). Given a,b, put t=(a-b)/2, s=-(a+b)/2. Then t-s=a and -t-s=b; hence f(a)=f(b).
The argument holds after spatial smearing and also distributionally.

Thus the displayed construction cannot simultaneously produce a nonconstant time-translation-invariant two-point function. If connected correlators also cluster, the time-constant connected two-point function vanishes. It cannot furnish the nontrivial massive sector intended in the paper.

There is an independent issue in the same proof: C(1+i lambda)|z-w|^(-4(1+i lambda)) with positive real C is generally not even Hermitian as a fixed-lambda kernel. Interchanging z,w leaves it unchanged, whereas conjugation reverses its nonconstant phase. WZW unitarity does not establish positivity of this displayed fixed-lambda form. Pairing lambda with -lambda may produce a different real kernel, but requires a new positivity proof and does not repair the separate-time-evenness obstruction.

A viable replacement must preserve physical time translation. At the scalar two-point level the familiar template is
S2(x-y)=integral rho(dm^2) integral d^3p/(2pi)^3
 exp(i p.(x-y)) exp(-sqrt(p^2+m^2)|t-s|)/(2 sqrt(p^2+m^2)),
with rho positive. Time reflection produces exp(-omega(t+s)), a genuine Gram factorization on positive times; it does not leave each argument separately unchanged.

This is only a template. Taking all higher correlators by Wick's rule produces a generalized free field, not interacting Yang–Mills. Gauge-invariant interacting Schwinger functions, their limits, locality and YM identification must still be constructed.

## 4. What survives from the other routes, and what cannot be combined into a proof

- ONON Path 1: unitary multiplicative characters and invariant means are useful. The assertion that ordinary L2 fails to exist on an infinite-measure space is false; L2(R) exists. No character exp(i gamma u) lies in ordinary L2(R). Changing to an invariant-mean Hilbert space requires a new arithmetic spectral identification.
- Path 2: the Born-rule argument puts all zeros into Hilbert spectral atoms at its first step. That is the missing bridge, not a consequence of the Born rule.
- Path 3: the BPY scalar identity is valuable with the scaling above. Its no-ghost argument again imports the same spectral-atom identification. The manuscript's displayed alternating-series moment calculation does not equal 2xi(s); already at s=2 its intermediate expression gives 1/12 rather than pi/3.
- Path 4: writing K=T* T using a Gram square root proves positivity of the constructed K. The unresolved question is its equality to the full Weil form. Coordinates Delta=1+i x with real x already restrict to the principal line; reflecting x does not detect a displacement off that line.
- Path 5: the passage inspected assumes RH in its completeness argument. It cannot independently supply the positivity used to prove RH.
- rh_physics-2-4_edited.tex already labels its temperedness Bridge Claim as equivalent to RH. Preserve that correction when older unconditional claims recur.
- rh_cesaro_v2.tex: for one off-line mode exp(delta u), its positive Abel norm is epsilon^2/(epsilon^2-4delta^2) ONLY for epsilon>2|delta|. Continuing the rational expression to epsilon=0 crosses a pole; it is not a limit of convergent positive integrals. At epsilon=delta=0.1 it is -1/3 while the defining integral diverges.
- Arithmetic-field paper: the Fock partition trace is sound. Its shifts are not canonical bosonic creation operators: [S_p*,S_p] is the projection onto states with zero p occupation, not identity. More importantly diag(log n) has pure point spectrum while the dilation generator on L2(R,du) has continuous spectrum, so the claimed unitary intertwiner cannot exist. Rational ideles have norm 1, not norm n.
- Wightman paper: compact Haar positivity is useful; the step “restrict SU(4) to the Poincare subgroup” is unavailable. SU(4) is not the noncompact conformal real form SU(2,2), and the field/distribution construction cannot be replaced by that restriction.
- Patched Haar-positivity paper: its proof-status section correctly separates positive-type/GNS/gauge-projection facts from imported arithmetic and continuum identifications. Those imported claims cannot validate one another by citation.

## 5. The strongest joint research direction

RH: combine the exact thermal-circle-to-BPY transformation above with the current prime connection and completed co-Poisson/Eisenstein boundary problem. Keep the exact xi identity as a matching test. Seek a positive arithmetic operator, or an exact completed norm-square formula, with every cusp/Schur correction retained. The calculations above immediately reject unchanged circle and log-integer generators. They do not yet provide the required operator or kill K_B.

YM: combine compact gauge projection and lattice reflection positivity with a reconstruction map that intertwines physical time translations and reflections. Seek uniform bounds, in physical units, on the vacuum-orthogonal transfer semigroup along the continuum limit:
||exp(-t H_a)(I-P_vac,a)|| <= exp(-m t), m>0 independent of cutoff and volume,
together with convergence and nontriviality of the full Schwinger family. Celestial data may constrain this map or its spectral density, but cannot replace it by a radial/conformal generator.

The newer ONON passage already correctly states that the principal-series parameter is kinematic and color projection does not remove it; it also labels spectral transfer as a conjecture. Its separate strong-coupling-plus-RG argument still does not prove continuum gap survival: scale independence along an RG trajectory does not identify a fixed strong-coupling lattice model with the continuum limit.

A conformal-cylinder gap gives exp(-Delta tau)=r^(-Delta) when r=exp(tau), not exp(-m r). Hence conformal spectral discreteness alone is insufficient for a physical mass gap.

The official YM target includes a nontrivial four-dimensional theory and a gap for the physical Hamiltonian: Jaffe–Witten, https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf. The template above is a research requirement, not a solution.

The common lesson is positivity plus a verified transport of the actual dynamics and control of the limit. Neither ordinary Haar positivity nor symmetry supplies that transport automatically.

## Coordination and verification
Claude's September 14 observation about rigidity of log-integer counting under bounded self-adjoint perturbations is consistent with the current intrinsic-GCD result. One qualification: the unilateral-Hardy-shift index obstruction is a distinct invariant; it does not literally use diag(log n) as its backbone.

This note does not claim whole-project Lean success. Previously observed cold builds failed; new analytic results here are not Lean-certified. No manuscript was overwritten and neither coordination PR nor PR173 was merged.
