# REDO FOR REAL: Loops from Trees via Celestial Cuts — Session Notes (2026-08-19)

## Strategy change (the decisive one)
Stop trying to *discover* a shadow-pole mechanism and match it to the box.
Instead DERIVE the celestial statement by Mellin-transforming the one
unconditionally true loops-from-trees statement in physics: Cutkosky/unitarity.
Literature anchors (established, peer-visible): Lam–Shao arXiv:1711.06138
(optical theorem in the conformal basis = CPW decomposition on the principal
series) and the Celestial Optical Theorem arXiv:2404.18898 (completeness
relation with explicit massless normalization N = 2^{l+2} pi^3).

## Step 1 — DONE, doubly verified (symbolic sympy + mpmath quadrature 1e-20..1e-31)
Script: celestial_cut_step1.py. Conventions: l = w q(z,zbar),
q=(1+|z|^2, 2x, 2y, 1-|z|^2), metric (+,-,-,-), CM frame P=(M,0,0,0).

Derived (not asserted):
1. d^3l/(2E) = 2 w dw d^2z            [Jacobian det = 4w^2(1+|z|^2)]
2. delta^4(P - l5 - l6) forces the cut pair to ANTIPODAL celestial points:
     z6 = -1/conj(z5),  w5 = M/(2(1+|z5|^2)),  w6 = M|z5|^2/(2(1+|z5|^2))
   with constraint Jacobian det = 2 M^2 |z5|^2.
3. LIPS density: dLIPS = d^2z5 / (8 pi^2 (1+|z5|^2)^2)  -> total 1/(8pi) exact.
   (i.e. the cut is UNIFORM on the round celestial sphere.)
4. Mellin image of the cut (energies weighted w^{Delta-1}):
     Phi(D5,D6;M) = (1/(8pi)) (M/2)^{D5+D6-2} Gamma(D5)Gamma(D6)/Gamma(D5+D6)
   Verified at 5 points incl. principal series, shadow pairs, off-series;
   rel err 1e-20..1e-31.

## What this explains about "that day" (December)
- The Gamma Gamma / Gamma OPE-coefficient shape the manuscripts ASSERTED is
  real — it is the Mellin image of pure two-particle phase space. Now derived.
- "Delta5+Delta6=2" is NOT a pole where a residue is taken. It is the locus of
  SCALE INVARIANCE of the cut: (M/2)^{D5+D6-2} -> M-independent exactly there,
  matching the constant Im[bubble]=1/(16pi). Cutkosky closes exactly:
  Phi(1,1)=1/(8pi)=2 Im I2. The December story was a garbled version of this.
- Meta AI note assessment: wrong that the mechanism is a residue at Delta=2
  with Plancherel irrelevant; right instinct that a measure/normalization
  factor was missing from all earlier constructions (ledger item (d)). The
  correct pairing of cut legs as (Delta, 2-Delta) shadow pairs comes from the
  completeness relation (2404.18898 eq 14-15), whose normalization N must be
  carried — likely the cure for the old lambda=0 delta-times-pole pathology
  (Plancherel-type density vanishing at lambda=0 tames the simple pole).

## Step 2 — NEXT (concrete, bounded)
a. Add the two tree propagators of the box's s-channel cut to the integrand:
   Disc_s I4 = int dLIPS 1/((l5-p1)^2 (l5-p1-p2... )) with the EXACT antipodal
   parametrization above; everything reduces to a 2d z5-integral. Compute it
   exactly/numerically as a function of (s,t).
b. BENCHMARK FIX (root cause of every prior "comes up short"): stop comparing
   to the scheme-ambiguous massless-box finite part. Use the internally
   massive box (finite, unambiguous) or compare Disc_s directly to the
   dispersive integrand — cut-to-cut comparison, no scheme.
c. Then Mellin-transform Disc_s I4(s,t) in s at fixed t and identify the
   principal-series density — that IS K1(lambda;s,t), obtained from the true
   side of the equation instead of guessed.
d. Wire into GppVerify/discovery/shadow_ope/ (this file + script are drop-in;
   no push creds in this container — commit via Claude Code session).

## Open/honest
- Nothing about the full box reconstruction is claimed yet. Step 1 is the
  atomic building block, now on bedrock.
- The old sech^2 closed forms (Sewn_s/Sewn_t) should be re-derived from this
  parametrization to see what they actually computed.

---
## Step 2a — DONE (three-way lock, 1e-23..1e-26, four kinematic points)
Script: box_cut_step2a.py. The box s-channel cut with mu-regulated tree lines
(cut lines massless -> Step-1 phase space applies verbatim):
  C(s,t,mu^2) = int dLIPS 1/[((l5-k1)^2-mu^2)((l5+k4)^2-mu^2)]
Three independent computations agree exactly:
  (1) CM angular integral, (2) celestial z5-plane integral with derived
  measure/antipode, (3) EXACT closed form via Feynman parameter:
    C = (1/8pi) int_0^1 dx / [ mu^2(s+mu^2) + s(s+t) x(1-x) ]
      = (1/8pi) (4/sqrt(d(d+4c))) atanh(sqrt(d/(d+4c))),
      c = mu^2(s+mu^2),  d = s(s+t) = -su.
  mu->0: C -> log(s(s+t)/(mu^2 s))/(4 pi s(s+t))   [collinear log, verified].
Also verified: q(z).q(w) = 2|z-w|^2. Celestial integrand in closed z-form
(the K1 source): d^2z/(8pi^2(1+|z|^2)^2) x 1/[(M^2|z|^2/(1+|z|^2)+mu^2)
(4 w5 w4 |z-z4|^2 + mu^2)], z4 = -cot(theta*/2), w4=(M/2)sin^2(theta*/2).

## Step 2c — DONE (Mellin image of the cut; pole structure derived & verified)
Script: mellin_cut_step2c.py. At fixed angle (kappa=(s+t)/s fixed),
M(sigma) = int_0^inf ds s^(sigma-1) C(s) continues meromorphically with
  M(sigma) = (1/(4 pi kappa)) [ 1/(2-sigma)^2 + log(kappa/mu^2)/(2-sigma) ] + regular.
Verified: exact tail vs quad 2e-13; continuation vs direct quad in-strip
1e-21..1e-26; s0-independence 1e-21; double-pole coeff to 7 digits and
simple-pole coeff to 8 digits at two kinematics.
LESSON (honest): naive numerical limits at sigma->2 FAIL because the Mellin
mass sits at s ~ exp(1/eps); poles must be carried by an exact analytic tail.
PHYSICS: the loop's celestial fingerprint is a DOUBLE pole at sigma=2 with
UNIVERSAL mu-independent coefficient 1/(4 pi kappa); the collinear (IR) log
lives entirely in the SIMPLE pole. Matches the known beta-plane lore
(loop celestial amplitudes ~ higher-order poles) — now derived with all
constants from Cutkosky + the Step-1 celestial phase-space dictionary.
M(1+i lambda) on the principal line is finite and smooth: this IS the honest
K1(lambda; angle, mu), obtained from the true side of the equation.

## Step 3 — NEXT
a. Dispersion: reconstruct the full mu-regulated box from its cuts in Mellin
   space (fix the 2*pi*i Cutkosky bookkeeping once, globally).
b. Identify C's celestial form with the discontinuity of the TREE 6-point
   celestial amplitude across the shadow-paired completeness locus
   (2404.18898 eq 14-15 normalization N carried explicitly) — closing the
   original December claim as a theorem, or bounding exactly what survives.
c. Commit celestial_cut_step1.py, box_cut_step2a.py, mellin_cut_step2c.py +
   these notes to GppVerify/discovery/shadow_ope/ via Claude Code (no push
   creds here). Log Step 1+2 results to Supabase lean_results ledger.

## Step 3a — DONE (loop reconstructed from its cut; zero free parameters)
Script: dispersion_step3a.py.
- Box parametric form: I4 = (i/16pi^2) J, J = int_simplex [dx]/Delta^2,
  Delta = mu^2(x2+x4) - s x1x3 - u x2x4. Inner y-integral done exactly:
  G(c,d) = int dy/(c+dy(1-y))^2 = 8 atanh(sqrt(d/w))/(sqrt(d) w^{3/2}) + 2/(cw),
  w = d+4c (hand-derived, verified 3e-21).
- Cutkosky constant DERIVED (not fitted): Im J = 8 pi^2 C, anchored exactly
  on the bubble (Im J_2 = pi = 8pi^2 * 1/(8pi)).
- Unsubtracted fixed-u dispersion:
  J(s,u) = 8 pi int_0^inf ds' C(s',u)/(s'+|s|)
  VERIFIED: J_direct == J_disp at 4 Euclidean points, rel err 0..1.6e-21.
- CELESTIAL DISPERSION RELATION (Mellin space, strip 0<Re sigma<1):
  M_J(sigma) = (8 pi^2 / sin(pi sigma)) * M_C(sigma)
  verified 1e-11 (real sigma), 3e-7 (complex; nested-quad limit).

## THE CHAIN, COMPLETE (honest final form of the December claim)
The one-loop celestial (Mellin) amplitude equals the Mellin transform of the
tree-level unitarity cut times the UNIVERSAL kernel pi/sin(pi sigma) (with the
derived 8pi^2 normalization). Concretely:
  (1) The cut lives on the celestial sphere with derived measure
      d^2z/(8pi^2(1+|z|^2)^2), cut legs antipodal (z6 = -1/zbar5).
  (2) Its Mellin image carries the Gamma Gamma / Gamma structure (derived).
  (3) Its Mellin poles: universal double pole 1/(4 pi kappa) at sigma=2
      (fixed angle); collinear log confined to the simple pole.
  (4) The full loop = Stieltjes transform of the cut; in Mellin space,
      multiplication by 8pi^2/sin(pi sigma). The sin poles at integer sigma
      are the beta-plane poles of celestial amplitudes.
"Shadow discontinuity" = the cut. "Special Delta locus" = pole structure of
M_C. Reconstruction kernel = elementary and universal. No residue-at-Delta=2
mechanism; no fudge factors anywhere in the chain.

## Remaining
3b. Celestial-native form: write C as (Mellin tree) x (Mellin tree) sewn by
    the principal-series completeness integral with explicit N normalization
    (2404.18898) — the last cosmetic link to "trees only"; content-wise the
    chain already uses only tree propagators + derived phase space.
3c. Commit all 5 files to GppVerify/discovery/shadow_ope/ + ledger entry
    (Claude Code session; no push creds here).
3d. Paper section: replace CH_v3 par.6.7 and the TOULAF-2 story with this
    derivation (supersede/withdraw TOULAF-2).
