# Local-field shadow kernels, celestial unitarity, and the adelic principal series

**Status: NEW RESEARCH FRONT. Not an RH proof. Not evidence toward RH.**

Source: Daniel Toupin's own research program, rewriting the corrected celestial
loops-from-cuts construction (`discovery/shadow_ope/`) in normalized principal-series
variables, to determine whether celestial Cutkosky unitarity, 1D Mellin/shadow harmonic
analysis, and adelic PGL(2) harmonic analysis are manifestations of a common rank-one
local-to-global structure. Every identity below was independently rerun in this container
(`local_shadow_kernel_verify.py`) before being written up here, and the two unconditional
structural facts (shadow reflection + principal-series positivity, at the Archimedean place;
the diagonal conformal lift) are formalized in Lean
(`GppVerify/QuantumGravity/{LocalShadowKernel,DiagonalConformalLift}.lean`).

## What is established (proved, in Lean, unconditionally)

1. **`GppLocalShadow.archKernel_reflection`**: the Archimedean shadow kernel
   `K_{∞,d}(a) := Γ(a)Γ(d-a)/Γ(d)` satisfies `K_{∞,d}(a) = K_{∞,d}(d-a)` for every real `d`
   and complex `a`.
2. **`GppLocalShadow.archKernel_principal_series` / `_pos`**: on the principal series
   `a = d/2 + it`, `K_{∞,d}(a) = |Γ(d/2+it)|²/Γ(d)`, positive whenever `d > 0`. Shadow
   reflection becomes Hermitian conjugation exactly on this line, via `d - a = conj(a)`
   (`Complex.Gamma_conj`) and `Complex.mul_conj`.
3. **`GppDiagonalLift.delta_D` / `J_D` / `D_one_sub_eq_shadow2_D` / `delta_shadow2_D`**: the
   diagonal lift `D(s) = (s,s)` has `Δ = 2s`, `J = 0`, and intertwines the 1D shadow `s↦1-s`
   with the 2D celestial shadow `(h,ħ)↦(1-h,1-ħ)` exactly.

Both files are kernel-clean: no `sorry`, no custom axiom (`scripts/check_axioms.lean`
confirms Lean built-ins only on all eight theorems).

**Not formalized, deliberately**: the integral representation `K_{∞,d}(a) =
∫₀^∞ x^(a-1)/(1+x)^d dx` is taken as a *definition* (the closed Beta/Gamma form), not
*derived* from Mathlib's `[0,1]`-interval Beta integral via the substitution `x=t/(1-t)`.
That derivation is real, tractable, separate work — not attempted this round, so as not to
conflate "I defined K via its known closed form" with "I proved the integral converges to
that closed form from Mathlib's more primitive Beta integral." Independently verified
numerically instead (`local_shadow_kernel_verify.py`, item 1, `rel err` `0` to `2e-31`
against direct numerical quadrature).

## What is verified numerically only (NOT in Lean, NOT claimed as theorems)

All to 30–40 significant digits in `local_shadow_kernel_verify.py`, run fresh in this
container:

- **d=1 specialization** (`K_{∞,1}(s) = Γ(s)Γ(1-s) = π/sin(πs)`, Euler reflection) and its
  role in the independently-verified Mellin-space dispersion relation
  `M_loop(σ) = [8π²/sin(πσ)]M_cut(σ) = 8π·K_{∞,1}(σ)·M_cut(σ)` from
  `discovery/shadow_ope/dispersion_step3a.py` (already independently rerun in the prior
  round: direct-vs-dispersion `0` to `1.6e-21`).
- **d=2 specialization**: `K_{∞,2}(1+iλ)/(8π) = λ/(8 sinh(πλ))`, matching the
  independently-verified celestial two-particle phase-space Mellin image
  `Φ(Δ5,Δ6;M)` from `discovery/shadow_ope/celestial_cut_step1.py` restricted to the shadow
  locus.
- **Non-Archimedean kernel** `K_{q,d}(a) = (1-q^{-d})/[(1-q^{-a})(1-q^{-(d-a)})]
  = ζ_q(a)ζ_q(d-a)/ζ_q(d)`: verified by direct shell-sum computation over `F^×` (4000
  valuation shells each side) against the closed form, for several `(q,d,a)`, plus its own
  reflection and principal-series-positivity specializations. **Measure-convention warning,
  caught and fixed in this round**: normalizing multiplicative Haar measure so `vol(O^×)=1`
  gives every valuation-`v` shell `π^v·O^×` volume *exactly 1* (by translation-invariance of
  `d^×x`), **not** `(1-1/q)` — that `(1-1/q)` factor belongs to the different,
  additive-Haar-derived normalization. An earlier draft of the verification script used the
  wrong factor and would have "confirmed" a bug; caught before this write-up by deriving the
  closed form from the shell sum by hand first (see the script's inline comment) and only
  then coding it. **Not formalized in Lean at all**: Mathlib has no p-adic/non-Archimedean
  multiplicative Haar measure infrastructure (`grep -rli "padic.*haar\|haar.*padic"
  .lake/packages/mathlib/Mathlib/` returns zero hits at the pinned `v4.19.0` commit) — this
  is a genuine, separate Mathlib gap, not attempted.
- **`Γ_C(s) = Γ_R(s)Γ_R(s+1)`** (`Γ_R(s)=π^{-s/2}Γ(s/2)`, `Γ_C(s)=2(2π)^{-s}Γ(s)`): verified
  to `~1e-41`. This is Legendre's duplication formula in disguise — Mathlib already has the
  duplication formula itself (`Real.Gamma_mul_Gamma_add_half`, used this round for
  `Digamma.lean`'s `ψ(1/2)`), so this specific corollary is likely formalizable in a future
  round; not attempted here for time.
- **Eisenstein scattering coefficient** `c(Δ) = Λ(2-Δ)/Λ(Δ)` (`Λ(s) = π^{-s/2}Γ(s/2)ζ(s)`,
  the completed Riemann zeta function): verified `|c(Δ)|=1` to machine-`mpmath` precision on
  `Δ=1+iλ`, resting on the functional equation `Λ(s)=Λ(1-s)` (also verified). **This is a
  genuine automorphic Weyl/shadow structure containing completed zeta factors — it is NOT
  evidence toward RH.** Eisenstein series scattering already contains `ζ(s)` in its
  functional-equation normalization without that proving anything about its zeros; unit
  modulus on the critical line is a *convexity-strip regularity* statement about a ratio of
  functional-equation-related quantities, not a positivity statement about `ζ` itself.
- **Product-vs-ratio sanity check** (§7 of the paper): for a toy local factor `A(s)=Γ(s)`,
  `A(s)A(1-s) = |A(s)|²` and `A(1-s)/A(s)` has unit modulus on `Re(s)=1/2` — confirms the
  general algebraic pattern (product = norm/positive spectral data, ratio = Weyl
  intertwiner/scattering phase) the paper's §7 asserts, for this one example. Does **not**
  establish that the *specific* celestial Cutkosky kernel and the *specific* normalized
  PGL(2) Weyl intertwiner arise from the same underlying local factor `a_∞(s)` — that is
  §9's open problem, below.

## What is a genuinely open research problem (NOT attempted, per Daniel's own instruction)

These are the paper's own central targets, correctly distinguished from bookkeeping. Recorded
here rather than forced through with an axiom or a rushed partial version.

1. **§9, the local factorization problem** (the paper's own "most important falsifiable
   calculation"): does there exist a local analytic factor `a_∞(s)` with
   `C_∞(s) = a_∞(s)a_∞(1-s)` (the physical/celestial positive kernel) and
   `M_∞(s) = a_∞(1-s)/a_∞(s)` (the correctly-normalized real/complex Archimedean
   Knapp-Stein/Weyl intertwiner)? And does the analogous `a_p(s)` at an unramified `p`-adic
   place produce the standard local Euler factor *naturally*, with no fitting? **Not
   attempted.** This needs (a) the exact normalization convention for `M_∞(s)` in a fixed
   spectral convention — a literature/derivation task in its own right (Knapp-Stein
   intertwining operators for the real/complex principal series), and (b) solving the
   resulting functional equation for `a_∞`, which may or may not have a solution in
   elementary terms. No progress made beyond stating the question precisely.
2. **§10, Cutkosky vs. Rankin-Selberg**: does an explicit local intertwiner exist between the
   celestial principal-series completeness/Cutkosky pairing and a local Rankin-Selberg
   bilinear form (starting at GL(1) or spherical PGL(2), where every normalization is
   explicit)? **Not attempted.** The paper is explicit that the target is a commuting diagram
   or an equality of bilinear forms, not a verbal analogy — that computation has not been
   started.
3. **§4, the R₊ principal-series skeleton as an actual Lean object**: unitarity of the
   dilation operator `(U_a f)(x) = √a f(ax)` on `L²(ℝ₊,dx)`, its self-adjoint generator
   `D = -i(x d/dx + 1/2)`, the inversion `J`, and `J`'s action as `t↦-t` under the Mellin
   transform. **Not attempted in Lean.** This is real functional-analysis infrastructure
   (unbounded self-adjoint operators, the Mellin transform as a unitary map) that Mathlib has
   partial but not obviously sufficient support for; a genuine scoping pass (does
   `Mathlib.Analysis.InnerProductSpace`/`MeasureTheory.Function.LpSpace` plus whatever Mellin
   machinery exists cover this, or is it another from-scratch undertaking like digamma
   turned out not to be?) was not done this round for time, not because it was judged
   infeasible — flagged as the first thing to scope next.
4. **§6, the naive adelic product**: `∏_v K_{v,1}(s)` is explicitly NOT claimed to be a
   convergent adelic product here (finite-place factors like `∏_p(1-p^{-1})` and the fact
   that `ζ(s)` and `ζ(1-s)` do not have simultaneous absolutely convergent Euler products
   rule out the naive version). The correct construction needs the standard
   adelic/Tate/PGL(2) normalization and meromorphic continuation — not attempted; this is
   exactly Tate's thesis territory and is its own undertaking, consistent with round 2's
   already-documented "no digamma-adjacent Tate's-thesis-scale infrastructure attempted
   casually" discipline.

## Success / failure criterion (the paper's own, stated so it isn't quietly dropped)

**Succeeds** if an explicit normalization-preserving local diagram is produced showing the
physical Archimedean cut kernel and the automorphic Weyl/Rankin-Selberg structures arise from
the same local principal-series data (§9/§10, above).

**Fails cleanly** if the exact local intertwiners cannot be made compatible without inserting
extra arithmetic factors or changing the physical kernel by hand.

**Neither outcome has been reached.** This round established the local facts that are true
regardless of how §9/§10 resolve (reflection, positivity, the diagonal lift, the numerical
confirmation of every stated closed form) and named the open problems precisely. Recording
this honestly, per the paper's own instruction, rather than either forcing a premature
"succeeds" or quietly letting the hard part drop.

## Explicit non-claims (carried over verbatim from the paper's own scope list)

Not claimed, by this document or any Lean file in this repository: RH; Weil positivity from
Cutkosky positivity; equality of celestial and automorphic Hilbert spaces; equality of
Cutkosky and Rankin-Selberg pairings; a convergent naive product of local positive kernels;
`σ=s` (the dispersion-relation Mellin variable and the CFT1/Riemann `s` are kept distinct
throughout — no transform has been exhibited identifying them); that `ℝ₊` alone is a
complete CFT; that the physical cut measure is the representation-theoretic Plancherel
measure (the opposite point, established last round: `P(λ)=πλ/sinh(πλ)` is *not* that
Plancherel measure); or that the physical Cutkosky product is itself the normalized Weyl
scattering coefficient.

## Connection to existing work in this repository

```
ordinary Cutkosky -> celestial two-body phase space -> K_{∞,2}(Δ) -> dispersion -> K_{∞,1}(σ)
```
(`discovery/shadow_ope/`, prior rounds, independently reverified)

```
ℝ₊ Mellin -> CFT1/PGL2 principal series -> s↔1-s -> Δ=2s -> celestial shadow
```
(this document; the `s↔1-s` / `Δ=2s` link is proved in Lean, `ℝ₊`→CFT1 is not, per §4 above)

```
local celestial/physical kernel  ?=  local automorphic principal-series structure
```
is the new horizontal bridge under investigation; the question mark is intentional (§9/§10).

The earlier `discovery/shadow_ope/` investigation (shadow-pole mechanism, superseded; then
the Cutkosky-cut route, confirmed) is untouched by this front and remains the historical
record of what didn't and did work there.
