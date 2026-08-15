# Survey: `arithmetic_principal_series_RH_program34.tex` — every theorem-level result

Requested: "make sure you get everything in the arithmetic principal series too, whatever's
there." This is the complete inventory. The source is 9369 lines, 102 theorem-level
environments (`theorem`/`lemma`/`proposition`/`corollary`/`definition`), spanning §1
through the Conclusion plus a 40-item bibliography. Every environment was indexed by line
number and read in context; the table below classifies all 102.

## The paper's own final verdict (read in full, quoted exactly)

The Conclusion ends: **"No proof of global trace conservation or positivity is supplied
here. Therefore no proof of RH is claimed."** This is consistent, word for word in spirit,
with the abstract's "RH is not claimed" and with a route explicitly rejected in-text
(§"Why unitarity is insufficient...") as "only RH in different words." The paper's
discipline matches everything already found in GppVerify's own corpus-error audits — it
does **not** reproduce the root error pattern (treating a zero ordinate as a genuine
point-spectrum eigenvalue), and does not overclaim anywhere it was checked.

## Classification legend

- **TRACTABLE** — self-contained real/complex analysis, provable from off-the-shelf
  Mathlib with no paper-specific scaffolding beyond what a name or two requires.
- **APPARATUS** — depends on paper-specific custom objects (the BPY law and its density
  `q`, the four-field Euclidean realization, Wigner–Born distributions, Thorin–Stieltjes
  representations, Möbius–Koszul complexes, Hardy defect spaces, Cayley atlases,
  prime-Archimedean Gram matrices, causal commutator algebras, ...). Formalizing any one of
  these would require first building a substantial slice of the paper's own private
  framework — realistically its own multi-file thread, not an incremental addition.
- **DONE** — already formalized in `HeatTraceCriterion.lean` (this session or the prior
  one), in either this paper's exact form or a subset of it.
- **NO-GO / NEGATIVE** — a self-contained obstruction result. Often shorter than a
  positive result, and matches the "honest boundary" discipline this repo already
  practices, but still requires the same paper-specific objects to *state* (e.g. "the
  Wigner–Born distribution takes negative values" needs the Wigner–Born distribution to be
  defined first) — so tagged APPARATUS unless the statement is genuinely elementary once
  stripped of the object it's about.

## Full index (102 environments)

| Line | Kind | Name | Tag | Note |
|---|---|---|---|---|
| 376 | prop | (unnamed, `x^{s-1/2}=x^{it}`) | TRACTABLE-TRIVIAL | A one-line algebraic identity on `s=1/2+it`; too trivial to be worth a standalone Lean file — would appear only as a `have` inside a larger development. |
| 428 | thm | Exact survival amplitude | APPARATUS | BPY survival amplitude. |
| 481 | thm | BPY as a four-component free-field radial observable | APPARATUS | Four-field Euclidean realization. |
| 537 | prop | The fractional radial insertion is of negative type | APPARATUS | Needs the fractional radial insertion object. |
| 624 | thm | Noncircular Griffiths–Simon target | APPARATUS | Statistical-mechanics (Ising) target construction. |
| 766 | thm | Cumulant–Stieltjes equivalence | APPARATUS | BPY cumulants, Hankel matrices `H_N^{(0)}`. |
| 841 | cor | Canonical BPY Jacobi operator | APPARATUS | Depends on 766. |
| 906 | thm | Intrinsic BPY Hausdorff criterion | APPARATUS | Hausdorff moment sequences of BPY cumulants. |
| 1067 | thm | Exact BPY reflection identity | APPARATUS | BPY-specific functional identity. |
| 1227 | thm | Exact coordinate pullback and infinitesimal bridge | APPARATUS | Custom coordinate map. |
| 1295 | cor | A sufficient Weyl-positivity theorem for RH | APPARATUS | Conditional-on-a-kernel-hypothesis criterion; the kernel `𝒦_ω` is paper-specific. |
| 1363 | thm | Endpoint Laguerre–Nevanlinna equivalence | APPARATUS | Laguerre–Nevanlinna class membership. |
| 1503 | thm | Single-parity equivalence | APPARATUS | Half-line kernel Gram factorization. |
| 1659 | prop | Horizontal Born identity | APPARATUS | `\|Ξ(x+iy)\|²−\|Ξ(x)\|²` identity — closer to tractable, but the surrounding Born/Wigner framework is needed for it to mean anything in context. |
| 1734 | thm | Wigner–Bessel factorization | APPARATUS | Wigner–Bessel expansion, custom. |
| 1849 | thm | Exact Eisenstein–Born identity | APPARATUS | Eisenstein series + Born distribution. |
| 2018 | thm | Hudson obstruction | NO-GO/APPARATUS | Wigner–Born distribution takes negative values (cites Hudson 1974's classical theorem) — needs the Wigner–Born object defined first. |
| 2106 | thm | Globality of prime–Archimedean gluing | APPARATUS | |
| 2194 | prop | Surviving cusp source | APPARATUS | |
| 2229 | def | Thorin–Stieltjes representation | APPARATUS | Definition, not a theorem; needed by 2250, 2315, 2335. |
| 2250 | thm | Shifted Thorin criterion | APPARATUS | |
| 2315 | prop | The atom at 3/4 is impossible | NO-GO/APPARATUS | |
| 2335 | prop | The proposed critical-center tilt diverges | NO-GO/APPARATUS | |
| 2391 | thm | Prime-power coherent overlap | APPARATUS | |
| 2467 | thm | Exact regularized Euler determinants | APPARATUS | Regularized determinant of an operator `D(s)`, custom. |
| 2521 | prop | Different singular orders of the first two repetitions | APPARATUS | |
| 2635 | thm | Exact prime Green amplitude | APPARATUS | |
| **2765** | **thm** | **Exact Archimedean Laplace transform** | **PARTIAL — DONE (2 of 3 pieces)** | `⟨ν_∞,e^{−r·}⟩=A_∞(r)` via a digamma-difference identity (needs Mathlib's digamma — **confirmed absent from the pin entirely**, not even the function itself exists) plus two elementary exponential integrals. The two elementary pieces are now `archimedeanLaplace_aux_one`/`_two` in `HeatTraceCriterion.lean` (this session). The digamma piece is out of reach without building digamma from scratch — a separate, large undertaking, not attempted. |
| 2819 | thm | Completed massive-resolvent identity | APPARATUS | Depends on 2765's `A_∞` in full (including the digamma piece), so not reachable until that piece is closed. |
| 2914 | def | Completed arithmetic heat trace | DONE | The object `𝒦(t)` is exactly what `HeatTraceCriterion.lean` targets; the definition itself needs no proof. |
| 2946 | thm | Exact heat subordination | DONE (x=0 case only) | `subordination_at_zero` proves the `x=0` case. The general-`x` case is presented in the paper as "the standard subordination formula" (classical, cited without its own proof) — **confirmed absent from Mathlib** (no Bessel-K machinery at all in the pin) and **not proved here**. This is the single highest-value remaining target for Thread HT: a genuine `K_{1/2}`-Bessel evaluation, `∫₀^∞ t^{-1/2}e^{-at-b/t}dt=√(π/a)e^{-2√(ab)}`. A derivation sketch (an `a↔b` symmetric first-order-ODE argument via differentiation under the integral sign) was worked out this session but is real, substantial, multi-step analysis — not attempted as a rushed proof. |
| 2967 | thm | Heat-trace criterion for RH | DONE (structure only) | This is the RH ⟺ complete-monotonicity criterion Thread HT already targets; `CompletelyMonotone` is defined, Bernstein's theorem (needed for the criterion itself) is confirmed absent and scoped as Thread HT's own separate next thread. |
| 3014 | thm | Unconditional complex heat expansion | APPARATUS | Needs the involution-indexed zero multiplicity framework `F`, `ζ∼−ζ`. |
| 3073 | thm | One fixed Hausdorff sequence | APPARATUS | The two-grid sequence `b_n=𝒦(n+1)+𝒦(√2(n+1))` — tractable *definition*, but the theorem needs the full heat-trace criterion machinery to state its content. |
| 3183 | prop | Semigroup deflation gives a finite Gaussian witness | APPARATUS | |
| 3220 | cor | A filtered two-state determinant detects every quartet | APPARATUS | |
| 3267 | thm | Exact Gaussian Weil identity | APPARATUS | `c*Gc = ⟨𝒲, f_c*f̃_c⟩` — needs `𝒲` and the Gram matrix `G` built from `𝒦`. |
| 3299 | thm | Finite Gaussian criterion for RH | APPARATUS | |
| 3382 | thm | Arithmetic Osterwalder–Schrader criterion | APPARATUS | The OS reflection-positivity reformulation — needs OS axioms, not in Mathlib (same missing-subsystem class as elsewhere in this repo). |
| 3477 | prop | Reflection positivity is stronger than boundary unitarity | NO-GO/APPARATUS | |
| 3648 | prop | Real-place thermal identity | APPARATUS | |
| 3710 | def | Plancherel-regularized arithmetic heat trace | APPARATUS | A second heat-trace variant, `𝒦_P`. |
| 3732 | thm | Trace-class Plancherel criterion | APPARATUS | |
| 3854 | prop | Faithful but non-coercive preconditioning | APPARATUS | |
| 3954 | lem | Vertical-line reflection rigidity | APPARATUS | Exponential-polynomial zero-set rigidity; touches on entire-function theory that could in principle be elementary, but the specific exponential-polynomial family `P(z)=Σ(a_jz+b_j)e^{λ_jz}` used is paper-specific. |
| 3984 | thm | No vertical-line finite gamma approximation | NO-GO/APPARATUS | |
| 4032 | prop | HCM no-go | NO-GO/APPARATUS | Hyperbolic complete monotonicity does not imply the needed positive-definiteness — a real, self-contained mathematical fact, but framed entirely in terms of the paper's specific gamma density family. |
| 4059 | thm | Exact local Euler–shadow transfer | APPARATUS | Transfer-function/state-space realization, custom. |
| 4121 | thm | Exact paraorthogonal Euler block | APPARATUS | Paraorthogonal polynomial theory, custom family. |
| 4182 | prop | Excess local zero density | APPARATUS | |
| 4253 | prop | Scalar passive completion is impossible | NO-GO/APPARATUS | |
| 4318 | thm | Exact finite Möbius cancellation | APPARATUS | Finite Möbius-inversion matrix identity — closest to tractable finite linear algebra, but tied to the paper's specific `ℳ_{P,N}(s)` matrix family. |
| 4408 | thm | Finite critical-line Krein symmetry | APPARATUS | |
| 4457 | prop | No positive bulk reweighting | NO-GO/APPARATUS | |
| 4617 | thm | Exact finite cohomological cancellation | APPARATUS | Möbius–Koszul complex contractibility — genuine homological algebra, needs the complex defined first. |
| 4797 | thm | Exact global Möbius–Archimedean Schur complement | APPARATUS | |
| 4921 | thm | Exact co-Poisson boundary identity | APPARATUS | |
| 5017 | thm | Prime–Archimedean self-adjointness | APPARATUS | |
| 5097 | prop | Boundary self-adjointness is blind to nonreal zeros | APPARATUS | |
| 5174 | thm | Exact Hardy leakage criterion | APPARATUS | Hardy-space defect theory. |
| 5202 | lem | Localized anti-inner crossing | APPARATUS | |
| 5256 | thm | Boundary-crossing saturation | APPARATUS | |
| 5337 | cor | Hardy zero–one law and uniform Nehari gap | APPARATUS | Cites Nehari's theorem (classical, but the specific application is paper-built). |
| 5475 | thm | The defect space generates the pole parameters | APPARATUS | |
| 5576 | thm | One-state realization and exact cutoff law | APPARATUS | |
| 5664 | thm | Conservation of difficulty as coefficient precision | APPARATUS | |
| 5775 | thm | Explicit affine Cauchy coefficients | APPARATUS | Generalized Laguerre polynomial `L_n^{(1)}` coefficients — the Laguerre machinery itself is standard, but the "affine Cauchy coefficient" framing is paper-specific. |
| 5863 | thm | Affine scalar zero–one law | APPARATUS | |
| 5968 | thm | Uniform conditioning of the dyadic affine atlas | APPARATUS | |
| 6018 | prop | Cauchy–Laguerre bridge | APPARATUS | |
| 6107 | thm | Resonance conservation for an exact split | APPARATUS | |
| 6172 | prop | No scalar absolute-error stability | NO-GO/APPARATUS | |
| 6219 | thm | Exact causal Möbius inverse | APPARATUS | Convolution algebra of causal distributions. |
| 6430 | def | Exact finite prime–Archimedean Gram matrix | APPARATUS | |
| 6459 | prop | Parity and displacement structure | APPARATUS | |
| 6560 | thm | Exact finite self-adjoint prime–Archimedean core | APPARATUS | |
| 6655 | thm | Regularized determinant | APPARATUS | |
| 6871 | thm | Conditional compact-uniform closure | APPARATUS | |
| **6929** | **thm** | **Positive Gamma–Plancherel defect** | **CANDIDATE, NOT YET ATTEMPTED** | `∫₀^∞ e^{−qx}/(1−e^{−2x})dx`-type digamma integral for `q,a,b>0` — looks elementary on its face but likely needs the digamma-integral representation (same blocker as 2765's third piece). Worth a dedicated look in a follow-up session; not attempted this session for the same reason as 2765's digamma piece. |
| 6962 | thm | Exact Archimedean resolution of the Schoenberg defect | APPARATUS | |
| 7037 | thm | Exact Gamma–prime–pole decomposition | APPARATUS | |
| 7085 | thm | Ultraviolet support obstruction | NO-GO/APPARATUS | |
| 7162 | thm | Shifted causality criterion | APPARATUS | |
| 7243 | thm | Hodge closure criterion | APPARATUS | `ℤ₂`-graded Hilbert complex — genuine homological-algebra machinery, substantial to formalize independent of RH content. |
| 7328 | thm | The Gamma norm is fractional Sobolev | APPARATUS | Fractional Sobolev norm identification — the fractional-Sobolev machinery itself may exist in Mathlib in some form; not checked this session, flagged as a candidate for the same reason as 6929. |
| 7371 | prop | A prime homotopy leaves the Poisson domain | NO-GO/APPARATUS | |
| 7410 | thm | Two-prime exactness without a Hodge gap | APPARATUS | |
| 7444 | thm | Heat-regularized prime homotopy | APPARATUS | |
| 7494 | thm | Bilateral heat destroys Tate causality | NO-GO/APPARATUS | |
| 7548 | thm | Exact causal heat-boundary anomaly | APPARATUS | |
| 7660 | thm | The prime heat term is a causal commutator trace | APPARATUS | |
| 7745 | cor | Prime–Archimedean relative boundary trace | APPARATUS | |
| 7778 | thm | Trace-class generator limit and local real-place subtraction | APPARATUS | |
| 7887 | thm | Exact sine-transform normal form | APPARATUS | The paper's own "correct box functional" — central to its final unresolved step. |
| 7980 | thm | One-scalar cutoff-growth criterion | APPARATUS | |
| 8033 | cor | RH as conservation of boundary trace | APPARATUS | |
| 8099 | prop | Corrected sharp phase and the zero side | APPARATUS | Conditional on RH by its own statement (`Assume RH...`) — a conditional restatement, not a candidate for unconditional formalization. |
| 8152 | thm | The semilocal diagonal is a Fejér mean | APPARATUS | |
| 8365 | thm | Nyman–Burnol ghost cokernel | APPARATUS | Tate/adelic cohomology — same missing-subsystem class as elsewhere in this repo (adelic harmonic analysis). |
| 8446 | prop | The BPY Lee–Yang assertion is exactly RH | APPARATUS | States an **equivalence to RH itself** as a named proposition — not a step toward RH, a restatement of it in Lee–Yang language. Correctly not claimed as progress by the paper. |
| 8547 | thm | Fixed two-fermion moment criterion | APPARATUS | |
| 8633 | thm | Exact theta boundary Ward identity | APPARATUS | |

## What this session actually added

`archimedeanLaplace_aux_one`, `archimedeanLaplace_aux_two` in `HeatTraceCriterion.lean` —
the two elementary exponential-integral pieces of the "Exact Archimedean Laplace
transform" theorem (line 2765), proved by algebraic rewriting to `resolvent_laplace`
(already in the file) plus `MeasureTheory.integral_sub`. Both kernel-verified to
`[propext, Classical.choice, Quot.sound]` only.

## Why the other ~99 were not attempted this session, stated plainly

The overwhelming majority of this paper's content is inseparable from its own private
mathematical apparatus: the BPY probability law and its moments, the four-field Euclidean
field realization, Wigner–Born quasi-probability distributions, Thorin–Stieltjes
representations, finite Möbius–Koszul complexes and their cohomology, Hardy defect spaces
and Nehari-gap arguments, Cayley/Laguerre affine atlases, prime–Archimedean Gram matrices,
and causal-commutator trace algebras. Formalizing even one of these objects well enough to
*state* one of its theorems is comparable in scope to a full new GppVerify thread (compare
Thread S's `SignatureInertia.lean`, which took a full session to reach one theorem's
foundation). Attempting shallow versions of many of them in one sitting would produce
either wrong statements or vacuous ones — exactly the failure mode this repo's own
standing rules exist to prevent. The honest inventory above is the deliverable: every
result is now named, classified, and — where a concrete blocker exists (digamma absent
from Mathlib; Bessel-K absent from Mathlib; OS axioms, Tate/adelic cohomology, and
Möbius–Koszul cohomology all absent, matching blockers already recorded elsewhere in this
repo) — the blocker is named precisely rather than left as a vague "too hard."

## Two flagged candidates for a future session, ranked

1. **General-`x` subordination** (line 2946's cited classical identity) — the single
   highest-value target. Self-contained real analysis, no paper-specific apparatus, and it
   is the engine of the whole heat-trace reformulation (§ "the prime–Archimedean heat
   trace"). A derivation route (an `a↔b`-symmetric ODE argument via differentiation under
   the integral sign) was sketched but not attempted as Lean this session — it is
   substantial, multi-step analysis and deserves its own dedicated attempt, not a rushed
   one.
2. **Line 6929 / 7328** — two further candidates that *may* reduce to digamma or
   fractional-Sobolev machinery already worth checking for at the pin; not investigated
   this session beyond noting the resemblance to the blocked digamma piece of line 2765.
