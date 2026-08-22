# discovery/cutkosky_weil — Local shadow kernels and the finite-prime Weil kernel

Research-front notes for the 2026-08-22 directive: "celestial Cutkosky positivity →
local shadow kernels → finite-prime Weil kernel → Casimir compression → global Weil
positivity → RH." Same convention as `discovery/local_field_shadow/` and
`discovery/shadow_ope/`: **discovery only, except where explicitly noted as formalized
in Lean.** Read this file first; `cutkosky_weil_verify.py` is the numerical companion,
rerun fresh in this container.

## The central question, answered

Daniel's own closing instruction for this round was: *"What physical/mathematical
projection turns `K_p` into `K_p−1` while preserving positivity globally? If we find
that projection from the Cutkosky completeness structure, then we have something
genuinely different from simply importing somebody else's RH machinery."*

**Direct answer: at the single-prime level, no such projection exists.**

`K_p(θ) = Σ_{n∈ℤ} r^{|n|} e^{inθ}` (`r = p^{-1/2}`, `θ = t log p`) is the classical
Poisson kernel on the circle. By the Herglotz/Bochner theorem, a Fourier-coefficient
sequence is positive-definite (equivalently: every truncated Toeplitz matrix built from
it is positive semidefinite) exactly when it is the Fourier series of a nonnegative
measure. `K_p`'s coefficient sequence `(r^{|n|})_n` is termwise nonnegative, so it is
automatically positive-definite — this is just the statement that the Poisson kernel is
a positive measure (an approximate identity), and it is why `Kp_pos` (§ below) is a
one-line consequence of the geometric series / cosine bound.

`K_p − 1` removes exactly the `n = 0` (DC / "vacuum") Fourier coefficient — the sequence
becomes `(r^{|n|})_{n≠0}`, `0` at `n = 0`. We tested directly whether this vacuum-
subtracted sequence remains positive-definite by building the truncated
`(2N+1)×(2N+1)` Toeplitz matrix `T[j,k] = c_{j−k}` for both sequences and computing
eigenvalues numerically (`mpmath.eig`, `N = 6`, dimension 13, primes `p = 2, 3, 5`):

| p | K_p min eig | K_p max eig | K_p−1 min eig | K_p−1 max eig |
|---|---|---|---|---|
| 2 | 0.128157 | 4.56496 | **−0.871843** | 3.56496 |
| 3 | 0.268444 | 3.31876 | **−0.731556** | 2.31876 |
| 5 | 0.38799  | 2.46752 | **−0.61201**  | 1.46752 |

`K_p`'s matrix is strictly positive definite in every case, exactly as expected. `K_p−1`'s
matrix has a strictly negative eigenvalue in every case — it is indefinite, not merely
"not yet shown positive." The vacuum subtraction **necessarily destroys**
Toeplitz/Bochner positive-definiteness at the single-prime level, for every prime
tested, at every truncation size checked.

**What this means for the research program.** This is a precise, informative *negative*
result, not a breakthrough and not a step toward RH. It says the naive local mechanism —
"maybe `K_p − 1` is itself already a positive kernel, prime by prime, via some Cutkosky-
completeness-relation-flavored projection" — does not exist. It does **not** rule out
global positivity of the full quadratic form `Q_GPP[f] = Q_∞[f] + Σ_p Q_p[f]`: a sum of
many individually-indefinite local pieces can absolutely be globally positive-definite
(this is exactly the situation in the classical Weil explicit formula, whose individual
prime terms are not sign-definite either — positivity, if it holds, is a genuinely
collective, cross-prime-and-Archimedean phenomenon there too). So the honest reading is:
Cutkosky's positive completeness relation `Σ_X |X⟩⟨X|` may still constrain the *global*
sum in a way that a single local factor cannot exhibit, but that global mechanism (if it
exists) is not visible, and cannot be found, one prime at a time. Any future attempt at
item 6 of the directive (a direct positivity factorization `Q[f] = |Af|²`) has to operate
on the assembled `Q_GPP`, not on any single `K_p − 1`.

## What's proved in Lean (`GppVerify/RiemannHypothesis/CutkoskyWeilBridge.lean`)

- `Kp (p t : ℝ) : ℝ` — the finite-place shadow kernel in real closed form,
  `(1−p⁻¹)/(1 − 2p^{−1/2}cos(t log p) + p⁻¹)`.
- `Wp (p t : ℝ) : ℝ := log p · (Kp p t − 1)` — the vacuum-subtracted, log-weighted kernel
  (definition only; no positivity claimed or provable, per the finding above).
- **`Kp_pos`**: `1 < p → 0 < Kp p t` for all real `t`. Unconditional, no axiom.
- `cutKernel (t : ℝ) : ℝ := t / (4 sinh(2πt))` — the celestial cut, already derived
  elsewhere in the tree.
- `H (t : ℝ) : ℝ := (t² + 1/4) · cutKernel t` — the Casimir-weighted Archimedean kernel.
- **`H_nonneg`**: `0 ≤ H t` for every real `t`. Unconditional, no axiom. Proof: `t` and
  `sinh(2πt)` always share sign, so the ratio is nonnegative; the `t=0` case is the junk
  value `0/0=0` in Lean's total division, itself `≥0`.

**Not formalized in Lean this round** (numerical-verification-only — see script,
sections 1–4): the full Poisson-series `HasSum`/`tsum` expansion of `K_p` (item 1's
series form — standard, not novel, deferred to preserve effort for the genuinely new
Toeplitz finding above); the exact Fourier pair `H(t) ↔ G(x) = 3/(512π)sech⁴(x/4)`
under the convention `G(x) = (1/2π)∫H(t)e^{itx}dt` (item 2 — confirmed numerically to
~1e-51 relative error at three sample points, a genuine Lean proof would need Mathlib's
Fourier-transform-of-sech⁴ machinery, not confirmed to exist); the removable-singularity/
pole-cancellation claim at `t=±i/2` as a formal complex-analytic regularity theorem
(item 2 — confirmed numerically via a shrinking-perturbation sequence converging cleanly
to a finite value, no formal residue calculus done). These remain honest open items, not
silently dropped.

## Item 3 — the Casimir operator's representation-theoretic origin

Not attempted as a Lean construction this round. The precise missing interface: Mathlib
(pinned `v4.19.0`) has no development of the principal-series representations of
`SL(2,ℝ)` or their Casimir/Laplace–Beltrami operator eigenvalues — the `t²+1/4` factor
here is used purely as a *number* (the known eigenvalue), not derived from an actual
operator on a Hilbert space of sections. Building the operator itself (unitary principal
series, the Casimir as a differential operator, its spectrum) is a separate,
substantial representation-theory undertaking, not a small gap-fill. Naming this
explicitly rather than papering over it with an axiom asserting the eigenvalue relation.

## Item 4/5 — `Q_GPP` construction and comparison to the classical Weil form

Not attempted this round beyond the single-prime diagnostic above. Before building
`Q_GPP[f] = Q_∞[f] + Σ_p Q_p[f]` and comparing it to the classical Weil explicit-formula
quadratic form, it is necessary to be precise about which object `WeilPositivityCriterion.lean`
already contains: **`GppWeilCriterion.pairedForm`** there is an *abstract* pairing
`Σ_{ρ∈S} conj(c(ι ρ))·c(ρ)` over finite subsets of the actual (unknown) nontrivial-zero
set — it is not the classical prime-sum quadratic form this directive's `Q_GPP` is meant
to build. `rh_iff_weil_pairedForm_nonneg` is a real, unconditional, already-proved
biconditional, but bridging it to a prime-side construction like `Q_GPP` requires the
classical Weil explicit formula itself (the integral-transform identity relating a sum
over zeros to a sum over primes plus an Archimedean term) — substantial, separate
infrastructure, not present in Mathlib, and not attempted here. Per the directive's own
explicit warning ("do not call two objects identical because their Fourier multipliers
look alike"), no such identification is made or assumed anywhere in this round's work.

## Item 9 — Connes–Consani / Selberg / Mayer / Tate / Knapp–Stein

Not used as machinery anywhere in this file or script. `K_p` and `H` here are derived
purely from the GPP local-field-shadow-kernel route (already in the tree) and the
celestial-cut kernel (already in the tree); no operator, projection, or identity was
imported from the Connes–Consani program. The single-prime Toeplitz computation above is
original to this session, run independently, not cross-checked against or motivated by
their scaling-trace construction.

## Explicit non-claims

- **No RH claim, conditional or otherwise.** `rh_iff_weil_pairedForm_nonneg` (pre-
  existing) states an equivalence between RH and an abstract nonnegativity condition on
  an unknown set (the actual zeros); nothing in this round establishes that condition.
- **No claim of global Weil positivity** for any constructed quadratic form — no such
  form was even assembled this round.
- **No claim that `K_p − 1` is positive**, locally or globally — the opposite was shown
  at the single-prime level.
- **No import of Connes–Consani's compression operator** or any external RH program's
  machinery as a black box.
- The golden-ratio/modular results (`GoldenRatioHyperbolicSector.lean`, prior round) are
  unrelated exact structural facts and are not used here to argue toward positivity.

## Reproducing

```
python3 cutkosky_weil_verify.py
```
No network access required; pure `mpmath` (dps=50), runs in well under a minute.
