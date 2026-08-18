# discovery

Search-and-discovery sandbox for the Tree-Loop-Sewing thread — deriving loop
integrands from celestial-holographic tree amplitudes via shadow
discontinuities. Same convention as [`weil-decay`](https://github.com/GoldenPhysicsProject/weil-decay):

**Discovery only. Nothing here is proved.** This is numerical/symbolic
exploration, versioned so it survives across sessions instead of living only
in an ephemeral scratchpad. Anything that solidifies into an unconditional or
honestly-conditional result graduates to `GppVerify/CelestialHolography/` for
Lean 4 formalization, with the conditional hypotheses named explicitly (see
`ShadowPairSewing.sewing_identity`'s H1/H2/H3 in
`GppVerify/CelestialHolography/TreeLoopSewing.lean` and the Sokhotski-Plemelj
mechanism in `DispersionReconstruction.lean`).

## The question

`ShadowPairSewing.sewing_identity` needs a genuine derivation of the
shadow-pair pole `⟨O_Δ5 O_Δ6⟩ ∝ 1/(Δ5+Δ6-2)` from an actual two-point
function / OPE computation for the six-point comb tree (legs
`A(5,1)-B(2)-C(3)-D(4,6)`), not an asserted pole. `shadow_ope/` attempts this
from scratch: real kinematics, real Mellin transforms, nothing inserted by
hand.

## What's been found so far

- `shadow_ope/celestial_kinematics.py`: verified celestial null-vector
  kinematics for the comb tree (symbolic dot-product identity, explicit
  massless 4-momenta).
- `shadow_ope/shadow_sewing.py`: the naive real-`λ` SL(2,ℂ) Plancherel
  completeness-relation sewing is **ill-defined as literally written** for
  this tree ordering — leg 6's Mellin transform is a delta function
  supported exactly at `λ=0`, which is exactly where leg 5's Mellin
  transform has a genuine simple pole. A zero-width delta multiplying a
  simple pole is not a number. This is not a dead end: it is the
  identification of exactly where the missing analytic step (deforming off
  the real locus, dispersive reconstruction) must act.

- `shadow_ope/dispersive_extraction.py`: attempted the regularization.
  Two results, one structural and confirmed, one a ruled-out attempt:
  - **Confirmed structurally** (not asserted): `t=(p2+p3)²` appears in
    none of `D1,D2,D3` — `p3` never enters except via the momentum-
    conservation identity used to rewrite `D3`. Whatever produces the
    box's `t`-dependence has to come from the `(z,z̄)` conformal-block
    integral, which this toy model deliberately hasn't included yet.
  - **Tried and ruled out**: giving `D3` a Feynman `iε` (`D3 → ω6·C ∓ iε`)
    does turn leg 6's Mellin transform into a genuine meromorphic function
    of `Δ6` everywhere `Δ6≠1` (verified against direct quadrature to
    `~1e-15`). But exactly at the coincidence point `Δ6=1`, the `ε`-
    dependent prefactor is `(∓iε)^0 = 1` for *every* `ε` — the regulator
    has literally zero effect there. Retarded and advanced come out
    identical; the pole at `Δ6=1` survives untouched. This regularization
    doesn't fix the collision, it just re-packages "delta(λ) times a pole"
    into "pole times a pole at the same point." A second, independent
    check (deforming the shadow condition itself, `Δ5=1+δ+iλ`,
    `Δ6=1-δ-iλ`) confirms the divergence is genuine, not a scheme
    artifact: for any `δ>0` the sewn integral is identically 0 (R misses
    the coincidence point entirely), and only at `δ=0` does it hit
    `L(1)·(finite coefficient)` — but `L` itself has a real pole at
    `Δ5=1`, so the naive limit is a genuine `∞·finite`, not a removable
    singularity.

## Status

Not converged, but sharpened. The naive completeness-relation sewing's
divergence is now confirmed genuine by two independent methods, not a
regularization-scheme artifact. Two live hypotheses for where the actual
fix lives, neither attempted yet: (1) the not-yet-included `(z,z̄)`
conformal-block factor supplies compensating structure that cancels the
divergence once the full construction (not just the energy/Mellin
sub-integral) is assembled; or (2) the Sokhotski-Plemelj `iε` belongs on
the final assembled `1/ℓ²` propagator after reconstruction, not on the
intermediate Mellin-space objects `L`, `R`.
