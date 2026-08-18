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

## Follow-up: why the D3-regulator idea was doomed in general (not just that
specific choice), and one more ruled-out idea

Two further checks, both negative but each narrowing the search space with a
clean, general, transferable reason rather than a case-by-case failure:

- **General no-go for the whole "shift D3 by a small constant" family.**
  Any regulator of the form `D3 → ω6·C + X` (Feynman `iε`, a tiny mass, an
  exponential-damping/Schwinger regulator via `Γ(ν)/η^ν` — all checked)
  produces a Mellin transform whose `X`-dependence enters as `X^{Δ6-1}`.
  At the coincidence point `Δ6=1` this power is `X^0 = 1` **for every `X`,
  including `X→0`** — the regulator is algebraically incapable of touching
  that point, no matter which specific regulator is chosen. This rules out
  the entire class at once, not just the one `iε` choice tried first.
- **`iε` on `s` (the physical Mandelstam scale in `D2`) instead of `D3`:**
  `L`'s own residue at `Δ5=1` genuinely depends on `s` (not degenerate the
  way `D3`'s regulator was), so `Res[L]|_{s∓iε}` is a legitimate retarded/
  advanced pair. Checked numerically: their difference is
  `2iε/(A(s²+ε²)) → 0` linearly as `ε→0`, exactly the expected Sokhotski-
  Plemelj behavior *away from* the invariant's own threshold (`s=0`). This
  is the correct, unsurprising answer for our generic external `s≠0` — but
  it also shows this specific move can't be the resolution: `s` is a fixed
  external kinematic input here, not a variable being integrated over, so a
  discontinuity in it doesn't do anything unless `s` itself is later
  continued/integrated (it isn't, in this construction).

## Follow-up: tying legs 5,6 by crossing symmetry finds a genuine, finite,
verified Sokhotski-Plemelj discontinuity -- the first positive result

All three regularizations above shared an assumption: legs 5 and 6 are
independent celestial operators (separate `z5,z6`, separate `ω5,ω6`,
separate Mellin transforms). But "sewing" 5,6 should mean they're the two
ends of the *same* internal line, so crossing symmetry ties them:
`k6=-k5`. For null `q(z,z̄)` this forces the *same* celestial point
(`z6=z5`) and `ω6=-ω5`, reached by continuing `ω5` around `ω=0` — an
actual contour choice, not an inserted regulator. That collapses the two-
variable construction (whose coincident-pole pathology was ruled out
three separate ways) into a single-variable Mellin transform in `ω5`
alone, sidestepping the pathology rather than trying to regularize it.

Second, necessary change: use a **real Lorentzian celestial point**
(`z̄=z*`), not the independent complex `z,z̄` ("split signature") used
everywhere else in this thread's history, including the historical
manuscripts. With independent complex `z,z̄`, `D2`'s zero lands at a
generically *complex* `ω5` — off the real integration contour, so no
causal `iε` can do anything there (checked: the discontinuity trivially
vanished). With `z̄=z*`, `A,B,C` become genuinely real and `D2`'s zero
`ω5=-s/B` lands *on* the real axis — a genuine physical unitarity
threshold, exactly where `DispersionReconstruction.lean`'s proven
mechanism applies.

**Result** (`shadow_ope/tied_leg_continuation.py`): with both changes, the
retarded/advanced discontinuity across `D2`'s threshold converges to a
finite, `ε`-independent, nonzero limit that matches the exact closed form
`disc(Δ) = -2πi/(ACB)·w0^{Δ-3}` (`w0=-s/B`) to `~1e-10` relative error,
with the residual shrinking as `O(ε²)` (`4e-6→4e-12` as `ε` goes
`0.01→0.00001`) — clean convergence, unlike every regulator tried before,
which stayed pathological regardless of `ε`. Verified at two independent
kinematic points, not one.

**What this does and doesn't show**: this is a real, verified building
block — the first place in this whole investigation where a genuine
Sokhotski-Plemelj discontinuity survives the `ε→0` limit with a finite,
non-trivial, closed-form value, directly instantiating the mechanism
already proven abstractly in Lean. It is *not* a derivation of the box
integral. The other singularity of the tied-leg amplitude (a double pole
at `ω5=0`, from `D1` and the crossing-continued `D3` vanishing together)
is a standard soft/IR singularity — expected structure, not evidence of
anything new, and not yet treated. Also not yet done: the full inverse-
Mellin assembly back to real loop-momentum space, the `(z,z̄)` integral
that must supply `t`-dependence, and a numeric comparison of the fully
assembled result against the known box formula.

## Follow-up: integrated over the WHOLE principal series ("wherever the
internal operators sum to 2") -- converges to an exact closed form

Daniel's steer: the shadow-pair condition `Δ5+Δ6=2` is always satisfied on
the principal series `Δ=1+iλ` paired with its shadow `2-Δ=1-iλ`, so the
natural completion of the tied-leg result is to integrate `disc(Δ)` over
the *entire* principal series against the Plancherel measure — the exact
operation that diverged in every earlier attempt (`shadow_sewing.py`,
`dispersive_extraction.py`, `mandelstam_regulator_check.py`).

On the principal series, `w0^{Δ-3} = w0^{-2}·e^{iλ ln w0}` — a pure phase
times a fixed prefactor, so `|disc(1+iλ)|` is *constant* in `λ`: no
growth, no pole, anywhere on this contour. Multiplied by the exponentially
-decaying Plancherel measure, the sewing integral is manifestly absolutely
convergent — textbook convergence, unlike anything tried before.

Scanning the real integral inside against candidate closed forms at five
different `x` values matched *exactly* (ratio `=π` to 8 digits at every
point) to a standard Fourier-transform identity for the Plancherel kernel,
giving:

```
Sewn = -iπ/(2·A·C·B) · w0⁻² · sech(ln(w0)/2)²      (w0 = -s/B)
```

Verified against **direct numerical quadrature of the λ-integral** (a
second, independent check beyond the earlier `ε→0` discontinuity
verification) to `~1e-30` relative error at **three** independent
kinematic points (`shadow_ope/principal_series_sewing.py`). Cutoff-
robustness checked too (`λ∈[-20,20]` vs `[-80,80]`: identical to 15
digits).

**What this shows**: the tied-leg / real-Lorentzian-slice construction
gives a finite, closed-form, non-singular value for the `D2`-threshold's
contribution to the shadow-pair sewing integral, integrated over the
*entire* principal series — the operation whose divergence this whole
sandbox exists to investigate now converges cleanly with an exact answer.

**What this doesn't show**: still only the `D2`-threshold piece, at one
fixed celestial point `z` (not integrated over the sphere). The `ω5=0`
soft/IR double pole and the `(z,z̄)` integral supplying `t`-dependence are
both still missing. No claim that `Sewn` equals any piece of the box
integral — a finite, doubly-verified closed form, nothing more asserted.

## Follow-up: the soft pole turns out to already be handled, and a sharp
(rigorous, not structural-argument-only) limit of the current toy model

Two more checks, closing out the loose ends listed above:

- **The `ω5=0` soft/IR double pole does not contribute to `disc(Δ)` at
  all.** Checked directly: evaluating the retarded-minus-advanced
  discontinuity at three different `Δ` in the convergence strip `(2,3)`
  (`2.1`, `2.5`, `2.9` — the strip's lower edge `Δ=2` is exactly where the
  soft pole lives) gives the *same* closed form at every point, with no
  sensitivity to how close `Δ` sits to the soft endpoint. The soft
  singularity is present identically in `M_ret` and `M_adv` (it doesn't
  depend on `D2`'s `iε` at all, since it comes from the `ω→0` endpoint,
  not the `D2` threshold) and therefore cancels exactly out of the
  difference. **The closed form already found is the complete `D2`-
  threshold answer** — no separate soft-pole treatment needed.

- **Rigorous (not just structural) confirmation that `t` cannot appear in
  this toy model, ever.** The exact kinematic identity `p1+p2+p3=-p4`
  (verified directly from `make_kinematics`, not assumed) forces
  `D3=(k5+p1+p2+p3)²=(k5-p4)²=-2k5·p4` — `p3`'s dependence cancels
  *identically*, not approximately. This means no `(z,z̄)` integral of the
  *current* construction (4 ordinary momenta + 1 sewn pair) can ever
  produce `t`-dependence, regardless of measure or contour: `t` genuinely
  never appears in `D1,D2,D3` as functions of the sewn variables. Reaching
  the actual box requires promoting legs 1–4 to genuine celestial
  operators too (a full 6-point treatment with cross-ratios among all six
  `z_i`), not extending the current one-sewn-pair construction.

## Status

Not converged, but sharpened twice, then genuinely advanced twice, then
clarified once more: the `D2`-threshold closed form (`Sewn`, above) is now
known to be *complete* for what it computes, and it's now rigorously
established that the current construction is structurally incapable of
ever reproducing `t`-dependence — the honest next frontier, if this is
pursued further, is a genuine 6-point all-celestial treatment (all six
`z_i` as operators, cross-ratio-dependent conformal blocks), which is a
substantially larger undertaking than anything attempted in this sandbox
so far. This sandbox has verified one real, non-trivial building block
(the `D2`-threshold Sokhotski-Plemelj discontinuity, closed-form, doubly
verified) toward the shadow-discontinuity mechanism at one loop, for one
specific propagator of one specific tree topology. It has not shown, and
does not claim to show, anything about the mechanism at higher loop
orders or non-perturbatively — extending the general `L`-loop structural
pattern already proved unconditionally in `TreeLoopSewing.lean`
(`pairSewing_cycleRank`) to genuine analytic content, pair-sewing by
pair-sewing with this now-working mechanism, is itself an open, likely
multi-session research program, not something this pass has attempted. Three regularization ideas ruled
out now (one of them — the D3-shift family — ruled out *in general*, for
every regulator of that shape, not case by case), each for a clear,
recorded reason rather than a dead end. The pattern across all three: any
fix has to act on whatever variable is genuinely being varied/integrated in
the reconstruction (the `Δ5,Δ6`/`λ` contour itself, or the eventual `ℓ²`),
not on `D3` additively and not on a fixed external Mandelstam invariant.
Two live hypotheses remain, neither attempted yet: (1) the not-yet-included
`(z,z̄)` conformal-block factor supplies compensating structure once the
full construction (not just the energy/Mellin sub-integral) is assembled;
or (2) the Sokhotski-Plemelj `iε` belongs on the final assembled `1/ℓ²`
propagator after reconstruction (matching `DispersionReconstruction.lean`'s
proven mechanism directly), not on any intermediate Mellin-space object.
