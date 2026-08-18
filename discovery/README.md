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

## Follow-up: t doesn't need the full 6-point rebuild after all -- a
different comb ordering gets there with the SAME machinery

The "t can never appear" finding was about *this specific* comb ordering
(`5-1-2-3-4-6`), not about the construction in principle. Tested the
obvious alternative before assuming the full 6-point-all-celestial
rewrite was required: swap which legs sit next to the sewn leg. Ordering
`5-2-3-1-4-6` (comb `A(5,2)-B(3)-C(1)-D(4,6)`) gives:

```
D1' = (k5+p2)²          = ω5·A'          (A' = 2q·p2)
D2' = (k5+p2+p3)²       = ω5·B'' + t     ((p2+p3)² = t exactly)
D3' = (k5+p2+p3+p1)²    = -ω5·C          (unchanged -- D3 only ever sees
                                           p4, by the same momentum-
                                           conservation identity,
                                           regardless of how 1,2,3 are
                                           ordered among themselves)
```

Ran the *exact same* verified machinery (tied legs, real Lorentzian
slice, causal `iε` on the affine propagator, principal-series
integration) with `(A,B,s)→(A',B'',t)`. Both independent checks pass at
the same precision as the `s`-channel result (`shadow_ope/
t_channel_sewing.py`): the discontinuity matches its closed form to
`~1e-9`, and the principal-series integral matches its `sech²` closed
form to `~1e-31`, at two independent kinematic points.

```
Sewn_t = -iπ/(2·A'·C·B'') · w0_t⁻² · sech(ln(w0_t)/2)²    (w0_t = -t/B'')
```

Genuinely `t`-dependent, doubly verified. One thing noted honestly, not
explained yet: the sign of the imaginary part is *opposite* `Sewn_s`'s at
the same kinematic point.

**Not yet shown**: whether `Sewn_s` and `Sewn_t` combine into anything
resembling the box formula's crossing-symmetric `Li₂(1-s/t)+Li₂(1-t/s)`
structure. That comparison isn't meaningful yet, because both are still
functions of one fixed `z` — the `(z,z̄)` integral is still missing from
both channels.

## Follow-up: direct attempt at the actual open problem (the kinematic
block `K_1(λ;s,t)`) -- a genuine new result, and an honest, informative
negative

Reading the full source material (see the conversation record) located
the precise open problem: the target is
`I_4^shadow(s,t) = ∫dλ/2π P(λ) K_1(λ;s,t)`, where `K_1` is a single
kinematic conformal block jointly dependent on both `s` and `t` — not a
sum of separately-`s`- and separately-`t`-dependent pieces the way
`Sewn_s`/`Sewn_t` above were built. Every source read (both ONON drafts,
the compact companion paper, and the paper specifically devoted to
developing `K_1`) states this derivation as open; the dedicated
companion's own words: *"The derivation is open and is claimed nowhere
in this paper."*

**A genuine new result** (`shadow_ope/kinematic_block_attempt.py`, Part
1): no source pins down the cross-ratio `z` as an explicit function of
`s,t` for this specific six-point construction. Derived it directly from
this session's own verified null-vector kinematics — extract each
external leg's celestial position (`z_1→∞` in this frame; handled via
the standard cross-ratio limit) and compute the 4-point cross-ratio.
Result, verified **exactly** (not approximately) at four independent
`(s,t)` points: `z(s,t) = s/(s+t)`. Nobody had written this down for this
construction; it's real, checkable progress.

**An honest negative, with a concrete diagnosis** (Part 2): assembled a
first candidate `K_1` from the now-proven conical-block reduction
(`k_h(z)`, proven in the kinematic companion) and the scalar 3-point OPE
coefficient, using `z̄=z` (real, from the chart above). It does **not**
reproduce the box — and diagnostically, `K_1(λ)` isn't even in `λ`,
which it should be (swapping `λ→−λ` swaps which of `Δ5,Δ6` is which, a
symmetry the true construction should respect). That points at what's
missing: the Temperedness Theorem's cancellation mechanism needs a
genuine complex `z̄=z*` (unit-circle) evaluation, not the real `z̄=z`
this chart gives; and/or an explicit shadow-symmetrization step the
dedicated companion's own strategy calls for and this first pass
skipped.

**Status of the central question**: not resolved, honestly. This is a
real, bounded attempt at the actual open problem, not a completed
derivation, and not a deflection either. The cross-ratio result is a
genuine, reusable piece; the assembly failure is diagnosed, not just
observed, and points at two concrete next things to try.

## Status

Not converged, but genuinely advanced several times in a row now. Recap of
where each open question currently stands:

- **The original coincident-pole divergence** (naive completeness-relation
  sewing, `shadow_sewing.py`): resolved for one propagator's threshold by
  tying legs 5,6 via crossing symmetry and working on a real Lorentzian
  celestial slice, rather than by any of the three regulators tried and
  ruled out first (Feynman `iε`/mass/Schwinger-damping on `D3` — ruled out
  *in general*, for every regulator of that shape, not case by case — and
  `iε` on the fixed external Mandelstam `s`, inert for the standard
  reason). The pattern behind all three failures: a fix has to act on
  whatever is genuinely being varied/integrated in the reconstruction, not
  on `D3` additively and not on a fixed external invariant.
- **The `D2`-threshold discontinuity, integrated over the whole principal
  series** (`Δ5+Δ6=2`): finite, closed-form, doubly verified
  (`Sewn_s`, `tied_leg_continuation.py` / `principal_series_sewing.py`).
- **The `ω=0` soft/IR pole**: confirmed to cancel out of the discontinuity
  automatically — `Sewn_s` is already the complete `D2`-threshold answer,
  nothing further needed there.
- **`t`-dependence**: *not* structurally impossible as first thought — that
  was specific to the one comb ordering tried first. A different ordering
  (`5-2-3-1-4-6`) reaches a genuinely `t`-dependent threshold with the
  *same* verified machinery, giving `Sewn_t`, doubly verified at the same
  precision as `Sewn_s` (`t_channel_sewing.py`).

## Follow-up: attempted the `(z,z̄)` integral -- a genuine, clean log
divergence, with a plausible (unverified) physical reading

Ran the natural next step: integrate `Sewn_s(z)` over the celestial
sphere (real slice, `z=x+iy`, `q(z,z*)=(1+x²+y², 2x, 2y, 1-x²-y²)`).
Grid-scanned first — smooth and finite everywhere checked. Then checked
the large-`|z|` falloff directly (an earlier hand estimate for this
guessed `1/r⁴`; computing it instead of trusting the guess showed that
was wrong): `|Sewn_s(z)| ~ K/r²` as `r→∞`, with `K` a **universal
constant independent of angle** — checked at 6 different angles, all
converging to the same `K≈0.26` (`shadow_ope/z_integral_attempt.py`).
Makes sense structurally: at large `|z|`, `q(z,z*)` is dominated by its
leading `r²` piece regardless of direction, so `A,B,C` all approach the
same asymptotic ratio.

**Consequence**: the flat-measure integral `∫d²z |Sewn_s(z)|` is a
confirmed, clean **logarithmic divergence** at large `z` — not a
numerical artifact, a directly verified `1/r²` falloff with an isotropic
coefficient.

**A plausible reading, explicitly flagged as a hypothesis, not verified**:
the known massless box integral is itself only finite after IR
regularization in the fully massless case (the historical manuscripts
audited earlier in this thread's history say so explicitly, in their own
box definition). A log-divergent `z`-integral is at least *consistent*
with reproducing that same IR structure, rather than evidence the
construction is wrong. Confirming that (versus it being an artifact of
the wrong measure choice) would need the divergence's coefficient
compared against the box's known IR-divergent piece in a matching
regularization scheme — not attempted.

**Explicitly still open**: whether the *flat* measure `d²z` is even the
right one for this specific completeness-relation context — a different,
standard celestial-CFT convention (a conformal weight factor like
`(1+|z|²)⁻²` for a weight-`(1/2,1/2)` primary) would change convergence
entirely, and no settled derivation of which applies here has been done.

**What's still open**: whether `Sewn_s` and `Sewn_t` combine (once the
still-missing `(z,z̄)` integral is done on both) into anything resembling
the box formula's crossing-symmetric structure. The sign difference
between them is now confirmed *robust*, not an accident of one kinematic
point: checked at 5 independent `(s,t,z)` points, `Sewn_s`'s prefactor
sign is `-1` and `Sewn_t`'s is `+1` at every single one where both land
on the physical branch. A consistent relative sign between two channel
orderings is exactly the kind of structure a genuine crossing-symmetric
assembly would need — worth taking seriously as a real clue, though *why*
it's always exactly this sign is not yet derived, only observed. And, at
a much larger scale, whether any of this generalizes
beyond one loop or one topology. This sandbox has verified several real,
doubly-checked building blocks toward the shadow-discontinuity mechanism
at one loop, for two thresholds of one tree topology. It has not shown,
and does not claim to show, anything about higher loop orders or
non-perturbative completeness — extending the general `L`-loop structural
pattern already proved unconditionally in `TreeLoopSewing.lean`
(`pairSewing_cycleRank`) to genuine analytic content, pair-sewing by
pair-sewing with this now-working mechanism, is itself an open, likely
multi-session research program, not something attempted here.

## Follow-up: `K1(λ;s,t)` attempt 2 -- found and fixed a real shadow-weight
bug (λ-parity now holds); box reproduction improved from "wildly wrong" to
"right order of magnitude, wrong normalization"

A careful re-read of the residue formula as it actually appears across the
historical source manuscripts (not from memory) turned up a concrete,
checkable bug in the first `K1` assembly attempt. The residue at the
shadow pole is `R(Δ5) = C_{12,Δ5}·C_{34,2-Δ5}·F4(Δ1,Δ2,Δ5;u)·F4(Δ3,Δ4,2-Δ5;v)`,
with `F4` the *ordinary* 4-point conformal block
`F4(Da,Db,D;w)=w^{(D-Da-Db)/2}·₂F₁(D/2,D/2;D;w)` — not the plain chiral
block `k_h(z)=z^h·₂F₁(h,h;2h;z)` used the first time. For external
`Δ=1` on all four legs this reduces to `F4(1,1,D;w)=w⁻¹·k_{D/2}(w)`, which
means leg 6 (`Δ6=2-Δ5`) must use block weight `1-h`, **not the same `h`**
as leg 5. The first attempt used `k_h(z)·k_h(z)` (same weight twice) —
structurally wrong, and it is exactly this bug, not "need genuine complex
`z̄=z*`" as originally guessed, that explains the earlier finding that
`K1(λ=+1)` and `K1(λ=-1)` weren't simply related: `k_h(z)²` is not
manifestly even under `λ→-λ` (which swaps `h↔1-h`), while the corrected
`K1_v2(λ) = C(λ)·z⁻²·k_h(z)·k_{1-h}(z)` is — verified numerically even to
>20 digits at four test points (`shadow_ope/kinematic_block_attempt2.py`).

With the fix and `u=v=z` (same cross-ratio in both blocks, the simplest
choice), the spectral integral lands within `0.34×`–`6.96×` of the exact
box at five spacelike (`z∈(0,1)`, box manifestly real) kinematic points —
a completely different regime from before (previously off by orders of
magnitude, occasionally underflowing to numerical zero). Real, if
incomplete, progress: right parity, right order of magnitude, real-valued
in the physical region, but not numerically correct.

Tried the standard crossing choice `v=1-z` instead of `v=z` next — did
not improve agreement, but was diagnostically useful: the spectral
integral's *value* barely moves across the five very different `(s,t)`
points (~0.55–0.67 throughout) while `box_exact` varies by more than
`10×` across the same points. That is a clean signal that what's missing
is not another guess at `u,v` but an entire **(s,t)-dependent overall
prefactor or Jacobian**, currently absent from the construction —
plausibly the `(ω5,ω6)→(σ,λ)` energy-Jacobian from the loop-measure
derivation (dropped here by only integrating over `λ` at fixed `z`), or
the round-sphere measure `dz dz̄/(1+zz̄)²` that at least one source's own
loop-measure derivation uses for the transverse/z-integration — which
would mean `z` itself should be an *integration variable* alongside `λ`,
with the `s,t`-dependence entering through the integration domain rather
than by plugging a fixed `z=s/(s+t)` into the blocks. Not yet tried.

## Follow-up: an exact, confirmed scaling law the construction must satisfy
-- and two cheap candidate fixes tried and ruled out

Chased the missing-prefactor diagnosis to a precise statement
(`shadow_ope/kinematic_block_scaling.py`). `K1_v2` depends only on the
scale-invariant ratio `z=s/(s+t)`, so its spectral integral `I(z)` is
invariant under `(s,t)→(c·s,c·t)`. But `box_exact` has mass dimension `-2`
and its own closed form shows `box_exact(s,t)=H(z)/(s+t)²` for some
function `H`. So `I(z)/box_exact` must scale as exactly `c²` at fixed `z`
— checked holding `z=0.6` fixed across four different overall scales
(`s+t ∈ {-5,-10,-15,-50}`): `ratio/(s+t)²` is constant to all 10 digits
shown in every case (`0.03813598329...`). **Confirmed, not approximate**:
the construction is missing an overall `(s,t)`-dependent prefactor of
exactly this weight — plausibly the `1/(ω5 ω6)` energy factor every
source's general derivation carries and that this construction (fixed
chart point, λ-only integral) has been dropping.

That fixes the *scale* but not the *shape*: the residual
`ratio/(s+t)²`, now genuinely a function of `z` alone, still varies by
more than an order of magnitude across six `z` values tested (`0.038` to
`2.25`) — a real, unresolved shape mismatch. Two cheap candidate fixes
were tried and **both ruled out**: (a) scanning a single power `z^p`
multiplying `K1_v2` for `p∈{-3,...,1}` — best case (`p=-2.5`) still
leaves a `2.4×` spread across just four `z` points, no simple power law
reconciles it; (b) adding a `t`-channel analog with `z_t=1-z_s` (echoing
the genuinely-verified `Sewn_s`/`Sewn_t` two-channel structure from
`t_channel_sewing.py`/`sign_derivation.py`) — narrows the spread
somewhat at moderate `z` but is far from uniform and even flips sign
relative to the box at extreme asymmetric kinematics.

**Where this leaves it**: the missing piece is real, confirmed in its
scaling weight, and definitely not a simple multiplicative correction.
The two remaining candidates worth trying next are genuinely different
`u≠1-v` cross-ratios per channel (built from all six operator positions,
not the two-point simplification `u=v=z` used throughout this attempt),
or treating the internal leg position as a true integration variable
against a round-sphere-type measure rather than a fixed chart point.
