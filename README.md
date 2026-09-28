# GPPVerify

Lean 4 + Mathlib formalization of **shadow holography**, the organizing idea of the Golden
Physics Project. It is a library of kernel-checked theorems, with every open step named
explicitly. It is not a proof of any famous conjecture.

**Public site:** https://lean.goldenphysics.org (plain-language overview) · technical blueprint at https://lean.goldenphysics.org/blueprint/  
**Source text:** Daniel Toupin, *On the Nature of Nature* — https://goldenphysics.org  
**Author:** Daniel Toupin | ORCID: 0009-0003-7682-9579  
**Exploratory companion:** [GPPDiscovery](https://github.com/GoldenPhysicsProject/GPPDiscovery) (numerics; nothing there is proved)

---

## What shadow holography is

One involution appears in two places.

- **Celestial holography.** Scattering amplitudes are Mellin-transformed in energy. They
  are labelled by conformal dimensions `Δ`, with the principal series at `Re Δ = 1`. The
  *shadow* map `Δ ↦ 2 − Δ` pairs each dimension with its partner.
- **Arithmetic.** The completed zeta function `ξ(s)` has a functional equation
  `s ↦ 1 − s`, and its critical line sits at `Re s = ½`.

Under `Δ = 2s` these are the same map. The version that matters is the antiholomorphic
reflection `τ(s) = 1 − s̄`. Its fixed set is exactly the critical line
(`GppFE.critical_line_is_fixed_locus`), and `ξ ∘ τ = conj ∘ ξ`.

The framework reads this holographically, at three nested levels. All three are Mellin or
Pontryagin dualities, so each is a precise dictionary rather than an analogy:

| Boundary | Bulk |
|---|---|
| multiplicative line `ℝ₊`, split at its fixed point `x = 1` | spectral sphere, split by the critical line (the *equator*) into two hemispheres |
| inversion `x ↦ 1/x` | reflection `s ↦ 1 − s̄` |
| support on a half-line | analyticity on a hemisphere (Paley–Wiener) |
| the integers as Fourier modes of a circle (theta, Poisson) | the functional equation |
| primes as a compact torus `∏ S¹`, dual to `ℚ₊^×` | the critical line embedded densely in that torus (Kronecker): *a hologram inside a hologram* |

The same equator appears in celestial scattering as the scale sector: boosts act on energy
by dilation. That part is an exact structural parallel. It is **not** a claim that `ξ` is a
correlator of any physical theory.

What the framework asks is how far this dictionary goes and where it breaks. Each transfer
either survives kernel-checking or fails at a specific, nameable place. Both outcomes are
recorded here.

## What is proved, and what is open

- **The dictionary itself.** Shadow/functional-equation identification, dilation-unitarity
  bridges between principal series and completed zeta, Haar self-duality, and the zero
  pairing `ρ ↦ 1 − ρ̄`. Most of the tree is in `CelestialHolography/` and
  `RiemannHypothesis/`.
- **Physics on the same involution.** Half-flip / CPT and time reversal, Majorana
  conditions, complete positivity, Grassmannian `Gr(2,4)` geometry, and a
  Standard Model sector. Physics inputs enter as explicit hypotheses, never as axioms.
- **RH, as one open question inside the framework.** Holographically, the functional
  equation says the hologram is *symmetric*, and RH says it is also *positive*
  (reflection-positive across the equator). The finite core is proved:
  `GppHolographicRP.reflectionForm_nonneg_iff` shows that positivity across the equator
  holds **iff** there are no off-equator mirror pairs. `GppWeilCriterion.rh_of_weil_pairedForm_nonneg`
  reduces RH to Weil positivity. The missing step is constructing that positivity for the
  actual arithmetic distribution. That step is equivalent to RH, it is not proved, and
  nothing in this repo assumes it.
- **Recorded dead ends.** Several routes were tried and shown not to work, for example the
  Fisher-zero log-concavity no-go (`FisherZeroLogConcavityNoGo.lean`). They stay in the tree
  as theorems about why they fail.

## Honesty rules (enforced by CI)

- **No `sorry`.** CI fails on one.
- **No custom `axiom`.** The count is zero, and `scripts/check_axioms.lean` audits it.
- **Open results are `open_…` stubs.** They are `theorem open_foo : True := trivial`, with a
  doc comment naming the exact missing mathematics. A file full of them still reports
  "0 sorry, 0 axiom", so the `open_` prefix (CI-checked) is what keeps that honest. A stub
  is retired only by proving it.

The current module, stub, and axiom counts are published on the
[blueprint](https://lean.goldenphysics.org) and kept in sync by `scripts/sync_published_counts.py`.
To reproduce them:

```bash
grep -rn "^\s*sorry\s*$" --include="*.lean" GppVerify/ | wc -l
grep -rn "^axiom " --include="*.lean" GppVerify/ | wc -l
grep -rn ": True := trivial" --include="*.lean" GppVerify/ | wc -l
```

## Build

```bash
curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
./elan-init -y
lake exe cache get
lake build
```

Blueprint: `pip install leanblueprint && cd blueprint && leanblueprint build`. The output is
`blueprint/web/index.html`.

## Layout

| Directory | Contents |
|---|---|
| `GppVerify/CelestialHolography/` | shadow transform, principal series, Mellin/dilation bridges |
| `GppVerify/RiemannHypothesis/` | functional equation, explicit-formula and Weil-positivity reductions, holographic reflection positivity |
| `GppVerify/StandardModel/`, `QuantumGravity/`, `QuantumInformation/`, … | physics sectors of the same involution |
| `GppVerify/Thread*/` | self-contained research threads |
| `discovery/` | exploratory notes that sit next to the Lean threads they feed |
| `docs/` | dated working notes; historical, not a status report |
