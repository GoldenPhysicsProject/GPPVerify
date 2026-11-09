# GPPVerify

Lean 4 + Mathlib formalization of **shadow holography**, the organizing idea of the Golden
Physics Project. It is a library of kernel-checked theorems, with every open step named
explicitly as it is built.

**Public site:** https://lean.goldenphysics.org (plain-language overview) · technical blueprint at https://lean.goldenphysics.org/blueprint/  
**Source text:** Daniel Toupin, *On the Nature of Nature* — https://goldenphysics.org  
**Author:** Daniel Toupin | ORCID: 0009-0003-7682-9579  
**Exploratory companions:** the five numeric workbenches [GPPDiscovery](https://github.com/GoldenPhysicsProject/GPPDiscovery), [GPPDiscovery2](https://github.com/GoldenPhysicsProject/GPPDiscovery2), [GPPDiscovery3](https://github.com/GoldenPhysicsProject/GPPDiscovery3), [GPPDiscovery4](https://github.com/GoldenPhysicsProject/GPPDiscovery4), [GPPDiscovery5](https://github.com/GoldenPhysicsProject/GPPDiscovery5) (numerical exploration that feeds the formalization)

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
by dilation. The framework's central hypothesis is that `ξ(s)` is a physical operator, and
this library builds, theorem by theorem, the exact dictionary that hypothesis stands on.

The goal is to map the full **arithmetic ↔ celestial CFT correspondence**, carrying the
dictionary as far as it goes. Each transfer is either kernel-checked or located at a
specific, named step, and both are recorded here.

## What is here

- **The dictionary itself.** Shadow/functional-equation identification, dilation-unitarity
  bridges between principal series and completed zeta, Haar self-duality, and the zero
  pairing `ρ ↦ 1 − ρ̄`. Most of the tree is in `CelestialHolography/` and
  `RiemannHypothesis/`.
- **Physics on the same involution.** Half-flip / CPT and time reversal, Majorana
  conditions, complete positivity, Grassmannian `Gr(2,4)` geometry, and a
  Standard Model sector. Physics inputs enter as explicit, named hypotheses.
- **The Riemann Hypothesis, one of the framework's targets.** Holographically, the
  functional equation says the hologram is *symmetric*, and RH says it is also *positive*
  (reflection-positive across the equator). The finite core is proved:
  `GppHolographicRP.reflectionForm_nonneg_iff` shows that positivity across the equator
  holds **iff** there are no off-equator mirror pairs, and
  `GppWeilCriterion.rh_of_weil_pairedForm_nonneg` reduces RH to Weil positivity. The
  library is building toward that positivity for the arithmetic distribution, layer by
  layer: idèles of ℚ and Fujisaki's lemma, local Tate theory, the explicit formula. A guide to
  the local and global Tate layer, with the file and principal declarations for each result, is
  in [`docs/TATE-GUIDE.md`](docs/TATE-GUIDE.md).
- **No-go theorems.** Routes that fail are kept as theorems pinning down exactly where they
  fail, for example the Fisher-zero log-concavity no-go (`FisherZeroLogConcavityNoGo.lean`).

## Standards (enforced by CI)

- **Every theorem is kernel-checked**, with zero `sorry` and zero custom axioms;
  `scripts/check_axioms.lean` audits the count.
- **Steps still being built are `open_…` stubs**: `theorem open_foo : True := trivial`, with a
  doc comment naming the exact mathematics that will fill it. The `open_` prefix is
  CI-checked, and a stub is retired by proving it.

## What a sceptical reader can check in ten minutes

Each point below is a command or a file.

- **The epistemics are mechanical.** `scripts/` holds the gates CI runs:
  `check_sorries.py`, `check_stub_naming.py` and `check_vacuity.py` (every declaration
  carries real content), `check_blueprint_refs.py` (every `\lean{}` in the blueprint must name a real
  declaration), `check_landing_claims.py` (the public page matches the tree), `check_import_graph.py`, and `check_axioms.lean` (`#print axioms` on the flagship
  theorems). Each script's header records the audit that produced it.
- **The Riemann Hypothesis is stated as an exact equivalence.**
  `rh_iff_weil_pairedForm_nonneg` (RH iff a positivity statement) and
  `GppHolographicRP.reflectionForm_nonneg_iff` (positivity across the equator iff
  every zero pairs on the equator) are proved, and the positivity step is named.
- **No-go results are first-class output**, kept as theorems, e.g.
  `FisherZeroLogConcavityNoGo.lean`.
- **The `open_…` stubs are counted and named**, so the stub ledger is the live map of
  what is being built next.
- **Dates are on everything.** `docs/` holds dated working notes and `archive/` holds
  earlier surveys; the current status is this file and the blueprint.

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
| `docs/` | dated working notes |
