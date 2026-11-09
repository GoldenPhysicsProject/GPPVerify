# GPPVerify

Lean 4 + Mathlib formalization of **shadow holography**, the organizing idea of the Golden
Physics Project. It is a library of kernel-checked theorems, with every open step named
explicitly as it is built.

**Public site:** https://lean.goldenphysics.org (plain-language overview) · technical blueprint at https://lean.goldenphysics.org/blueprint/ · [site map](sitemap.xml)  
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

The library holds about 1,200 Lean modules. Each major directory carries its own
README with the map of that layer; this section is the index of them.

- **The dictionary itself.** Shadow/functional-equation identification, dilation-unitarity
  bridges between principal series and completed zeta, Haar self-duality, and the zero
  pairing `ρ ↦ 1 − ρ̄`. Most of the tree is in
  [`CelestialHolography/`](GppVerify/CelestialHolography/README.md) and
  [`RiemannHypothesis/`](GppVerify/RiemannHypothesis/README.md).
- **The Tate layer.** Tate's thesis for ℚ, built end to end: the local functional
  equation at the real place for both parities, the ideles of ℚ and Fujisaki's theorem,
  the standard adelic character with `ℚ^⊥ = ℚ` (GP-DUAL), the Haar normalization with
  covolume one, the self-duality of `∏_p ℤ_p`, and the classical Poisson control made
  unconditional. The guide to the layer, with every file, its principal results, and its
  dependencies, is [`docs/TATE-GUIDE.md`](docs/TATE-GUIDE.md). The remaining steps are
  named propositions in the statement file: Fourier inversion, Plancherel, the scaled
  Poisson formula, and GW-EF, the link from Poisson summation to the Weil form.
- **The Riemann Hypothesis, one of the framework's targets.** Holographically, the
  functional equation says the hologram is *symmetric*, and RH says it is also *positive*
  (reflection-positive across the equator). The finite core is proved:
  `GppHolographicRP.reflectionForm_nonneg_iff` shows that positivity across the equator
  holds **iff** there are no off-equator mirror pairs, and
  `GppWeilCriterion.rh_of_weil_pairedForm_nonneg` reduces RH to Weil positivity. The
  finite windows of that positivity are certified: the Schur sector form is positive
  for sectors K = 2 to 18, and the first two zero orbitals close the K = 5 diagonal in
  exact rational arithmetic (the AUG2 certificate, an independent tail sum over 138,067
  further zeros confirms the closure is a fact about the zeros). The current target is
  the positivity stated as unitarity of the global S-matrix; its open statement is
  named (SPEC), with GW-EF as the named link to the Weil form.
- **Physics on the same involution.** Half-flip / CPT and time reversal, Majorana
  conditions, complete positivity, Grassmannian `Gr(2,4)` geometry, and a
  Standard Model sector: [`StandardModel/`](GppVerify/StandardModel/README.md),
  [`QuantumGravity/`](GppVerify/QuantumGravity/README.md), and the smaller sectors in
  the layout table below. Physics inputs enter as explicit, named hypotheses.
- **No-go theorems.** Routes that fail are kept as theorems pinning down exactly where they
  fail, for example the Fisher-zero log-concavity no-go (`FisherZeroLogConcavityNoGo.lean`).
  They live in [`NoGo/`](GppVerify/NoGo/) and in the layers they close off.
- **Upstream staging.** [`Upstream/`](GppVerify/Upstream/README.md) holds files written
  to Mathlib conventions for contribution to Mathlib: the Weierstrass and
  entire-function order-of-growth cluster, the two adele files of the Tate layer, and
  the two-vector projection formulas. The first contribution is open as
  [mathlib4 PR #45825](https://github.com/leanprover-community/mathlib4/pull/45825);
  the rest are staged.

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

| Directory | Files | Contents |
|---|---|---|
| `GppVerify/RiemannHypothesis/` | 584 | [the RH programme](GppVerify/RiemannHypothesis/README.md): functional equation, Tate layer, explicit formula, Weil positivity reductions, certificates |
| `GppVerify/CelestialHolography/` | 329 | [the celestial side](GppVerify/CelestialHolography/README.md): shadow transform, principal series, Penrose and ambitwistor geometry |
| `GppVerify/StandardModel/` | 132 | [the Standard Model sector](GppVerify/StandardModel/README.md): CPT and orientation, charge, Pati–Salam |
| `GppVerify/QuantumGravity/` | 53 | [quantum gravity](GppVerify/QuantumGravity/README.md): causal diamonds, equator thermodynamics, Fisher geometry |
| `GppVerify/NoGo/` | 23 | no-go theorems: routes closed, with the failing step located |
| `GppVerify/GeneralRelativity/` | 20 | causal diamonds and boundary charges in GR form |
| `GppVerify/NumberTheory/` | 19 | zeta values, Euler sums, BSD point counts, shadow Euler identities |
| `GppVerify/ThreadWeilParity/` | 16 | the Weil parity thread |
| `GppVerify/Upstream/` | 11 | [Mathlib staging](GppVerify/Upstream/README.md) |
| `GppVerify/Analysis/` | 5 | Landau and Pringsheim theory for Dirichlet series |
| `GppVerify/Cosmology/` | 4 | cosmological sectors |
| `GppVerify/QuantumInformation/` | 4 | quantum information sectors |
| `GppVerify/QuantumFieldTheory/` | 3 | QFT sectors |
| `GppVerify/ThreadS/`, `ThreadHT/`, `ThreadWeilSemibound/` | 5 | self-contained research threads |
| `GppVerify/Certificates/`, `StringTheory/`, `YangMills/` | 3 | single-file sectors |
| `discovery/` | | exploratory notes that sit next to the Lean threads they feed |
| `docs/` | | [dated working notes](docs/README.md), and the [Tate guide](docs/TATE-GUIDE.md) |
| `blueprint/` | | the technical blueprint source |
| `scripts/` | | the CI gates |
| `archive/` | | earlier surveys, including the dependency map |
