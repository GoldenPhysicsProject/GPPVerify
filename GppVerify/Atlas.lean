/-!
# Atlas — the library's own map

This module is the map of GPPVerify, written inside the library so a bot working
in a workbench can descend the chain from wherever it stands: area → frontier
module → the seat that owns the front → the Discovery repo that fed it → the
bridge document that governs it. It contains no theorems. It is documentation
only, kept honest by the same rule as the rest of the record: every count below
was produced by a command run against the remote on the day named.

Counts: GitHub API tree of `main`, queried 2026-11-17 — **1,418 `.lean` files**
(tree not truncated). This module is one more file on top of that count; it
describes `main`, not itself. When the counts drift, edit this file through the
suggestion box like any other canon change.

## The chain

Daniel (head) → Turbo (hub: audits, relays, operations) → the five seats →
their Discovery repos (public scratchpads, where the working is done) → their
GPPVerify workbench branches (where compile receipts live) → `main` (banked).
Nothing is banked until a different arm has audited it firsthand, the branch
CI check named `lake build` is green on the pinned head, and Claude Code —
the only merger to `main` (Daniel's rule, 2026-11-17) — merges it.

What lives outside Lean, in the private GPP-bridge repo: `GOAL.md` (every goal
in priority order), `TEAM-SOUL.md`, `TEAM-SOPS.md` (channels, gates, the editing
rule), `TEAM-MEMORIES.md`, `SUGGESTIONS.md` (the suggestion box), the weekly
CONVERSATION files (the shared room; index at `CONVERSATION.md`), the seats'
`LANE-STATE-*.md` files, and `research/CAMPAIGN-ORDER-2026-11-17.md` (the
campaign order the phases below refer to).

## The areas (module counts from the tree of `main`, 2026-11-17)

* `GppVerify/RiemannHypothesis` — **749**. The Riemann Hypothesis programme:
  the fixed-window Weil form, ARP and its OB-6 contractivity form, the Suzuki
  box certificates, the Krein/Toeplitz machinery. Frontier modules:
  `ShiftPresentation` (`OB6`, `OB6At`, `arp_iff_ob6`), `TwoSpaceForm`
  (`ob6At_iff_single_cutoff`, the two-positive-space form), `Ob6CofinalWidths`
  (the all-widths cofinal chain), `BoxCurvature`, `BoxArchimedean`,
  `BoxEventTwo` (the box certificates, banked as PRs #629–#633),
  `SuzukiKickCone`, `KreinBridge`, `RHProofStructure` (the proof structure and
  its open stubs; A1, `scaling_eigenspace_ode`, closed in PR #634). Relates to:
  GOAL Tier 0, goal 1; campaign Phases 0–3; seats D1 (Lean), D2 (filings),
  D3 (audits), D5 (theory).
* `GppVerify/CelestialHolography` — **334**. The celestial dictionary: s = Δ,
  the shadow involution Δ ↦ d − Δ, reflection positivity on the celestial side.
  Relates to: GOAL Tier 0 and the ontology paper (Tier 2); the same involution
  the RH area's pairing is built from.
* `GppVerify/StandardModel` — **132**. Orientation, charge and arrow structure
  (the arrow-form CPT material lives in this neighbourhood of the library).
  Relates to: the Which Way Is Forward thread (Tier 2).
* `GppVerify/QuantumGravity` — **53**. Causal diamonds, Born-rule and
  finiteness material. Relates to: the volume-constraint paper thread (Tier 2).
* `GppVerify/Upstream` — **29**. General-purpose results bound for Mathlib
  (digamma bounds and series among them). Relates to: the Mathlib upstreaming
  goal; check here before proving a utility lemma from scratch.
* `GppVerify/NoGo` — **25**. Formalised dead ends. Read before resurrecting a
  route: if it is here, it was killed with the obstruction located.
* `GppVerify/GeneralRelativity` — **20**. Diamond/ADM boundary material behind
  the volume-constraint paper (Tier 2, goal 8).
* `GppVerify/NumberTheory` — **20**. BSD point counts, Euler sums, standalone
  arithmetic.
* `GppVerify/ThreadWeilParity` — **16**. The Weil-form parity thread:
  archimedean tails, defect and cross-heat positivity.
* Root level — **15**, including `GppVerify.lean` itself (the root graph this
  module is wired into) and `CoreTheorems`.
* `GppVerify/Analysis` — **7**. Mellin/Plancherel machinery the RH area draws on.
* `GppVerify/Cosmology` — **4**. Halo pairs, dark-sector ratios.
* `GppVerify/QuantumInformation` — **4**. CHSH, Choi matrices, complete positivity.
* `GppVerify/QuantumFieldTheory` — **3**. The Fock-space material (`FockGibbs`,
  `FiniteLatticeGap`, `ArithmeticFock`).
* `GppVerify/YangMills` — **3**, including `MassGap`. Relates to: GOAL Tier 0,
  goal 2 (the Millennium Metaproblem).
* `GppVerify/Certificates` — **1**. `GppVerify/StringTheory` — **1**
  (`DivisionAlgebras`, the sphere-tower material). `GppVerify/ThreadS` — **1**.
  `GppVerify/ThreadWeilSemibound` — **1**.

## The seats, their workbenches, their Discovery repos

GPPVerify carries 152 branches (git ls-remote, 2026-11-17); most are finished
front branches. The standing workbenches:

* **D1 Claude Code** (the Lean lane; only merger). Workbench: `claude/workbench`
  (plus the session-pinned `claude/gpp-verify-lean-formalization-qmoucj` and the
  older `claude-code/workbench`). Fast lanes on `main`: `claude-fast.yml` and
  `claude-code-fast.yml` (job name `targeted build`). Discovery counterpart:
  GPPDiscovery1 does not exist; D1 works directly in Verify.
* **D2 Astra + Sol, and the GPT seat** (constructions, filings, audits on paper).
  Workbench: `astra/workbench`. Discovery repo: **GPPDiscovery2** (34 branches) —
  filings land there first, are audited by Turbo, and reach Verify through D1.
* **D3 Flint** (Turbo's audit seat; the independent arm). Workbench:
  `flint/workbench` — which carried her frozen Krein/Quartet
  handover (QuartetSpectral, QuartetFiniteCore, KreinKpsiContinuous), now banked
  on `main` together with this module. Discovery repo: **GPPDiscovery3** (4 branches, incl.
  `flint/moving-in`).
* **D4 Turbo** (hub). Workbench: `turbo/stub-closing`. Discovery repo:
  **GPPDiscovery4** (1 branch, `main`).
* **D5 Heart of the Cosmos** (Grok; theory). Workbench: `heart/workbench` (older:
  `grok/workbench`). Discovery repo: **GPPDiscovery5** (6 branches, the `team/*`
  lines). Status, per the bridge record: out of commission since 2026-11-15;
  her PR #11 channel stays warm and nothing waits on her.
* Also present: `codex/lean-workbench` (the Codex seat, outside the D-map) and
  `guest/workbench`.

Fast lanes: a fast lane is a targeted build of only the front's modules
(~2 min) with sorry and bare-axiom gates — an iteration aid; the full `Build`
remains the merge gate. On `main` today: `claude-fast.yml`,
`claude-code-fast.yml`, `causal-short-window-fast.yml`, `prime-gram-fast.yml`.
The per-seat lanes for astra/flint/heart/turbo are added by PR #635
(`turbo/fastlane-per-seat`) — if your seat's lane does not run, check that #635
is merged.

## Shared assets outside the library

* **Zeros data** — `~/workspace/zeros-platt/`: 63,150,760 Platt/LMFDB zeros in
  17 binary `.dat` files; `validation.json` records the count check passing
  (γ₁ decoded to 47 digits). Data for checks, never proof input.
* **Literature** — `~/workspace/literature-2026/`: the Pasterski corpus
  (`pasterski/`, 50 PDFs), the Strominger corpus (`strominger-holography/`,
  160 PDFs), Euler and Riemann folders, and the annotated bibliography
  `rh-2026-annotated-bibliography.pdf` (61 items).
* **The RH goal workspace** — `~/workspace/goals/prove-the-riemann-hypothesis/`:
  `files/` holds the seats' notes (Flint's β± grid, the Phase 0b co-audit, the
  running-law and index analyses), `hidden_files/` the receipts, scripts and
  the ARP hunt note.
* **The bridge research folder** — `research/` in GPP-bridge: the campaign
  order, `research/codex` (72 files), `research/external` (3,399 files),
  `research/rh`; and `MuseResearch/` (182 files), the seats' shared research
  shelf.

*Filed by Flint (D3), 2026-11-17, at Daniel's direction. Sources: the API tree
and ls-remote output quoted above, the bridge lane states, and GOAL.md — all
read firsthand on the day of filing.*
-/
