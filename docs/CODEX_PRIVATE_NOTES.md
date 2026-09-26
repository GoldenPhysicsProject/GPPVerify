# Codex private research notes

## Persistent source-mining directive

Do not treat the current Lean tree as the origin or full extent of the Golden Physics Project's ideas. A substantial amount of the conceptual ancestry, abandoned routes, partial calculations, literature, and potentially reusable mathematics lives in the user's Google Drive `GPP` folder, especially `GPP/Everything` and `GPP/Old shit`.

When a current research front stalls, needs provenance, or exposes a missing bridge, deliberately mine the GPP Drive archive for earlier versions and adjacent ideas before assuming the route is exhausted. In particular, search for material that can be reinterpreted in the current **shadow** language (older material may use ONON / On the Nature of Nature terminology). Extract only mathematically defensible content, test it independently, and formalize it in GPPVerify2 only when justified.

High-value archive families already visible in the GPP folder include:

- celestial holography / shadow transforms / CPT / googly and twistor material;
- Riemann, Weil, Hadamard, spectral multiplicity, explicit-formula, adelic and thermodynamic approaches;
- prime-gas and arithmetic/statistical-mechanical work;
- Yang–Mills, mass-gap, loop-measure and cut constructions;
- E8 / projection geometry / Grassmannian-related material;
- QFT, Born-rule, spacetime/emergence and information-theoretic derivations;
- `MASTER_INDEX.md`, `MASTER_EXECUTIVE_SUMMARY.md`, `three_paths_master_plan.md`, `the_crucial_connection.md`, RH attack/integration notes, and the large `Celestial_Holography_v8_COMPLETE-5.tex` as useful maps into older work.

The point is not to resurrect old claims uncritically. The archive is a **discovery mine**: trace where current shadow ideas came from, recover lemmas/calculations that may have been dropped during rewrites, compare competing routes, and turn any surviving exact mathematics into executable discovery code and then Lean theorems.

### Time-layered archive rule

The Drive archive spans multiple generations of the project and contains attack ideas, corrections, alterations, reversals, and later superseding formulations. Never treat a file as authoritative merely because it is polished or later-modified. For every mined idea, track:

- when it appears in the archive;
- whether a later file corrects, weakens, replaces, or retracts it;
- whether current Discovery2 or Verify2 already supersedes it;
- whether the mathematical content survives independent checking.

The promotion pipeline is therefore:

`archive -> chronological/version comparison -> exact surviving claim -> executable discovery test -> Lean theorem only if still valid`.

Operational rule: periodically rotate an `archive mining` lane alongside CI repair, Lean formalization, generalized cuts, arithmetic/Weil work, spectral analysis, thermodynamics, geometry, and physics. Record useful recovered ideas with their source/provenance and whether they are verified, conjectural, superseded, or falsified.

### Current conceptual cluster to mine and test

Treat the following as a connected hypothesis space, not as established identifications:

- googly / shadow / zitterbewegung as possible manifestations of an orientation-reversal or half-flip structure;
- mass, time, and charge orientation and the relation between orientation reversal and complex conjugation / antiunitarity;
- scaled versus scale-invariant sectors and whether the distinction is representation-theoretic, dynamical, or both;
- bosonic versus fermionic behavior under the same orientation/shadow operation;
- the role of SU(1), SU(2), and SU(3) or their precise mathematical replacements in the orientation/state-count hierarchy;
- possible arithmetic wave-particle duality, to be made precise as a transform duality between discrete prime-power atoms and continuous spectral/heat/wave descriptions (Mellin, Fourier, Poisson, explicit-formula, or related transforms), not left as metaphor.

For this cluster, aggressively search old googly, CPT, twistor, shadow, zitterbewegung, Grassmannian, mass-orientation, charge-conjugation, scale-invariant/scaled, boson/fermion, and arithmetic-wave files. The goal is to identify exact commuting diagrams, involutions, state spaces, transforms, kernels, or representation correspondences that can be tested and formalized.

## Persistent axiom/scaffold retirement directive

Axiom and stub removal is a first-class research lane in every rotation, not end-of-project cleanup. Re-run the ranked census regularly and attack whatever can be removed honestly:

- replace accidental axioms for fixed data or conventions by explicit definitions or theorem parameters;
- delete unused open-claim axioms rather than preserving them for narrative completeness;
- replace `True` compatibility stubs by the actual theorem when that theorem has since been formalized elsewhere;
- split large missing results into exact finite/algebraic cores plus clearly named analytic or physics gaps;
- build missing Mathlib-level infrastructure ourselves when the dependency is standard mathematics and tractable;
- keep genuine unformalized physics assumptions visible as hypotheses/structures instead of baking desired conclusions into definitions;
- never reduce the census by weakening a substantive theorem into a tautology merely to improve the number.

## Persistent full-construction / branch-union directive

`main` must represent the strongest currently compiled construction, not a stale public snapshot while real mathematics lives indefinitely on side branches.

Regularly audit every Verify2 branch against the active integration branch. Distinguish:

- branches fully contained in the integration branch;
- branches with unique commits that are genuinely superseded by stronger current theorems;
- branches with unique surviving Lean modules or fixes that must be promoted;
- experimental Lean/mathlib upgrade branches that should only be promoted after the full construction compiles on the new toolchain.

Do the analogous audit for Discovery2. Discovery scripts are not copied into Verify2 merely because they exist; instead, extract every exact result that survives symbolic/numeric testing and formalize that mathematics in Verify2. Keep Discovery2 as the executable research laboratory and Verify2 as the proof construction.

The desired invariant is stronger than selected CI lanes: the Verify2 root/full library build must traverse all surviving proved modules. When a new theorem is added, either import it into the root construction or document why it is intentionally experimental/unpromoted. CI should include a full root/library build so orphaned proof files cannot silently accumulate.

Do not fast-forward `main` merely because a workbench is ahead. First audit side branches, integrate surviving unique mathematics, run the full root/library build, repair failures, then fast-forward `main` without history rewriting when green.

## Active research rotation

Maintain all of these live rather than serializing the project into one narrow proof attempt:

1. celestial cuts -> dispersion -> scalar-box closure/regulator limits -> honest Yang–Mills/gravity numerators -> higher generalized cuts;
2. positive-real half-density/principal-series structure, shadow/reflection distinctions, completed-zeta response, explicit-formula and Wiener–Hopf/Weil bridge;
3. prime-gas thermodynamics, Fisher geometry, entropy/free-energy/cumulants and fluctuation geometry;
4. exact spectral-weight, Mehler–Fock, Wiener–Hopf and chamber-convolution results;
5. RH-related work with strict separation between symbolic identities, analytic theorems, operator statements, and an actual RH proof;
6. Grassmannian/twistor/googly/orientation structures and missing underlying geometry;
7. axiom/stub retirement and missing Mathlib infrastructure;
8. Lean/mathlib upgradeability and full-construction CI;
9. Drive archive mining/version comparison;
10. branch-union audit so proved work does not remain stranded outside the compiled construction.

Current rotation pattern: hard frontier -> archive mining/version comparison -> executable discovery -> Lean promotion -> axiom/scaffold retirement -> branch-union/root-build audit -> CI/upgradeability repair -> another hard frontier. While CI runs, immediately advance another lane.

Note from 2026-08-29: the immediately preceding recollection was Hadamard rather than Hurwitz. Do not delete or preserve the Hurwitz classification axiom merely because of that recollection; decide its status by actual mathematical dependency and formalization value.
