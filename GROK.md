# GPPVerify — Heart of the Cosmos / Grok operating instructions

The rules for this repo are **not** here. They live in `GoldenPhysicsProject/GPP-bridge`,
the same place Claude and Codex read, so the copies cannot drift. This file exists only
so a session working in this checkout gets a pointer auto-loaded, matching `CLAUDE.md`.

This seat follows Claude's GPPVerify process exactly: the same file layout, the same
small-PR flow, the same CI honesty gates, the same `#print axioms` audit, the same
PR #11 reporting, and dated notes on the bridge. Only the namespace is different
(`grok/…` instead of `claude-code/…`).

**Read, in this order:**

| File (in the GPP-bridge checkout) | For |
|---|---|
| `CONVERSATION.md` and [PR #11](https://github.com/GoldenPhysicsProject/GPP-bridge/pull/11) | **first, every turn.** Report results or ask questions on PR #11, signed **Heart of the Cosmos / Grok**. |
| `rules/GPPVERIFY.md` | the actual rules: non-negotiables, CI gates, branch topology, toolchain, deploy gotchas |
| `work/grok/GPPVERIFY_PROCESS.md` | this seat's working copy of Claude's live process (PRs #520–#551 and the PR #11 loop) |
| `GROK_RESEARCH_NOTES.md` | append dated notes of what this seat did |
| `rules/PROJECT.md` | owner, credentials (vault only — never paste them here), division of labour |

**Do not duplicate those rules back into this file.** `CLAUDE.md` already drifted once
(2026-08-24) that way. Fix the bridge copy instead.

## Seat conventions

| Piece | This seat |
|---|---|
| Standing workbench | `grok/workbench` (cut from current `main`; the old `grok/workbench` was renamed `guest/workbench` and is not mine) |
| Topic branches | short-lived `grok/<thread>`, cut from `grok/workbench` / `main`; delete them on merge |
| Destination | `main`, PR-only. Never push directly to `main`. |
| Other seats | read freely; never push `claude-code/*`, `codex/*`, `turbo/*`, `astra/*`, or `guest/*` |
| Discovery lab | [GPPDiscovery5](https://github.com/GoldenPhysicsProject/GPPDiscovery5) (numerics only). Lean work stays in this repo. |
| Signature | Heart of the Cosmos / Grok, on PR #11 and in commit/PR text |

Honesty gates are the ones CI already runs, the same ones Claude uses: no `sorry` /
`admit`, no custom `axiom`, `open_` stubs for parked gaps, import-graph, vacuity,
stub naming, native stub audit, blueprint refs, landing-page claims, unused binders,
and `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`.
A scratch file that still carries an intended `sorry` cannot land on `main` as written.

Author merges a `grok/…` PR only after CI is green on the real head SHA, then reports
the merge, the axiom list, and the honest boundary on PR #11.

RH and ARP remain OPEN. Nothing in this seat claims otherwise.

Credit: Daniel Toupin / Golden Physics Project.
