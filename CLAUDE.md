# GPPVerify — Claude operating instructions

Lean 4 formalization of the Golden Physics Project's shadow framework (Haar measure
self-duality, shadow = CPT, and the Riemann Hypothesis thread). This file holds stable
operating rules, not a session diary — status, findings, and progress live in
`docs/FORMALIZATION_PLAN.md`, the blueprint (`blueprint/src/web.tex`), and Supabase
(`lean_tasks`/`lean_results`/`formalization_queue`), not here.

Shared project context (owner, credentials, Codex division-of-labor, other repos):
`website/CLAUDE.md`. Numeric/exploratory discovery work happens in
`GoldenPhysicsProject/weil-decay` (its own `CLAUDE.md`) before graduating here.

## Non-negotiable rules

- No `sorry`. No axiom whose statement asserts an open claim (an axiom that just *is* the
  theorem being worked toward is a lie, not a proof). The honest way to park an unfinished
  result is `theorem foo : True := trivial` — tracked separately from `sorry`/axiom counts,
  never mistaken for a proved fact.
- Verify every uncertain lemma name/signature against the pinned Mathlib source
  (`.lake/packages/mathlib`) before using it — don't guess API from memory.
- Build small, standalone lemmas in a scratch file first (`lake env lean <scratch>.lean`,
  default heartbeats), confirm independently, only then integrate into the real project
  file. Delete the scratch file once integrated.
- Small PRs, CI-green before merge. Verify CI green via the GitHub Actions API on the
  **actual commit SHA** (never assume from push alone), and verify the deploy chain
  (`build.yml`, `blueprint.yml`, "Deploy to GitHub Pages" / `pages-build-deployment`) on
  the **actual merge commit SHA** after merging — not on the PR branch tip.
- Multiple sessions (this account, other Claude sessions, Codex on its own branches) touch
  this repo concurrently. Fetch and independently verify state before trusting a summary,
  screenshot, or another session's own claim about what it did.

## Branch hygiene (added 2026-08-24, after a 14-stray-branch audit)

A 2026-08-24 audit found 14 unmerged branches, several months old, some with real proved
content nobody had merged or even looked at again — pure loss, and two rescued (PR #122)
only because someone happened to go looking. Don't let that happen again:

**Every branch you create gets closed the same session, one of two ways:**
1. Merged — PR opened, CI verified green on the real head SHA, merged, deploy chain
   verified on the real merge SHA, or
2. Explicitly discarded, with a one-line note of why (superseded, duplicate, dead end) —
   not just abandoned silently.

A branch with no PR and no note, sitting untouched for weeks, is the failure mode this
rule exists to prevent. See `weil-decay/CLAUDE.md` for the discovery-side half of this
discipline.

## Toolchain

- Lean 4 / Mathlib 4.19.0 (`lean-toolchain`, `lake-manifest.json` pin the exact versions).
- `lake` lives at `/root/.elan/bin/lake` — not always on `$PATH` in a fresh shell; add
  `/root/.elan/bin` to `PATH` explicitly if `lake: command not found`.
- Reuse `.lake/` build cache across worktrees/clones when verifying a branch builds — a
  full from-scratch `lake build` is far slower than an incremental one off a warm cache.

## Known gotchas

- `leanblueprint`'s `\lean{...}` macro needs **raw, unescaped underscores** in identifier
  names. A backslash-escaped underscore turns plasTeX's parsed argument into a multi-token
  `TeXFragment` instead of a flat string and crashes `digest()`. Before pushing anything
  that touches `blueprint/src/web.tex`: `grep -n '\\lean{' blueprint/src/web.tex | grep
  '\\_'` must return nothing.
- `blueprint.yml` only deploys on push to `main`, not on PR/feature-branch pushes.
  `blueprint/src/web.tex` is hand-authored and does not auto-regenerate from Lean source —
  update it manually alongside any Lean change worth documenting there.
- Dot-notation can silently resolve to a more general lemma than intended
  (`HasFDerivAtFilter.sub` instead of `HasDerivAt.sub`) when the more specific lemma's
  defining file isn't imported — import the specific `Mathlib.Analysis.Calculus.Deriv.*`
  files you actually need rather than relying on a broader import to pull them in
  transitively.
- `λ` is a reserved token (lambda syntax) in Lean 4 — don't use it as an identifier.

## Session protocol

Supabase project `dunrgpupddbmzffntwph`. At session start, query `formalization_queue` for
`status='ready'` items (priority order) and `lean_tasks` for `status='pending'`. Claim an
item by setting `status='formalizing'` before starting.

At session end (mandatory): write a row to `lean_results` for anything non-trivial —
what was proved (with commit SHAs), verification evidence, what was attempted and failed
and why, the exact honest boundary of what's still open. Update the source
`formalization_queue`/`lean_tasks` row status (`formalized`/`blocked`/etc.). Never write a
success row for unverified work — a failed gate is itself a result, write it up honestly.
