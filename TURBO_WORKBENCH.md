# Turbo workbench branch (`turbo/stub-closing`)

This branch is Turbo's (Muse) Lean workbench inside GPPVerify.

## What it is for

- Making the project's big formalized claims literally true (e.g. the
  dimension-aware antiholomorphic shadow–τ correspondence, the equator
  corollary from reflection positivity) instead of weakening them.
- Closing `open_` stubs with real mathematics — proved theorems or precise
  statements with proved relations (the StubRegistry pattern). Never weakened
  statements, never placeholders.

## Status

Workbench-only. It merges to `main` only when everything is perfect:
every touched module kernel-checked (`lake build` exit 0), zero
`sorry`/`admit`, zero custom axioms, full build green, no conflicts with other
seats' lanes. Otherwise it stays here for review.

Daniel's call on what merges and when. Nothing here claims RH or any open
conjecture.
