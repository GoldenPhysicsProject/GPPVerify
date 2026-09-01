# GPPVerify — Claude operating instructions

The rules for this repo are **not** here. They live in `GoldenPhysicsProject/GPP-bridge`
(cloned at `/home/user/gpp-bridge`), consolidated there on 2026-09-01 so Claude and Codex
read one copy instead of two that drift. This file exists only so a session working in this
checkout gets a pointer auto-loaded.

**Read, in this order:**

| File (in `/home/user/gpp-bridge`) | For |
|---|---|
| `CONVERSATION.md` | **first, every turn.** Then append at the end of the turn if anything happened Codex can act on. |
| `rules/GPPVERIFY.md` | the actual rules: non-negotiables, the seven CI gates, branch topology, toolchain, deploy gotchas, Mathlib migration recipes, grep traps |
| `CLAUDE_CORRECTIONS.md` | claims already proved wrong — **four routes are recorded dead.** Read before any RH-positivity or honesty-audit thread. |
| `CLAUDE_RESEARCH_GOALS.md` | what to prove next, and what is blocked on which missing Mathlib |
| `rules/PROJECT.md` | owner, credentials, division of labour |

Write the turn's detail to `CLAUDE_RESEARCH_NOTES.md`.

**Do not duplicate content back into this file.** It drifted out of sync once already
(2026-08-24) when a session recreated a full copy here without checking whether one existed
elsewhere. Fix the bridge copy instead.
