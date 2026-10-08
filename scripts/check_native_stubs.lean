-- Native (environment-level) stub audit for GPPVerify.
-- Run with: lake env lean scripts/check_native_stubs.lean
--
-- Complements the text-scanning Python gates (`check_stub_naming.py`, `check_vacuity.py`) with a check
-- on the elaborated environment, so it does not depend on source formatting, comment placement or
-- multiline declarations. It classifies every theorem declared in a `GppVerify.*` module by the *type*
-- the kernel actually sees:
--
--   * `true-stub`     conclusion (after all binders) is literally `True`;
--   * `refl-stub`     conclusion is `a = a` with syntactically identical sides.
--
-- It prints counts and the names; it does not decide scientific adequacy, and it does not replace the
-- Python gates (which also check naming, the blueprint, and the landing page).
import GppVerify
open Lean Meta

def conclusionKind (ty : Expr) : MetaM (Option String) :=
  forallTelescope ty fun _ body => do
    let body ← whnfR body
    if body.isConstOf ``True then return some "true-stub"
    match body.eq? with
    | some (_, a, b) => if a == b then return some "refl-stub" else return none
    | none => return none

#eval show MetaM Unit from do
  let env ← getEnv
  let mut trueStubs : Array Name := #[]
  let mut reflStubs : Array Name := #[]
  let mut total := 0
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    let some idx := env.getModuleIdxFor? n | continue
    unless env.header.moduleNames[idx.toNat]!.getRoot == `GppVerify do continue
    if n.isInternalDetail || (n.toString.splitOn "._proof_").length > 1 then continue
    total := total + 1
    match ← conclusionKind ci.type with
    | some "true-stub" => trueStubs := trueStubs.push n
    | some "refl-stub" => reflStubs := reflStubs.push n
    | _ => pure ()
  IO.println s!"theorems in GppVerify.*: {total}"
  IO.println s!"true-stubs (conclusion True): {trueStubs.size}"
  IO.println s!"refl-stubs (a = a): {reflStubs.size}"
  for n in reflStubs.qsort (·.toString < ·.toString) do
    IO.println s!"  refl-stub: {n}"
  -- Auto-generated proof terms (`_proof_N`, e.g. inside derived `DecidableEq` instances) are skipped above.
  if reflStubs.size > 0 then
    throwError "{reflStubs.size} reflexivity stub(s): a theorem whose conclusion is `a = a`"
