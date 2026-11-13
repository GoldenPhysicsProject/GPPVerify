/-
Workbench-only audit module (claude-code/workbench, 2026-11-13). Not for merge.
`#assert_std_axioms` FAILS THE BUILD if any listed declaration depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound` (in particular `sorryAx`).
It turns the fast lane's green "build changed modules" into an axiom receipt.
-/
import GppVerify.RiemannHypothesis.QuartetO2
import GppVerify.RiemannHypothesis.KreinHPsi

open Lean Elab Command

elab "#assert_std_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on non-standard axiom {a}"
    logInfo m!"{n}: standard axioms only ({axs.size})"

#assert_std_axioms GppQuartetSpectral.Fhat_conj GppQuartetSpectral.quartetSum_online
  GppQuartetSpectral.quartetSum_online_nonneg GppQuartetSpectral.conj_Sfin
  GppKreinBridge.no_neg_plane_in_window GppKreinBridge.bridge GppKreinBridge.fit_translates
  GppKreinBridge.bridge_concrete GppKreinBridge.card_lower_freqs_le
  GppKreinBridge.quadruple_two_lower GppKreinBridge.quadruple_not_P1
  GppQuartetO2.O2mult_summable_norm GppQuartetO2.O2mult_of_premises
