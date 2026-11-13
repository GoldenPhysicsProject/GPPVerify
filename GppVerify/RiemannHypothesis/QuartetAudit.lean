/-
Workbench-only audit module (claude-code/workbench, 2026-11-13). Not for merge.
`#assert_std_axioms` FAILS THE BUILD if any listed declaration depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound` (in particular `sorryAx`).
It turns the fast lane's green "build changed modules" into an axiom receipt.
-/
import GppVerify.RiemannHypothesis.QuartetO2
import GppVerify.RiemannHypothesis.KreinHPsi
import GppVerify.RiemannHypothesis.QuartetFiniteCore

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

#assert_std_axioms GppQuartetFiniteCore.triG_eq_zero_of_abs_ge
  GppQuartetFiniteCore.triG_even
  GppQuartetFiniteCore.triG_eq_triForm
  GppQuartetFiniteCore.continuous_tri
  GppQuartetFiniteCore.continuous_triG
  GppQuartetFiniteCore.Rc_even
  GppQuartetFiniteCore.Rc_eq_zero_of_abs_gt
  GppQuartetFiniteCore.continuous_Rc
  GppQuartetFiniteCore.rcAdmissible
  GppQuartetFiniteCore.primeTerm_eq_sum_of_bound
  GppQuartetFiniteCore.kform_primeTerm_finite
  GppQuartetFiniteCore.kform_primeTerm
  GppQuartetFiniteCore.kform_poleTerm
  GppQuartetFiniteCore.kform_poleTerm_on_ker
  GppQuartetFiniteCore.kform_Kpsi
  GppQuartetFiniteCore.tri_integral_sinh
  GppQuartetFiniteCore.tri_integral_cosh
  GppQuartetFiniteCore.tri_integral_exp_half
  GppQuartetFiniteCore.tri_integral_exp_neg_half
  GppQuartetFiniteCore.Fhat_zero
  GppQuartetFiniteCore.Fhat_one
  GppQuartetFiniteCore.Fhat_zero_sq_add_one_sq
  GppQuartetFiniteCore.O2_of_weilEF
