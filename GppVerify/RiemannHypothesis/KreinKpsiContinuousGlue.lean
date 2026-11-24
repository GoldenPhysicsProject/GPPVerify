/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat), 2026-11-14, takeover shift for Claude Code's lane.

# `Kpsi` is continuous — the two archimedean obligations are discharged

`KreinKpsiContinuous.lean` (Flint, 2026-11-13) proves `Continuous Kpsi` modulo two
named obligations about the archimedean factor of `archTerm`:

* `ArchGammaFactorContinuous : ContinuousOn archFactor (Ioi 0)`;
* `ArchEnvelopeIntegrable : IntegrableOn (fun t => bigPsi t ^ 2 * |archFactor t|) (Ioi 0)`.

`ArchEnvelope.lean` (Claude Code, PR #591, merged to main as `25a4beb`, Flint-audited)
proves both statements for the functions `archFactor'` and `bigPsi'`, whose definitions
are textually identical to `archFactor` and `bigPsi` here:

* `GppArchEnvelope.continuousOn_archFactor' : ContinuousOn archFactor' (Ioi 0)`
  (in fact `archFactor'` is continuous on all of `ℝ`);
* `GppArchEnvelope.integrableOn_envelope :
    IntegrableOn (fun t => bigPsi' t ^ 2 * |archFactor' t|) (Ioi 0) volume`.

Since the definition bodies agree term for term, the discharges below are `exact`.
This file therefore closes the continuity input of Krein's representation theorem
for `Kpsi` unconditionally: `continuous_Kpsi` needs no hypotheses.

No `sorry`. No named premises. Standard axioms only.
-/
import GppVerify.RiemannHypothesis.KreinKpsiContinuous
import GppVerify.RiemannHypothesis.ArchEnvelope

namespace GppKreinKpsiContinuousGlue

open GppKreinKpsiContinuous MeasureTheory Set

/-- The first obligation of `KreinKpsiContinuous.lean`, discharged:
the digamma factor of `archTerm` is continuous on `(0, ∞)`. -/
theorem archGammaFactorContinuous_proved : ArchGammaFactorContinuous :=
  GppArchEnvelope.continuousOn_archFactor'

/-- The second obligation of `KreinKpsiContinuous.lean`, discharged:
the `d`-independent envelope of the `archTerm` integrand is integrable on `(0, ∞)`. -/
theorem archEnvelopeIntegrable_proved : ArchEnvelopeIntegrable :=
  GppArchEnvelope.integrableOn_envelope

/-- **Continuity of `archTerm`, unconditionally.** -/
theorem continuous_archTerm : Continuous GppKreinHPsi.archTerm :=
  GppKreinKpsiContinuous.continuous_archTerm
    archGammaFactorContinuous_proved archEnvelopeIntegrable_proved

/-- **Continuity of `Kpsi`, unconditionally.** This is the continuity input that
Krein's representation theorem (the primary behind the named premise `KreinDecomp`)
requires of the kernel. -/
theorem continuous_Kpsi : Continuous GppKreinHPsi.Kpsi :=
  GppKreinKpsiContinuous.continuous_Kpsi
    archGammaFactorContinuous_proved archEnvelopeIntegrable_proved

end GppKreinKpsiContinuousGlue
