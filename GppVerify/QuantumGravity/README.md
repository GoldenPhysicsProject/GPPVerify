# GppVerify/QuantumGravity

Quantum gravity in the library's language: 53 files centred on causal
diamonds, the equator of the shadow involution read as a horizon, and
the Fisher geometry of the states on it.

## Clusters

- **Causal diamonds.** The `CausalDiamond*` files: the Fisher
  cancellation across the diamond, the gamma bridge, boundary terms and
  their cancellations; the companion GR forms are in
  [`../GeneralRelativity/`](../GeneralRelativity/).
- **Equator files.** `EquatorSU2.lean`, `EquatorThermalBound.lean`: the
  equator as a thermal boundary, its SU(2) action, and the bounds the
  thermality imposes.
- **Fisher and information geometry.** `FiniteWeightedCovarianceSymmetrization.lean`,
  `CumulantLaw.lean`, `FubiniStudyLocalKahler.lean`: the metric side of
  the state space, cumulants, and the local Kähler structure.
- **Special functions of the theory.** `Digamma.lean` (the Gauss series
  for the digamma function, proved here and used across the library),
  `AllLoopFiniteness.lean`, `BornRuleHaar.lean`.

## Entry points

`CausalDiamondFisherCancellation.lean` for the diamond programme, and
`Digamma.lean` for a self-contained result used everywhere else.

Back to the [library README](../../README.md).
