# GppVerify/CelestialHolography

The celestial side of the dictionary: 329 files on the shadow transform,
the principal series, and the geometry that carries them (Penrose
twistors, ambitwistor space, Grassmannians), together with the bridges
that identify this side with the arithmetic side.

## Clusters

- **Shadow and principal series.** `ConformalShadowPrincipalSeries.lean`
  (the general-d shadow algebra: the involution Δ ↦ d − Δ and its fixed
  locus), `PrincipalSeriesDilationBridge.lean`,
  `PrincipalSeriesShadowConjugation.lean`,
  `ArithmeticPrincipalSeriesSelection.lean`,
  `ArithmeticTemperedPrincipalSeries.lean`,
  `CompletedZetaPrincipalSeriesResponse.lean`: the dilation action, its
  unitarity, and the tempered spectrum, with the arithmetic selection
  rules that pick the zeta response out of the principal series.
- **Penrose and ambitwistor geometry.** The `Ambient*`, `Ambitwistor*`,
  and `Penrose*` files: incidence geometry, contact structures, ray
  quotients, and the intertwiners between the two pictures.
- **State sums and reconstruction.** The `*StateSum*` files: scalar,
  vector, and Fourier state sums and their reconstruction theorems, the
  finite models in which the dictionary is computed exactly.
- **Fourier and shadow diamonds.** The `Fourier*` and `*ShadowDiamond*`
  files: the split of the Fourier kernel by shadow polarity and the
  diamond geometry of the light cone in split signature.
- **Arithmetic defect files.** The `Arithmetic*` files beyond the
  principal series: completed-defect criteria, Euler log anomalies,
  no-ghost coercivity: the arithmetic side read in celestial language.

## Entry points

`ConformalShadowPrincipalSeries.lean` for the involution itself, and
`PrincipalSeriesDilationBridge.lean` for the bridge to the arithmetic
dilation action. The arithmetic mirror of this directory is
[`../RiemannHypothesis/`](../RiemannHypothesis/README.md).

Back to the [library README](../../README.md).
