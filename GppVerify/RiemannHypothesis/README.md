# GppVerify/RiemannHypothesis

The Riemann Hypothesis programme of the library: 585 files carrying the
functional equation, the Tate layer, the explicit formula, the Weil
positivity reductions, and the finite certificates. Everything here is
kernel-checked with zero `sorry` and no axioms beyond the standard three;
what is open is named, as a stub or as an exact proposition.

## The reduction chain

- `WeilPositivityCriterion.lean`: the criterion in finite paired form, and
  `rh_iff_weil_pairedForm_nonneg`, RH iff the paired Weil form is
  nonnegative.
- The holographic reflection positivity file: positivity across the equator
  holds iff there are no off-equator mirror pairs
  (`reflectionForm_nonneg_iff`).
- The explicit formula is assembled in stages (E1, E2a real and complex,
  with the Mellin interpolation and autocorrelation transport files);
  GW-EF, the identification of the criterion-side Weil form with the
  arithmetic Weil form of the place split in `GlobalWeilPlaces.lean`,
  is the named open link.

## The Tate layer

Tate's thesis for ℚ: `SchwartzTateLocal.lean` and `SchwartzTateLocalFE.lean`
(local theory at the real place, both parities), `IdeleQ.lean`,
`IdeleClassGroupQ.lean` (Fujisaki for ℚ), `AdelicDiscrete.lean`,
`AdelicFundamentalDomain.lean`, `AdelicCovolume.lean` (covolume one),
`AdelicCharacter.lean` (the standard character, GP-DUAL: ℚ^⊥ = ℚ),
`AdelicPoissonStatement.lean` (the statement file; Poisson summation for the
whole class and the scaled formula stand as named open propositions),
`AdelicFiniteFourier.lean` and `AdelicFourierInversion.lean` (Fourier
inversion and Plancherel on the adelic Schwartz class, proved),
`AdelicFiniteDuality.lean` (self-duality of ∏_p ℤ_p, proved, which makes
the classical Poisson control unconditional), and `AdelicCarrier.lean`
(the bridge to Mathlib's adele ring). The full map is
[`docs/TATE-GUIDE.md`](../../docs/TATE-GUIDE.md).

## Certificates and sectors

- The Schur sector certificates: positivity of the sector form for
  K = 2 to 18, banked with the sector matrices.
- The AUG2 rational certificate: the K = 5 diagonal of the negative
  channel is the sum of the first two zero orbitals, in exact rational
  arithmetic; the orbital machinery is in `GppSpectralOrbitals` and the
  projection formulas in [`../Upstream/`](../Upstream/README.md).
- The Fisher layer: zeta Gibbs states, Fisher information and its
  nonnegativity (`CountableFisher*`, `ZetaGibbsFisher*`), and the
  Fisher-zero log-concavity no-go.
- Prime Poisson files (`FinitePrimePoisson*`, `GlobalPrimePoisson*`,
  `PrimePoissonRadial*`): the prime-side form of Poisson summation and
  its positive-type properties.

## Entry points

A reader new to this directory: `WeilPositivityCriterion.lean` for the
target, `AdelicPoissonStatement.lean` for the global construction, and
the Tate guide for the layer between them.

Back to the [library README](../../README.md).
