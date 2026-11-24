# GppVerify/StandardModel

The Standard Model sector: 132 files, half of them on CPT and
orientation. The organising fact is the same involution as everywhere in
the library, read on labels: a particle carries charge, parity, and a
time arrow as independent signs, and the observable is their product.

## Clusters

- **CPT and orientation.** The `CPT*`, `*Orientation*`, and
  `BlackMirror*` files: the paired orientation states, the fold that
  identifies CPT with a parity times an arrow flip, and the separation
  results (CPT does not by itself force antimatter; the diagonal gauge
  separates from the paired one). The arrow-form CPT theorem and its
  finite label model are in the `WhichWayForward*` files.
- **Charge.** The `Charge*` files: charge flip obstructions, the double
  transfer a charge flip requires, and relational charge on paired
  sheets.
- **Gauge structure.** `PrimePatiSalamCartan.lean` (the SU(3) sector of
  Pati–Salam read off the primes), anomaly bookkeeping on CPT sheets,
  and the orientation templates that tie the sector to the arithmetic
  side (`ArithmeticCoPoissonOrientationTemplate.lean`,
  `ArithmeticReciprocityOrientationParity.lean`).
- **No-goes kept as theorems.** `CPTSymmetryDoesNotForceAntimatter.lean`
  is the pattern of the library: a route that fails is a theorem
  locating the failure. The SU(2)_L × SU(2)_R construction is recorded
  as a no-go in the v26 line; SU(3) is present, in the Pati–Salam file
  above.

## Entry points

The CPT spine files for the orientation theory, and
`PrimePatiSalamCartan.lean` for the gauge sector.

Back to the [library README](../../README.md).
