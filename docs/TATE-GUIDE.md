# The Tate Layer of GPPVerify: A Guide

This guide identifies the Tate's thesis layer of the GPPVerify library: the
local Tate theory at the real place and the global theory on the adeles of
ℚ, with the file for each result, its principal declarations, and its
dependencies. It is written for a reader who wants to find, cite, or reuse
a specific result without reading the whole tree.

**Pin.** Repository `GoldenPhysicsProject/GPPVerify`, branch `main`,
commit `5431ff4861d661d2eb4d7924742c00bd84d97b6b` (the merge of PR #530,
2026-11-09). License Apache-2.0. Author Daniel Toupin, ORCID
0009-0003-7682-9579; see `CITATION.cff` in the repository. Everything
named below is kernel-checked in the full root build with no `sorry`, no
`admit`, and no axioms beyond the standard three (`propext`,
`Classical.choice`, `Quot.sound`), unless it is listed under *Open* at the
end.

The layer is 18 files and about 3,600 lines. The carrier throughout is
the concrete adele ring `AQ := ℝ × 𝔸_f`, where `𝔸_f` is Mathlib's
`FiniteAdeleRing ℤ ℚ`, with Haar measure `adeleHaar` normalized as
Lebesgue measure at the infinite place and `vol(∏_p ℤ_p) = 1` at the
finite places.

## The four headline results

1. **Local functional equation (both parities).** For a Schwartz function
   on ℝ of parity `ε ∈ {0, 1}`, the local Tate zeta integral satisfies
   the functional equation in the strip `0 < Re s < 1`, with gamma factor
   `γ_ℝ(s, ε) = (−i)^ε · A_ε(1−s)/A_ε(s)` and cocycle
   `γ(s)γ(1−s) = (−1)^ε`. Files: `SchwartzTateLocal.lean`,
   `SchwartzTateLocalFE.lean`, on the evaluations in
   `LocalTateEvaluations.lean` and `ArchimedeanTateParity.lean`.
2. **GP-DUAL: `ℚ^⊥ = ℚ`.** For the standard adelic character
   `adeleChar`, an adele `a` pairs trivially with every diagonal rational
   if and only if `a` is itself a diagonal rational:
   `forall_adeleChar_principal_mul_eq_one_iff`. File:
   `AdelicCharacter.lean` (PR #526).
3. **Covolume one.** The fundamental domain `fundBox` of ℚ in `AQ` has
   `covolume_eq_one` under the pinned normalization, proved as a
   computation from that normalization. Files: `AdelicDiscrete.lean`,
   `AdelicFundamentalDomain.lean`, `AdelicCovolume.lean`, with the finite
   Haar measure in `Upstream/RatFiniteAdeleRingHaar.lean`
   (`haar_integralAdeles : haar integralAdeles = 1`).
4. **Self-duality of `∏_p ℤ_p`, and the classical Poisson control made
   unconditional.** The finite Fourier transform of the indicator of the
   integral adeles is itself: `finFourierIntegralSelfDual`
   (`AdelicFiniteDuality.lean`, PR #530). With it, the control theorem of
   the Poisson statement file, `poissonSummation_pureTensor_integral`,
   holds with no hypothesis: for `φ ⊗ 1_{∏ℤ_v}`, adelic Poisson summation
   is Mathlib's classical `SchwartzMap.tsum_eq_tsum_fourier` over ℤ.

## Local layer

Dependencies run downward: each file imports the ones above it in its
group.

- **`LocalTateEvaluations.lean`** (206 lines). The raw evaluations:
  `gaussian`, `localZeta`, `localZeta_even_split`, `localZeta_half_line`,
  `archimedean_evaluation`, `archimedean_evaluation_Gamma`, and the finite
  place evaluation `finite_evaluation`. No GppVerify imports; the base of
  the local layer.
- **`ArchimedeanTateParity.lean`**. The parity package: `archFactor`,
  `archPhase`, `testVector`, `parityZeta`; the test vector's zeta
  evaluation `parityZeta_testVector_eq_localZeta`, its Fourier transform
  `fourier_testVector`, and the test-vector local functional equation
  `localFE_testVector`. The archimedean phases are `+1` (even) and `−i`
  (odd). Imports `LocalTateEvaluations`.
- **`SchwartzTateLocal.lean`** (143 lines). Convergence and the gamma
  ratio for general rapidly decaying functions: `RapidDecay` estimates,
  `schwartz_parityZeta_integrable`, `gammaRatio`,
  `archFactor_ne_zero_strip`, `gammaRatio_mul_gammaRatio_one_sub` (the
  cocycle). Imports `ArchimedeanTateParity`.
- **`SchwartzTateLocalFE.lean`** (560 lines). The general local functional
  equation for Schwartz functions of either parity in the strip, built
  through the subordination integrals (`subord_integral`,
  `real_subord_integral`, `norm_subord`). Imports `SchwartzTateLocal`.

## Ideles

- **`IdeleGroup.lean`** (147 lines). The idele group of ℚ, the diagonal
  embedding `diagonalEmbedding` and its injectivity.
- **`IdeleQ.lean`** (584 lines). The per-place norm `lnorm` and its
  multiplicativity, `prodQ` (an idele of norm `q`), `exists_prodQ_eq`,
  `exists_rat_norm`; the header fixes `haarK1`, the Haar probability
  measure on the norm-one ideles `K¹ = 𝔸¹/ℚˣ`.
- **`IdeleClassGroupQ.lean`** (210 lines). The idele class group of ℚ,
  its Haar measure `haarCQ`, and Fujisaki's theorem for ℚ in positive-type
  form (`adelic_haar_square_positive_type`). Imports `IdeleQ`.

## Global layer: discreteness, domain, covolume

- **`AdelicPoissonCore.lean`**. The arithmetic core lemmas
  (`den_eq_one_of_padicNorm_le_one`,
  `eq_zero_of_integral_of_abs_lt_one`).
- **`AdelicDiscrete.lean`**. The diagonal `principal`, the boxes `intBox`
  and `box`, and discreteness: `principal_discrete`. Imports `IdeleQ`,
  `AdelicPoissonCore`.
- **`AdelicFundamentalDomain.lean`**. Strong approximation
  (`exists_rat_sub_mem_integers`), the fundamental domain `fundBox`, and
  the tiling statement `existsUnique_sub_principal_mem_fundBox`. Imports
  `AdelicDiscrete`.
- **`Upstream/RatFiniteAdeleRingHaar.lean`** (182 lines). Haar measure on
  `𝔸_f`: `integralAdeles` is compact and open, `haar` is defined, and
  `haar_integralAdeles : haar integralAdeles = 1`. Written Mathlib-only,
  in Mathlib's naming; see *Upstream staging* below.
- **`AdelicCovolume.lean`**. `adeleHaar`, `covolume`, and
  `covolume_eq_one`. Imports `AdelicFundamentalDomain`,
  `RatFiniteAdeleRingHaar`.

## Global layer: character and Poisson

- **`AdelicCharacter.lean`** (PR #526). The fractional-part character
  `e`, its representative machinery (`IsRep`, `isRep_principal`), and the
  standard character `adeleChar : AddChar AQ Circle`, defined globally
  through a rational representative of the finite part
  (`adeleChar_eq_of_isRep`: `ψ x = e(x_∞ − q)` for any `q` with `x_f − q`
  everywhere integral, independent of the choice of `q`). Proved:
  continuity, nontriviality, triviality on ℚ and on `∏ℤ_v`, and GP-DUAL
  above. Its split into the archimedean factor times `finChar` is
  `adeleChar_split` in `AdelicPoissonStatement.lean`; the factorization of
  `finChar` as a product of local characters, place by place, is not yet
  proved. Imports `AdelicFundamentalDomain`.
- **`AdelicPoissonStatement.lean`** (292 lines, PR #527). The statement
  file of the layer. Proved in it: the character split `adeleChar_split`
  (ψ is the archimedean factor times `finChar`), `finChar_integral`, the
  phases `archimedean_phase_even` (`+1`) and `archimedean_phase_odd`
  (`−i`) computed through ψ itself, the Schwartz–Bruhat class as the span
  of pure tensors (`pureTensor`, `IsSchwartzBruhat`), Fourier
  factorization on pure tensors `adelicFourier_pureTensor`, the boundary
  split `boundary_split` (from Poisson summation alone, no further
  hypothesis), and the GP-DUAL kernel collapse. Imports
  `AdelicCovolume`, `AdelicCharacter`, `SchwartzTateLocalFE`.
- **`AdelicFiniteDuality.lean`** (145 lines, PR #530). The self-duality
  proof: `finChar_eq_one_iff` (the finite character is trivial exactly on
  `intBox`), the subring properties of `intBox`, and
  `finFourierIntegralSelfDual`. Imports `AdelicPoissonStatement`,
  `AdelicCovolume`.

## The Mathlib carrier bridge

- **`Upstream/RatAdeleRingEquiv.lean`** (68 lines, PR #529).
  `Rat.AdeleRing.ringEquivProd : AdeleRing ℤ ℚ ≃+* ℝ × FiniteAdeleRing ℤ ℚ`
  and the matching homeomorphism, with the diagonal law
  `ringEquivProd_algebraMap`. Mathlib-only, in Mathlib's naming.
- **`AdelicCarrier.lean`** (PR #529). Transport across that equivalence:
  the diagonal agrees (`principal_eq_ringEquivProd_algebraMap`),
  discreteness (`discrete_range_algebraMap`) and cocompactness
  (`compactSpace_adele_quotient`) hold for Mathlib's carrier. This file is
  a leaf by design: the Haar theory stays on the concrete carrier.

## Open, stated as named propositions

The following are stated exactly, as `Prop` definitions to be proved, in
`AdelicPoissonStatement.lean`. They are not axioms and no result above
depends on them except where a hypothesis is named.

- `AdelicPoissonSummation`: Poisson summation on `AQ` for the full
  Schwartz–Bruhat class.
- `AdelicFourierInversion`: `F (F f) x = f (−x)`.
- `AdelicPlancherel`: the Fourier transform is an isometry on `L²(AQ)`.
- `HaarScaling`: the scaling law of `adeleHaar` under idele dilation,
  through `ideleNorm`.
- `AdelicPoissonScaled`: the idele-scaled Poisson formula (GZ5).

**GW-EF**, the identification of the criterion-side Weil form with the
arithmetic Weil form of the place split (`GlobalWeilPlaces.lean`,
`weilForm_eq_pole_add_places`), is open and is the named link between
this layer and the explicit formula. It belongs to the neighboring Weil
layer, not to the Tate layer.

## Not part of this layer

`AdelicL2.lean` is a stub-era file whose statements are placeholders. It
is superseded by the files above and is not citable as part of the Tate
layer.

## Upstream staging

Two files of this layer live in `GppVerify/Upstream/` and are written to
Mathlib conventions throughout (`RatFiniteAdeleRingHaar.lean`,
`RatAdeleRingEquiv.lean`), as are the other files of that folder (the
Weierstrass and entire-function order-of-growth cluster and
`TwoVectorProjection.lean`). They are the library's staging area for
eventual Mathlib contribution; at the pin above, none has been sent.

---

Daniel Toupin / Golden Physics Project, with AI assistance from Turbo
(drafted at Daniel's direction, following a suggestion by Astra) and
Claude Code (placed in the repository; one wording correction in the
`AdelicCharacter.lean` entry, where the character is defined globally and
not yet as a product of local characters).
