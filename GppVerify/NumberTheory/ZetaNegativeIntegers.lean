import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# ζ(-3) = 1/120, corrected from a sign error

Source: decoding_reality_v43221.tex asserts `ζ(-3) = -1/120` (used as an input to a
zeta-regularized sum). The correct value, via the classical formula
`ζ(-k) = -B'_{k+1}/(k+1)` for the Bernoulli numbers `B'_n` (Mathlib's `bernoulli'`,
with `B'_1 = +1/2`), is `ζ(-3) = -B'_4/4 = -(-1/30)/4 = +1/120`: the source's sign is
wrong. Both the Mathlib special-value lemma
(`riemannZeta_neg_nat_eq_bernoulli'`) and the numeric value of `bernoulli' 4`
(`bernoulli'_four`) already exist in Mathlib, so this is a fully clean, no-gap proof —
independently checked against the classical value 1/120 via SymPy before formalizing.
-/

namespace GppZetaNegativeIntegers

/-- **ζ(-3) = 1/120** (not `-1/120` as asserted in the source), via Mathlib's
    `riemannZeta_neg_nat_eq_bernoulli'` special-value formula and `bernoulli'_four`. -/
theorem riemannZeta_neg_three : riemannZeta (-3 : ℂ) = 1 / 120 := by
  norm_num [riemannZeta_neg_nat_eq_bernoulli' 3, bernoulli'_four]

end GppZetaNegativeIntegers
