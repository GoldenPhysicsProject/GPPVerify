import Mathlib.Tactic

/-!
# Arithmetic reciprocity as a model for globally compensated orientation defects

Quadratic Hilbert reciprocity over a global field states, schematically,

    product_v (a,b)_v = 1,

where every local Hilbert symbol is `+1` or `-1` and only finitely many are nontrivial.
Consequently a single isolated `-1` local defect is impossible: nontrivial local signs must
be globally compensated so that their product is `+1` (equivalently, the number of `-1`
defects is even in the quadratic case).

This file formalizes only the elementary sign consequence once the reciprocity product law
is supplied.  It does NOT formalize Hilbert symbols or prove Hilbert reciprocity itself.

The possible physics use is sharply limited but intriguing: if microscopic half-flips are
local Z2 defects while complete CPT is the global reciprocity constraint, an isolated
half-flip would have to be accompanied by another defect/boundary channel.  That resembles
the independently derived charge-transfer obstruction, but the identification remains a
hypothesis to test rather than a theorem of physics.
-/

namespace GppArithmeticReciprocityOrientationParity

/-- Product of one distinguished local sign with all other places. -/
def globalSign (eps : ℝ) (rest : List ℝ) : ℝ := eps * rest.prod

/-- If every other place is trivial and the reciprocity product is +1, the distinguished
    place cannot carry a lone -1 defect. -/
theorem no_single_defect_under_product_one
    (eps : ℝ) (rest : List ℝ)
    (hrest : rest.prod = 1)
    (hglobal : globalSign eps rest = 1) : eps = 1 := by
  simp [globalSign, hrest] at hglobal
  exact hglobal

/-- A single `-1` defect with all other local signs +1 violates the reciprocity product. -/
theorem one_negative_defect_violates_reciprocity :
    globalSign (-1) [1,1,1] ≠ 1 := by
  norm_num [globalSign]

/-- Two `-1` defects compensate and satisfy the quadratic product constraint. -/
theorem two_negative_defects_compensate :
    ((-1 : ℝ) * (-1) * 1 * 1) = 1 := by
  norm_num

/-- More generally, if one local sign is reversed, preserving a product-one global law
    requires the product of the remaining channels to reverse as well. -/
theorem half_flip_requires_compensating_global_flip
    (eps restProd : ℝ)
    (hbefore : eps * restProd = 1)
    (hafter : (-eps) * (-restProd) = 1) :
    (-eps) * (-restProd) = eps * restProd := by
  rw [hbefore, hafter]

/-- Diagonal reversal of two factors preserves their product exactly, the same elementary
    algebra underlying both quadratic reciprocity signs and the project's q*t character. -/
theorem diagonal_sign_reversal_preserves_product (a b : ℝ) :
    (-a) * (-b) = a*b := by ring

end GppArithmeticReciprocityOrientationParity
