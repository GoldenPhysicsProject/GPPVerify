import Mathlib.Tactic

/-!
# Spin(10,2) chiral-alignment finite core

Finite algebra accompanying Daniel Toupin,
"Which Way Is Forward?", v19.

The manuscript derives from Clifford chirality multiplication that a positive
Spin(10,2) Weyl module branches under Spin(10) x Spin(2) as an aligned pair

  (16,+) + (16bar,-),

while the opposite Weyl chirality gives the anti-aligned pair.  In signature
(10,2) a Majorana-Weyl real structure exchanges the two complex K-types, so
they are conjugate components of one real object rather than independent
copies.

This Lean file formalizes only the finite sign and complex-conjugation core.
It does not formalize real Clifford-algebra classification or Lie-group
branching.
-/

namespace GppSpin102ChiralRealityCore

/-- Product chirality of two binary half-spin signs. -/
def chiralityProduct (q t : ℤ) : ℤ := q * t

/-- Aligned signs have positive product. -/
theorem aligned_signs_positive :
    chiralityProduct 1 1 = 1 ∧
    chiralityProduct (-1) (-1) = 1 := by
  norm_num [chiralityProduct]

/-- Anti-aligned signs have negative product. -/
theorem antialigned_signs_negative :
    chiralityProduct 1 (-1) = -1 ∧
    chiralityProduct (-1) 1 = -1 := by
  norm_num [chiralityProduct]

/-- Simultaneous reversal preserves product chirality. -/
theorem simultaneous_reversal_preserves_chirality (q t : ℤ) :
    chiralityProduct (-q) (-t) = chiralityProduct q t := by
  simp [chiralityProduct]

/-- Either single half flip reverses product chirality. -/
theorem one_half_flip_reverses_chirality (q t : ℤ) :
    chiralityProduct (-q) t = - chiralityProduct q t ∧
    chiralityProduct q (-t) = - chiralityProduct q t := by
  simp [chiralityProduct]

abbrev ConjugatePair := ℂ × ℂ

/-- Prototype anti-linear reality exchange between conjugate compact K-types. -/
def realityExchange (v : ConjugatePair) : ConjugatePair :=
  (star v.2, star v.1)

/-- The reality exchange is involutive. -/
theorem realityExchange_sq (v : ConjugatePair) :
    realityExchange (realityExchange v) = v := by
  rcases v with ⟨a,b⟩
  simp [realityExchange]

/-- A fixed vector is determined by either one of its complex components. -/
theorem reality_fixed_partner (v : ConjugatePair)
    (h : realityExchange v = v) :
    v.2 = star v.1 := by
  have h2 := congrArg Prod.snd h
  simpa [realityExchange] using h2.symm

/-- Conversely, one complex component and its conjugate form a real fixed pair. -/
theorem conjugate_pair_is_reality_fixed (a : ℂ) :
    realityExchange (a, star a) = (a, star a) := by
  simp [realityExchange]

/-- The conjugate components of a real pair have equal squared norm. -/
theorem reality_pair_equal_normSq (a : ℂ) :
    Complex.normSq (star a) = Complex.normSq a := by
  simp [Complex.normSq]

/-- One complex 16-dimensional component carries 32 real scalar components. -/
theorem complex16_real_dimension_count :
    16 * 2 = 32 := by
  norm_num

/-- The complexified Weyl carrier has two complex 16-dimensional K-types. -/
theorem complexified_k_type_dimension_count :
    16 + 16 = 32 := by
  norm_num

end GppSpin102ChiralRealityCore
