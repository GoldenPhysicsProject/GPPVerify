import Mathlib.Tactic

/-!
# Five-dimensional Ward reconstruction of a four-dimensional massive-vector projector

A massive four-dimensional vector obtained from a five-dimensional massless gauge field
has cut momentum `K = (p, κ)` with `p^2 = κ^2 = μ^2`.  The correct Ward identity is

  p · J₄ = κ J₅,

not, in general, `p · J₄ = 0`.

This file formalizes the scalar algebraic core showing that the longitudinal term of the
four-dimensional massive polarization projector exactly reconstructs the fifth-current
contribution.  It also packages the two independent projector factors that occur in a
rank-two cut and makes explicit the term lost by replacing a massive projector by a bare
four-dimensional metric contraction.
-/

namespace GppMassiveVectorWardReconstruction

/-- If the five-dimensional Ward identities give `p·J = κ J₅` on both sides of a
cut and `μ² = κ²`, then the longitudinal massive-projector term is exactly `J₅L J₅R`. -/
theorem longitudinal_term_eq_fifth_current
    {pJL pJR jL5 jR5 κ μ : ℝ}
    (hμ : μ ^ 2 = κ ^ 2)
    (hμ0 : μ ≠ 0)
    (hL : pJL = κ * jL5)
    (hR : pJR = κ * jR5) :
    pJL * pJR / μ ^ 2 = jL5 * jR5 := by
  rw [hL, hR, hμ]
  have hκ0 : κ ≠ 0 := by
    intro hκ
    rw [hκ, zero_pow (by norm_num)] at hμ
    have : μ ^ 2 = 0 := hμ
    exact hμ0 (sq_eq_zero_iff.mp this)
  field_simp [hκ0]
  ring

/-- Consequently the four-dimensional massive-vector projector contraction equals the
negative five-dimensional metric contraction, written here as its 4D and fifth pieces. -/
theorem massive_projector_eq_fiveDim_contraction
    {j4dot pJL pJR jL5 jR5 κ μ : ℝ}
    (hμ : μ ^ 2 = κ ^ 2)
    (hμ0 : μ ≠ 0)
    (hL : pJL = κ * jL5)
    (hR : pJR = κ * jR5) :
    -j4dot + pJL * pJR / μ ^ 2 = -j4dot + jL5 * jR5 := by
  rw [longitudinal_term_eq_fifth_current hμ hμ0 hL hR]

/-- The amount omitted by a bare four-dimensional metric replacement is exactly the
fifth-current product.  Thus the metric shortcut is valid only when this term vanishes. -/
theorem massive_projector_sub_bare_metric_eq_fifth_current
    {j4dot pJL pJR jL5 jR5 κ μ : ℝ}
    (hμ : μ ^ 2 = κ ^ 2)
    (hμ0 : μ ≠ 0)
    (hL : pJL = κ * jL5)
    (hR : pJR = κ * jR5) :
    (-j4dot + pJL * pJR / μ ^ 2) - (-j4dot) = jL5 * jR5 := by
  rw [massive_projector_eq_fiveDim_contraction hμ hμ0 hL hR]
  ring

/-- In the rank-two sewing problem the two massive-vector polarization projectors must
be reconstructed independently.  Their product is exactly the product of the two
corresponding five-dimensional contractions. -/
theorem double_massive_projector_eq_fiveDim_product
    {j4dot₁ pJL₁ pJR₁ jL5₁ jR5₁ κ₁ μ₁ : ℝ}
    {j4dot₂ pJL₂ pJR₂ jL5₂ jR5₂ κ₂ μ₂ : ℝ}
    (hμ₁ : μ₁ ^ 2 = κ₁ ^ 2)
    (hμ₁0 : μ₁ ≠ 0)
    (hL₁ : pJL₁ = κ₁ * jL5₁)
    (hR₁ : pJR₁ = κ₁ * jR5₁)
    (hμ₂ : μ₂ ^ 2 = κ₂ ^ 2)
    (hμ₂0 : μ₂ ≠ 0)
    (hL₂ : pJL₂ = κ₂ * jL5₂)
    (hR₂ : pJR₂ = κ₂ * jR5₂) :
    (-j4dot₁ + pJL₁ * pJR₁ / μ₁ ^ 2) *
        (-j4dot₂ + pJL₂ * pJR₂ / μ₂ ^ 2) =
      (-j4dot₁ + jL5₁ * jR5₁) *
        (-j4dot₂ + jL5₂ * jR5₂) := by
  rw [massive_projector_eq_fiveDim_contraction hμ₁ hμ₁0 hL₁ hR₁]
  rw [massive_projector_eq_fiveDim_contraction hμ₂ hμ₂0 hL₂ hR₂]

/-- The exact error made by replacing both massive-vector projectors by bare 4D metric
contractions.  There are three omitted pieces: the two single-longitudinal cross terms
and the double-longitudinal term. -/
theorem double_projector_sub_double_bare_metric
    {j4dot₁ pJL₁ pJR₁ jL5₁ jR5₁ κ₁ μ₁ : ℝ}
    {j4dot₂ pJL₂ pJR₂ jL5₂ jR5₂ κ₂ μ₂ : ℝ}
    (hμ₁ : μ₁ ^ 2 = κ₁ ^ 2)
    (hμ₁0 : μ₁ ≠ 0)
    (hL₁ : pJL₁ = κ₁ * jL5₁)
    (hR₁ : pJR₁ = κ₁ * jR5₁)
    (hμ₂ : μ₂ ^ 2 = κ₂ ^ 2)
    (hμ₂0 : μ₂ ≠ 0)
    (hL₂ : pJL₂ = κ₂ * jL5₂)
    (hR₂ : pJR₂ = κ₂ * jR5₂) :
    (-j4dot₁ + pJL₁ * pJR₁ / μ₁ ^ 2) *
        (-j4dot₂ + pJL₂ * pJR₂ / μ₂ ^ 2) -
      ((-j4dot₁) * (-j4dot₂)) =
    (-j4dot₁) * (jL5₂ * jR5₂) +
      (jL5₁ * jR5₁) * (-j4dot₂) +
      (jL5₁ * jR5₁) * (jL5₂ * jR5₂) := by
  rw [double_massive_projector_eq_fiveDim_product
    hμ₁ hμ₁0 hL₁ hR₁ hμ₂ hμ₂0 hL₂ hR₂]
  ring

end GppMassiveVectorWardReconstruction

#print axioms GppMassiveVectorWardReconstruction.longitudinal_term_eq_fifth_current
#print axioms GppMassiveVectorWardReconstruction.massive_projector_eq_fiveDim_contraction
#print axioms GppMassiveVectorWardReconstruction.massive_projector_sub_bare_metric_eq_fifth_current
#print axioms GppMassiveVectorWardReconstruction.double_massive_projector_eq_fiveDim_product
#print axioms GppMassiveVectorWardReconstruction.double_projector_sub_double_bare_metric
