import Mathlib.Tactic

/-!
# Prime-square-root Cayley algebra

Elementary algebraic core of the local TFD / Dirichlet-to-Neumann block after
writing q = sqrt(p). No RH claim and no arithmetic distribution input.
-/

namespace GppPrimeSqrtCayley

noncomputable def cayleyBeta (q : ℝ) : ℝ := (q - 1) / (q + 1)

noncomputable def diagEntry (q : ℝ) : ℝ :=
  (q^2 + 1) / (2 * (q^2 - 1))

noncomputable def offEntry (q : ℝ) : ℝ :=
  q / (q^2 - 1)

/-- The symmetric local block eigenvalue in the (1,1) direction. -/
theorem diag_sub_off_eq
    {q : ℝ} (hq1 : q ≠ 1) (hqm1 : q ≠ -1) :
    diagEntry q - offEntry q = (q - 1) / (2 * (q + 1)) := by
  have hsub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hadd : q + 1 ≠ 0 := by
    intro h
    apply hqm1
    linarith
  have hden : q ^ 2 - 1 ≠ 0 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by ring]
    exact mul_ne_zero hsub hadd
  unfold diagEntry offEntry
  field_simp [hden, hsub, hadd]
  ring

/-- The antisymmetric local block eigenvalue in the (1,-1) direction. -/
theorem diag_add_off_eq
    {q : ℝ} (hq1 : q ≠ 1) (hqm1 : q ≠ -1) :
    diagEntry q + offEntry q = (q + 1) / (2 * (q - 1)) := by
  have hsub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hadd : q + 1 ≠ 0 := by
    intro h
    apply hqm1
    linarith
  have hden : q ^ 2 - 1 ≠ 0 := by
    rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by ring]
    exact mul_ne_zero hsub hadd
  unfold diagEntry offEntry
  field_simp [hden, hsub, hadd]
  ring

/-- The two local eigenvalues form an exact reciprocal pair with product 1/4. -/
theorem eigenvalue_product_quarter
    {q : ℝ} (hq1 : q ≠ 1) (hqm1 : q ≠ -1) :
    (diagEntry q - offEntry q) * (diagEntry q + offEntry q) = (1 : ℝ) / 4 := by
  have hsub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hadd : q + 1 ≠ 0 := by
    intro h
    apply hqm1
    linarith
  rw [diag_sub_off_eq hq1 hqm1, diag_add_off_eq hq1 hqm1]
  field_simp [hsub, hadd]
  ring

/-- The lower eigenvalue is one half of the Cayley coordinate. -/
theorem lower_eq_half_cayley
    {q : ℝ} (hq1 : q ≠ 1) (hqm1 : q ≠ -1) :
    diagEntry q - offEntry q = cayleyBeta q / 2 := by
  have hadd : q + 1 ≠ 0 := by
    intro h
    apply hqm1
    linarith
  rw [diag_sub_off_eq hq1 hqm1]
  unfold cayleyBeta
  field_simp [hadd]
  ring

/-- Inversion q -> q^{-1} flips the Cayley coordinate. -/
theorem cayleyBeta_inv
    {q : ℝ} (hq0 : q ≠ 0) :
    cayleyBeta q⁻¹ = -cayleyBeta q := by
  unfold cayleyBeta
  field_simp [hq0]
  ring


/--
Multiplication becomes the Einstein/Mobius addition law in the square-root
Cayley coordinate, in cross-multiplied form.
-/
theorem cayleyBeta_mul_cross
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    cayleyBeta (q * r) * (1 + cayleyBeta q * cayleyBeta r) =
      cayleyBeta q + cayleyBeta r := by
  have hq1 : q + 1 ≠ 0 := by positivity
  have hr1 : r + 1 ≠ 0 := by positivity
  have hqr1 : q * r + 1 ≠ 0 := by positivity
  unfold cayleyBeta
  field_simp [hq1, hr1, hqr1]
  ring

/--
A positive diagonal metric component cannot be invariant under a nontrivial
reciprocal dilation.  This is the scalar core of the two-dimensional
boost-versus-Hilbert-unitarity rigidity argument.
-/
theorem positive_diag_invariance_forces_unit_scale
    {r g : ℝ} (hr : 0 < r) (hg : 0 < g)
    (hinv : r ^ 2 * g = g) :
    r = 1 := by
  have hfactor : (r ^ 2 - 1) * g = 0 := by
    calc
      (r ^ 2 - 1) * g = r ^ 2 * g - g := by ring
      _ = 0 := by rw [hinv]; ring
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hr2 : r ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hg0
  have hr_sq : r ^ 2 = 1 := by linarith
  nlinarith

end GppPrimeSqrtCayley

#print axioms GppPrimeSqrtCayley.diag_sub_off_eq
#print axioms GppPrimeSqrtCayley.diag_add_off_eq
#print axioms GppPrimeSqrtCayley.eigenvalue_product_quarter
#print axioms GppPrimeSqrtCayley.lower_eq_half_cayley
#print axioms GppPrimeSqrtCayley.cayleyBeta_inv
#print axioms GppPrimeSqrtCayley.cayleyBeta_mul_cross
#print axioms GppPrimeSqrtCayley.positive_diag_invariance_forces_unit_scale
