import Mathlib

/-!
# The sphere's two grades: mirror symmetry does not imply one global spectral line

Daniel Toupin / Golden Physics Project; Codex discovery formalization.
A finite polynomial model of the grading issue in the projective-line zeta
identity zeta(P¹_Z,s) = zeta(s) * zeta(s-1).

We deliberately use an elementary polynomial seed rather than ξ: this gives an
UNCONDITIONAL counterexample to the inference from a whole-product functional
equation to zeros on the whole product's fixed line, without importing RH or
any unproved zeta-zero assertion.

The polynomial is NOT ζ, not a global arithmetic zeta, and the exact two-grade
cohomological interpretation for P¹ is a separate geometric input.
-/

namespace GppGradedSphere

/-- Model of one weight-zero symmetric spectral factor, with zero at 1/2. -/
def seed (s : ℂ) : ℂ := (s - (1 / 2 : ℂ)) ^ 2

/-- Model of the two Tate grades of the projective sphere. -/
def sphereModel (s : ℂ) : ℂ := seed s * seed (s - 1)

/-- The seed has its own involution about 1/2. -/
theorem seed_mirror (s : ℂ) : seed (1 - s) = seed s := by
  unfold seed
  ring

/-- The entire two-factor product has an involution about 1. -/
theorem sphere_global_mirror (s : ℂ) : sphereModel (2 - s) = sphereModel s := by
  unfold sphereModel seed
  ring

/-- The weight-zero factor contributes a zero on Re(s)=1/2. -/
theorem zero_weight_zero : sphereModel (1 / 2 : ℂ) = 0 := by
  norm_num [sphereModel, seed]

/-- The Tate-twisted weight-two factor contributes a zero on Re(s)=3/2. -/
theorem zero_weight_two : sphereModel (3 / 2 : ℂ) = 0 := by
  norm_num [sphereModel, seed]

/-- No zero at the whole product's mirror centre s=1 in this model. -/
theorem global_centre_nonzero : sphereModel (1 : ℂ) ≠ 0 := by
  norm_num [sphereModel, seed]

/-- Standard centre associated to a *motivic weight* w, not
    Deninger's auxiliary cohomological degree. -/
def motivicCentre (w : ℚ) : ℚ := (w + 1) / 2

theorem weight_zero_centre : motivicCentre 0 = 1 / 2 := by
  norm_num [motivicCentre]

theorem weight_one_centre : motivicCentre 1 = 1 := by
  norm_num [motivicCentre]

theorem weight_two_centre : motivicCentre 2 = 3 / 2 := by
  norm_num [motivicCentre]

/-- An honest Tate twist by one changes the motivic weight by two
and shifts its central point by one. -/
theorem tate_shift_centre (w : ℚ) :
    motivicCentre (w + 2) = motivicCentre w + 1 := by
  dsimp [motivicCentre]
  ring

/-- The formal effective motivic weight +1/2 of the shifted F_(1/4)
factor is not the image of an integer cohomological weight.
This does NOT exclude all possible non-geometric analytic twists. -/
theorem quarter_shift_weight_not_integral (n : ℤ) :
    (n : ℚ) ≠ (1 / 2 : ℚ) := by
  intro h
  have hlo : (0 : ℚ) < n := by rw [h]; norm_num
  have hhi : (n : ℚ) < 1 := by rw [h]; norm_num
  have hlo' : (0 : ℤ) < n := by exact_mod_cast hlo
  have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

#check sphere_global_mirror
#check quarter_shift_weight_not_integral
#print axioms sphere_global_mirror
#print axioms quarter_shift_weight_not_integral

end GppGradedSphere
