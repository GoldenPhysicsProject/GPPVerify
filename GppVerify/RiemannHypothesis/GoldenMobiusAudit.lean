import GppVerify.ThreadWeilParity.SuzukiReflectionSymmetry
import Mathlib.Tactic

/-!
# Golden Möbius audit

This file tests, exactly and without numerical fitting, whether the Möbius transformations
already present in the RH boundary program contain the golden-ratio dynamics

  x ↦ 1 + 1/x.

The answer is nuanced:

* the critical Cayley shadow map is x ↦ 1 - 1/x, so the golden map is obtained by
  precomposing it with the sign involution x ↦ -x;
* the even/odd Sherman--Morrison rank-one transforms become translations by ∓1 after
  the reciprocal coordinate y = 2/x;
* if that translation is combined with the reciprocal involution y ↦ 1/y, the resulting
  map is exactly y ↦ 1 + 1/y.

This is an algebraic structural observation only. No identification of the reciprocal
involution with the concrete arithmetic boundary transfer is asserted here.
-/

namespace GppGoldenMobius

noncomputable section

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

def cayleyShadow (x : ℝ) : ℝ := 1 - 1 / x

def goldenMap (x : ℝ) : ℝ := 1 + 1 / x

/-- The sign-twisted critical Cayley shadow is exactly the golden Möbius map. -/
theorem goldenMap_eq_cayleyShadow_neg (x : ℝ) :
    goldenMap x = cayleyShadow (-x) := by
  simp [goldenMap, cayleyShadow]

/-- The golden ratio satisfies its defining quadratic equation. -/
theorem goldenRatio_sq :
    goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem goldenRatio_pos : 0 < goldenRatio := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  dsimp [goldenRatio]
  positivity


/-- Reciprocal of the golden ratio in its standard affine form. -/
theorem one_div_goldenRatio :
    1 / goldenRatio = goldenRatio - 1 := by
  have hphi0 : goldenRatio ≠ 0 := ne_of_gt goldenRatio_pos
  have hsq := goldenRatio_sq
  field_simp [hphi0]
  nlinarith

/-- The stable multiplier / inverse-square golden constant. -/
theorem one_div_goldenRatio_sq :
    1 / (goldenRatio ^ 2) = (3 - Real.sqrt 5) / 2 := by
  have hphi0 : goldenRatio ≠ 0 := ne_of_gt goldenRatio_pos
  calc
    1 / (goldenRatio ^ 2) = (1 / goldenRatio) ^ 2 := by
      field_simp [hphi0]
    _ = (goldenRatio - 1) ^ 2 := by rw [one_div_goldenRatio]
    _ = 2 - goldenRatio := by
      nlinarith [goldenRatio_sq]
    _ = (3 - Real.sqrt 5) / 2 := by
      unfold goldenRatio
      ring

/-- The exact dyadic Hardy-atlas precision margin is φ⁻². -/
theorem dyadic_margin_eq_golden_inv_sq :
    (1 - 1 / Real.sqrt 5) / (1 + 1 / Real.sqrt 5)
      = 1 / (goldenRatio ^ 2) := by
  have hspos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 5 ≠ 0 := ne_of_gt hspos
  have hden : 1 + 1 / Real.sqrt 5 ≠ 0 := by positivity
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [one_div_goldenRatio_sq]
  field_simp [hs0, hden]
  nlinarith


/-- Any nonzero solution of x²=x+1 is a fixed point of the golden map. -/
theorem goldenMap_fixed_of_quadratic
    {x : ℝ} (hx : x ≠ 0) (hquad : x ^ 2 = x + 1) :
    goldenMap x = x := by
  unfold goldenMap
  field_simp [hx]
  nlinarith

theorem goldenRatio_fixed :
    goldenMap goldenRatio = goldenRatio := by
  apply goldenMap_fixed_of_quadratic
  · exact ne_of_gt goldenRatio_pos
  · exact goldenRatio_sq

/-- In contrast, the untwisted Cayley-shadow map has no real nonzero fixed point. -/
theorem cayleyShadow_no_real_fixed
    {x : ℝ} (hx : x ≠ 0) :
    cayleyShadow x ≠ x := by
  intro h
  unfold cayleyShadow at h
  field_simp [hx] at h
  have hs : 0 ≤ (x - (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

/-- Odd rank-one Sherman--Morrison transform. -/
def oddSchur (x : ℝ) : ℝ := 2 * x / (x + 2)

/-- Even rank-one Sherman--Morrison transform. -/
def evenSchur (x : ℝ) : ℝ := -2 * x / (x - 2)

/-- Reciprocal projective coordinate in which the Schur transforms linearize. -/
def reciprocalCoord (x : ℝ) : ℝ := 2 / x

/-- The odd rank-one update is translation by +1 in y=2/x. -/
theorem reciprocalCoord_oddSchur
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (oddSchur x) = reciprocalCoord x + 1 := by
  unfold reciprocalCoord oddSchur
  field_simp [hx]
  ring

/-- The even rank-one update is translation by -1 in y=2/x. -/
theorem reciprocalCoord_evenSchur
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (evenSchur x) = reciprocalCoord x - 1 := by
  unfold reciprocalCoord evenSchur
  field_simp [hx]
  ring

/-- The two Sherman--Morrison Möbius transformations are mutual inverses away from poles. -/
theorem oddSchur_evenSchur
    {x : ℝ} (hx : x ≠ 2) :
    oddSchur (evenSchur x) = x := by
  unfold oddSchur evenSchur
  field_simp [hx]
  ring

/-- The reciprocal involution in the y-coordinate corresponds to x ↦ 4/x. -/
def poleDual (x : ℝ) : ℝ := 4 / x

theorem reciprocalCoord_poleDual
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (poleDual x) = 1 / reciprocalCoord x := by
  unfold reciprocalCoord poleDual
  field_simp [hx]
  ring

/--
Translation by +1 after reciprocal duality is the golden map.

This is the exact modular-looking algebraic pattern T ∘ R, but the theorem deliberately
does not claim that poleDual is the arithmetic reflection of the completed RH system.
-/
theorem schur_duality_golden
    {x : ℝ} (hx : x ≠ 0) :
    reciprocalCoord (oddSchur (poleDual x))
      = goldenMap (reciprocalCoord x) := by
  unfold reciprocalCoord oddSchur poleDual goldenMap
  field_simp [hx]
  ring


/-! ## Actual shadow coordinates from the RH program -/

/-- The scalar Cayley coordinate used in the RH program: β(s)=(s-1)/s. -/
def criticalCayley (s : ℂ) : ℂ := (s - 1) / s

/-- Functional-equation shadow acts by reciprocal inversion on the actual Cayley
coordinate β(s). -/
theorem criticalCayley_shadow_eq_inv
    {s : ℂ} (_hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    criticalCayley (1 - s) = (criticalCayley s)⁻¹ := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold criticalCayley
  field_simp [h1s, hs1']
  ring

/-- The projective half-density coordinate w=exp(2π(s-1/2)). -/
def projectiveShadowCoord (s : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi : ℂ) * (s - (1 / 2 : ℂ)))

/-- Shadow is reciprocal inversion also in the exponential projective coordinate. -/
theorem projectiveShadowCoord_shadow_eq_inv (s : ℂ) :
    projectiveShadowCoord (1 - s) = (projectiveShadowCoord s)⁻¹ := by
  unfold projectiveShadowCoord
  have hcenter : (1 - s) - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) := by ring
  rw [hcenter, mul_neg, Complex.exp_neg]

/-- Generic completed shadow quotient; the BPY/de Branges phase has this form. -/
def shadowQuotient (F : ℂ → ℂ) (a z : ℂ) : ℂ :=
  F (a + z) / F (a - z)

/-- Reversing the spectral variable swaps numerator and denominator, hence inverts the
completed shadow quotient. -/
theorem shadowQuotient_neg_eq_inv
    (F : ℂ → ℂ) (a z : ℂ)
    (hp : F (a + z) ≠ 0) (hm : F (a - z) ≠ 0) :
    shadowQuotient F a (-z) = (shadowQuotient F a z)⁻¹ := by
  unfold shadowQuotient
  have hplus : a - -z = a + z := by ring
  have hminus : a + -z = a - z := by ring
  rw [hplus, hminus]
  field_simp [hp, hm]


/-! ## Exact golden word in the Suzuki boundary pair -/

open GppWeilParity

/-- Projective ratio of the canonical Suzuki 0/π boundary pair. -/
def suzukiRatio (I : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiA I z / suzukiB I z

/-- Suzuki reflection swaps the two homogeneous boundary coordinates up to the same
minus sign, hence the projective ratio is inverted. -/
theorem suzukiRatio_neg_eq_inv
    (I : ℂ → ℂ) (z : ℂ)
    (hA : suzukiA I z ≠ 0) (hB : suzukiB I z ≠ 0) :
    suzukiRatio I (-z) = (suzukiRatio I z)⁻¹ := by
  unfold suzukiRatio
  rw [suzukiA_neg_eq_neg_suzukiB, suzukiB_neg_eq_neg_suzukiA]
  field_simp [hA, hB]

/-- The unit upper-triangular boundary-frame shear A↦A+B acts by q↦q+1. -/
def suzukiShearedRatio (I : ℂ → ℂ) (z : ℂ) : ℂ :=
  (suzukiA I z + suzukiB I z) / suzukiB I z

theorem suzukiShearedRatio_eq_add_one
    (I : ℂ → ℂ) (z : ℂ) (hB : suzukiB I z ≠ 0) :
    suzukiShearedRatio I z = suzukiRatio I z + 1 := by
  unfold suzukiShearedRatio suzukiRatio
  field_simp [hB]

/--
**Exact golden Möbius word in the canonical Suzuki boundary pair.**

Reflect z↦-z, which swaps A and B projectively, then apply the unit shear A↦A+B.
On q=A/B this is exactly q↦1+1/q.
-/
theorem suzuki_reflect_then_shear_golden
    (I : ℂ → ℂ) (z : ℂ)
    (hA : suzukiA I z ≠ 0) (hB : suzukiB I z ≠ 0) :
    suzukiShearedRatio I (-z) = 1 + (suzukiRatio I z)⁻¹ := by
  have hBneg : suzukiB I (-z) ≠ 0 := by
    rw [suzukiB_neg_eq_neg_suzukiA]
    exact neg_ne_zero.mpr hA
  rw [suzukiShearedRatio_eq_add_one I (-z) hBneg,
      suzukiRatio_neg_eq_inv I z hA hB]
  ring

/-- A fixed point of the reflected-and-sheared Suzuki boundary word obeys the golden
quadratic. This theorem is conditional: no arithmetic fixed-point claim is made. -/
theorem suzuki_golden_quadratic_of_fixed
    (I : ℂ → ℂ) (z : ℂ)
    (hA : suzukiA I z ≠ 0) (hB : suzukiB I z ≠ 0)
    (hfix : suzukiShearedRatio I (-z) = suzukiRatio I z) :
    (suzukiRatio I z) ^ 2 = suzukiRatio I z + 1 := by
  have hgold := suzuki_reflect_then_shear_golden I z hA hB
  have hq0 : suzukiRatio I z ≠ 0 := by
    unfold suzukiRatio
    exact div_ne_zero hA hB
  rw [hfix] at hgold
  have hmul := congrArg (fun w : ℂ => suzukiRatio I z * w) hgold
  calc
    (suzukiRatio I z) ^ 2
        = suzukiRatio I z * suzukiRatio I z := by ring
    _ = suzukiRatio I z * (1 + (suzukiRatio I z)⁻¹) := hmul
    _ = suzukiRatio I z + 1 := by
      simp [mul_add, hq0]



/-! ## Projective conjugacy to the Sherman--Morrison response -/

/-- Complex version of the odd rank-one response update. -/
def oddSchurC (x : ℂ) : ℂ := 2 * x / (x + 2)

/-- Complex version of the projective swap x↦4/x. -/
def poleDualC (x : ℂ) : ℂ := 4 / x

/-- Affine response coordinate corresponding to a projective ratio q=A/B. -/
def responseFromRatio (q : ℂ) : ℂ := 2 / q

/-- Unit shear q↦q+1 becomes the odd Sherman--Morrison update in x=2/q. -/
theorem responseFromRatio_add_one
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    responseFromRatio (q + 1) = oddSchurC (responseFromRatio q) := by
  have hq1' : 1 + q ≠ 0 := by
    simpa [add_comm] using hq1
  unfold responseFromRatio oddSchurC
  field_simp [hq0, hq1, hq1']
  ring

/-- Projective swap q↦q⁻¹ becomes x↦4/x in x=2/q. -/
theorem responseFromRatio_inv
    {q : ℂ} (hq0 : q ≠ 0) :
    responseFromRatio q⁻¹ = poleDualC (responseFromRatio q) := by
  unfold responseFromRatio poleDualC
  field_simp [hq0]
  ring

/-- Suzuki reflection therefore induces the pole-duality map on the normalized response
coordinate x=2/(A/B). -/
theorem suzuki_response_reflection_eq_poleDual
    (I : ℂ → ℂ) (z : ℂ)
    (hA : suzukiA I z ≠ 0) (hB : suzukiB I z ≠ 0) :
    responseFromRatio (suzukiRatio I (-z))
      = poleDualC (responseFromRatio (suzukiRatio I z)) := by
  rw [suzukiRatio_neg_eq_inv I z hA hB]
  apply responseFromRatio_inv
  unfold suzukiRatio
  exact div_ne_zero hA hB

/-- The unit Suzuki boundary shear induces the odd Sherman--Morrison response update. -/
theorem suzuki_response_shear_eq_oddSchur
    (I : ℂ → ℂ) (z : ℂ)
    (hA : suzukiA I z ≠ 0) (hB : suzukiB I z ≠ 0)
    (hAB : suzukiA I z + suzukiB I z ≠ 0) :
    responseFromRatio (suzukiShearedRatio I z)
      = oddSchurC (responseFromRatio (suzukiRatio I z)) := by
  have hq0 : suzukiRatio I z ≠ 0 := by
    unfold suzukiRatio
    exact div_ne_zero hA hB
  have hq1 : suzukiRatio I z + 1 ≠ 0 := by
    unfold suzukiRatio
    intro h
    have hmul := congrArg (fun w : ℂ => w * suzukiB I z) h
    field_simp [hB] at hmul
    exact hAB (by simpa using hmul)
  rw [suzukiShearedRatio_eq_add_one I z hB]
  exact responseFromRatio_add_one hq0 hq1


/-! ## The natural Schur/Herglotz coordinate kills the naive golden closure -/

/-- Cayley/Herglotz impedance associated with a Schur variable q. -/
def impedance (q : ℂ) : ℂ := (1 + q) / (1 - q)

/-- Reciprocal shadow q↦q⁻¹ becomes a sign flip of the impedance.  Thus reciprocal
shadow and additive rank-one feedback do not act as the golden map in the same natural
linearized coordinate. -/
theorem impedance_inv_eq_neg
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    impedance q⁻¹ = -impedance q := by
  unfold impedance
  have hqi1 : q⁻¹ ≠ 1 := by
    intro h
    have hmul := congrArg (fun w : ℂ => w * q) h
    have honeq : (1 : ℂ) = q := by
      simpa [hq0] using hmul
    exact hq1 honeq.symm
  field_simp [hq0, hq1, hqi1]
  ring

/-- If the rank-one update is unit translation in the impedance coordinate, then
shadow followed by that update is the affine reflection m↦1-m, not golden dynamics. -/
theorem translated_shadow_impedance
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    impedance q⁻¹ + 1 = 1 - impedance q := by
  rw [impedance_inv_eq_neg hq0 hq1]
  ring

/-- The resulting affine reflection is an involution. -/
theorem affineReflection_involution (m : ℂ) :
    1 - (1 - m) = m := by
  ring


/-! ## Cayley background factor inside the Suzuki boundary ratio -/

/-- The elementary pole/Cayley factor carried by the explicit (z-i)/(z+i) prefactor. -/
def poleCayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- The pole Cayley factor is literally the RH Cayley coordinate beta(s) after the
centered spectral change of variable s=(z+i)/(2i). -/
theorem poleCayley_eq_criticalCayley
    {z : ℂ} (hzi : z + Complex.I ≠ 0) :
    poleCayley z =
      criticalCayley ((z + Complex.I) / (2 * Complex.I)) := by
  have hi : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  unfold poleCayley criticalCayley
  field_simp [hzi, hi]
  ring

/-- The canonical Suzuki ratio factors into the elementary critical Cayley background
times one arithmetic reflection ratio I(z)/I(-z). -/
theorem suzukiRatio_factorization
    (I : ℂ → ℂ) {z : ℂ}
    (hzi : z + Complex.I ≠ 0) (hIm : I (-z) ≠ 0) :
    suzukiRatio I z =
      poleCayley z * (I z / I (-z)) := by
  unfold suzukiRatio suzukiA suzukiB poleCayley
  field_simp [hzi, hIm]
  ring

/-- The elementary pole/Cayley background itself reciprocates under z -> -z. -/
theorem poleCayley_neg_eq_inv
    {z : ℂ} (hp : z + Complex.I ≠ 0) (hm : z - Complex.I ≠ 0) :
    poleCayley (-z) = (poleCayley z)⁻¹ := by
  unfold poleCayley
  field_simp [hp, hm]
  ring

/-! ## Golden extremality among positive reciprocal-shear maps -/

/-- A positive shear of size a followed by reciprocal duality. -/
def weightedGoldenMap (a x : ℝ) : ℝ := a + 1 / x

/-- The interval [phi,infinity) is invariant under every reciprocal-shear map with
shear a >= 1. -/
theorem weightedGoldenMap_ge_golden
    {a x : ℝ} (ha : 1 ≤ a) (hx : goldenRatio ≤ x) :
    goldenRatio ≤ weightedGoldenMap a x := by
  have hphi0 : 0 < goldenRatio := goldenRatio_pos
  have hx0 : 0 < x := lt_of_lt_of_le hphi0 hx
  have hinv_nonneg : 0 ≤ 1 / x := by positivity
  have hphi_le_two : goldenRatio ≤ 2 := by
    have hs : Real.sqrt 5 ≤ 3 := by
      have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hs2 : (Real.sqrt 5)^2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith
    unfold goldenRatio
    linarith
  unfold weightedGoldenMap
  calc
    goldenRatio ≤ 2 := hphi_le_two
    _ ≤ a + 1 / x := by linarith

/-- On the invariant positive region, the absolute derivative factor 1/x^2 is bounded
by the golden constant phi^{-2}. This is the weakest contraction in the unit-shear case. -/
theorem reciprocal_derivative_factor_le_golden
    {x : ℝ} (hx : goldenRatio ≤ x) :
    1 / (x ^ 2) ≤ 1 / (goldenRatio ^ 2) := by
  have hphi0 : 0 < goldenRatio := goldenRatio_pos
  have hx0 : 0 < x := lt_of_lt_of_le hphi0 hx
  have hsquares : goldenRatio ^ 2 ≤ x ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (sq_pos_of_pos hphi0) hsquares

/-- Exact derivative of a reciprocal-shear map. -/
theorem hasDerivAt_weightedGoldenMap
    (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (weightedGoldenMap a) (-(1 / x ^ 2)) x := by
  unfold weightedGoldenMap
  convert (hasDerivAt_const x a).add (hasDerivAt_inv (hasDerivAt_id x) hx) using 1 <;> ring

/-- Therefore every positive reciprocal-shear step with a >= 1 is locally no less
contractive than the golden step once the orbit lies in [phi,infinity). -/
theorem weightedGoldenMap_deriv_norm_bound
    (a : ℝ) {x : ℝ} (hx : goldenRatio ≤ x) :
    |-(1 / x ^ 2)| ≤ 1 / (goldenRatio ^ 2) := by
  have hphi0 : 0 < goldenRatio := goldenRatio_pos
  have hx0 : 0 < x := lt_of_lt_of_le hphi0 hx
  rw [abs_of_nonpos]
  · simpa using reciprocal_derivative_factor_le_golden hx
  · have : 0 ≤ 1 / x ^ 2 := by positivity
    linarith


end

end GppGoldenMobius
