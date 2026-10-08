import GppVerify.RiemannHypothesis.PrimeOccupationBridge
import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import GppVerify.RiemannHypothesis.RankOneThresholdControls
import GppVerify.RiemannHypothesis.PrimeContractionUnitarity
import GppVerify.RiemannHypothesis.BostConnesKmsAlgebra
import Mathlib.Tactic

/-!
# Selected-prime radial compensation and the one-channel/two-channel obstruction

This module records the exact local algebra suggested by comparing the GPP
fixed-window programme with the selected-prime compensation mechanism in the
2026-09-30 OpenAI quasi-RH paper.

The point is deliberately local and finite.

For the geometric occupation response

  n(z) = z/(1-z),

subtracting a radially rescaled copy gives

  n(z) - n(qz)
    = (1-q) z / ((1-z)(1-qz)).

At the Euler-whitening level the distinction between the true rank-one zeta
channel and the shifted-product control becomes sharper.

A degree-one whitening polynomial is

  W_r(u) = 1-r u.

Under the same radial rescaling r -> q r,

  W_{qr}(u) - W_r(u) = (1-q) r u.

The scalar term cancels and only ONE frequency/channel remains.

For a degree-two complementary pair

  W_{r+,r-}(u) = (1-r+ u)(1-r- u),

the identical operation gives

  W_{qr+,qr-}(u)-W_{r+,r-}(u)
    = (1-q)(r+ + r-)u
      - (1-q^2)r+r- u^2.

Thus the same compensation necessarily leaves a quadratic/two-step residual
whenever 0<q<1 and both radii are nonzero.  This is an exact algebraic
discriminator between a single Euler channel and the shifted-product control;
coefficient positivity by itself does not provide the discriminator.

The module also combines this with the already-proved TFD midpoint uniqueness:
for p>1 and theta != 0, the complementary radii

  p^(-1/2) p^theta,   p^(-1/2) p^(-theta)

are distinct, so no nonzero two-mode coefficient vector can satisfy both TFD
annihilation equations simultaneously.

Finally we instantiate the existing jump-energy identity on a two-box vector
f - T_t f.  This isolates the exact positive collision term before any global
prime summation or Archimedean/pole renormalization.

Scope: exact local algebra and Hilbert-space identities only.  No global
fixed-window estimate and no RH claim.
-/

namespace GppSelectedPrimeCompensation

open Complex
open GppPrimeOccupation
open GppRankOneControls

/-! ## Occupation-level marked-minus-rescaled identity -/

/-- A geometric occupation response minus a radially rescaled copy. -/
noncomputable def compensatedOccupation (q z : ℂ) : ℂ :=
  occupation z - occupation (q * z)

/-- Exact selected-prime compensation identity for the geometric occupation
response. -/
theorem compensatedOccupation_eq
    {q z : ℂ} (hz : 1 - z ≠ 0) (hqz : 1 - q * z ≠ 0) :
    compensatedOccupation q z =
      (1 - q) * z / ((1 - z) * (1 - q * z)) := by
  unfold compensatedOccupation occupation
  rw [div_sub_div _ _ hz hqz]
  congr 1
  ring

/-! ## Whitening-polynomial compensation -/

/-- The true rank-one local whitening polynomial. -/
def singleWhitening (r u : ℝ) : ℝ := 1 - r * u

/-- A generic degree-two complementary whitening polynomial. -/
def doubleWhitening (rPlus rMinus u : ℝ) : ℝ :=
  (1 - rPlus * u) * (1 - rMinus * u)

/-- Radial compensation of a degree-one Euler channel kills the scalar term
and leaves exactly one linear channel. -/
theorem single_radial_compensation (q r u : ℝ) :
    singleWhitening (q * r) u - singleWhitening r u =
      (1 - q) * r * u := by
  unfold singleWhitening
  ring

/-- Radial compensation of a degree-two complementary channel necessarily
contains a quadratic residual. -/
theorem double_radial_compensation (q rPlus rMinus u : ℝ) :
    doubleWhitening (q * rPlus) (q * rMinus) u -
        doubleWhitening rPlus rMinus u =
      (1 - q) * (rPlus + rMinus) * u -
        (1 - q ^ 2) * rPlus * rMinus * u ^ 2 := by
  unfold doubleWhitening
  ring

/-- Coefficient of the unavoidable quadratic channel after radial
compensation of a two-radius whitening polynomial. -/
def quadraticResidualCoeff (q rPlus rMinus : ℝ) : ℝ :=
  -(1 - q ^ 2) * rPlus * rMinus

/-- For a genuine contraction 0<q<1 and two nonzero radii, the quadratic
residual coefficient cannot vanish. -/
theorem quadraticResidualCoeff_ne_zero
    {q rPlus rMinus : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrPlus : rPlus ≠ 0) (hrMinus : rMinus ≠ 0) :
    quadraticResidualCoeff q rPlus rMinus ≠ 0 := by
  have hq : 1 - q ^ 2 ≠ 0 := by
    have : q ^ 2 < 1 := by nlinarith
    linarith
  unfold quadraticResidualCoeff
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hq) hrPlus) hrMinus

/-! ## The actual shifted-product radii -/

/-- Critical TFD radius at one prime. -/
noncomputable def criticalRadius (p : ℝ) : ℝ :=
  p ^ (-(1 / 2 : ℝ))

/-- Positive complementary multiplier p^theta. -/
noncomputable def complementaryMultiplier (p theta : ℝ) : ℝ :=
  p ^ theta

/-- The two shifted-product radii r p^(+theta), r p^(-theta). -/
noncomputable def shiftedRadiusPlus (p theta : ℝ) : ℝ :=
  criticalRadius p * complementaryMultiplier p theta

noncomputable def shiftedRadiusMinus (p theta : ℝ) : ℝ :=
  criticalRadius p * (complementaryMultiplier p theta)⁻¹

/-- A positive number different from one is different from its reciprocal. -/
lemma mul_radius_inv_ne
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≠ 1) :
    r * a ≠ r * a⁻¹ := by
  intro h
  have haeq : a = a⁻¹ := by
    apply mul_left_cancel₀ hr.ne'
    exact h
  have hsq0 := congrArg (fun x : ℝ => x * a) haeq
  have hsq : a * a = 1 := by
    simpa [inv_mul_cancel₀ ha.ne'] using hsq0
  have haeq1 : a = 1 := by
    nlinarith [sq_nonneg (a - 1)]
  exact ha1 haeq1

/-- For p>1 and theta != 0, the two complementary shifted-product radii
are genuinely distinct. -/
theorem shifted_radii_ne
    {p theta : ℝ} (hp : 1 < p) (htheta : theta ≠ 0) :
    shiftedRadiusPlus p theta ≠ shiftedRadiusMinus p theta := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : 0 < criticalRadius p := by
    unfold criticalRadius
    exact Real.rpow_pos_of_pos hp0 _
  have ha : 0 < complementaryMultiplier p theta := by
    unfold complementaryMultiplier
    exact Real.rpow_pos_of_pos hp0 _
  have ha1 : complementaryMultiplier p theta ≠ 1 := by
    intro h
    apply htheta
    exact (GppPrimeContraction.rpow_eq_one_iff_of_one_lt hp theta).mp h
  exact mul_radius_inv_ne hr ha ha1

/-- The prime radial scaling q=1/p is a strict contraction for p>1. -/
theorem prime_radial_scale_bounds {p : ℝ} (hp : 1 < p) :
    0 < p⁻¹ ∧ p⁻¹ < 1 := by
  constructor
  · exact inv_pos.mpr (lt_trans zero_lt_one hp)
  · exact inv_lt_one_of_one_lt₀ hp

/-- Consequently, radial compensation of the shifted-product local factor
has a nonzero quadratic residual at every p>1. -/
theorem shifted_product_quadratic_residual_ne_zero
    {p theta : ℝ} (hp : 1 < p) :
    quadraticResidualCoeff p⁻¹
      (shiftedRadiusPlus p theta) (shiftedRadiusMinus p theta) ≠ 0 := by
  obtain ⟨hq0, hq1⟩ := prime_radial_scale_bounds hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : 0 < criticalRadius p := by
    unfold criticalRadius
    exact Real.rpow_pos_of_pos hp0 _
  have ha : 0 < complementaryMultiplier p theta := by
    unfold complementaryMultiplier
    exact Real.rpow_pos_of_pos hp0 _
  apply quadraticResidualCoeff_ne_zero hq0 hq1
  · unfold shiftedRadiusPlus
    exact mul_ne_zero hr.ne' ha.ne'
  · unfold shiftedRadiusMinus
    exact mul_ne_zero hr.ne' (inv_ne_zero ha.ne')

/-! ## TFD single-radius obstruction -/

/-- The complementary shifted-product pair cannot be represented by one
nonzero pure two-mode TFD vector when theta != 0: satisfying both midpoint
annihilation equations forces the vector to vanish. -/
theorem shifted_two_radius_tfd_no_nonzero
    (psi : ℕ × ℕ → ℝ) {p theta : ℝ}
    (hp : 1 < p) (htheta : theta ≠ 0)
    (hPlus :
      aL psi - shiftedRadiusPlus p theta • aRdag psi = 0)
    (hMinus :
      aL psi - shiftedRadiusMinus p theta • aRdag psi = 0) :
    psi = 0 := by
  exact unique_radius psi
    (shiftedRadiusPlus p theta) (shiftedRadiusMinus p theta)
    (shifted_radii_ne hp htheta) hPlus hMinus

/-! ## Two-box collision form before global scalarization -/

/-- Instantiation of the exact jump-energy identity on a two-box vector
a_t = f - T_t f.  This is the positive collision term that should be kept
intact before combining it with pole/Archimedean diagonal counterterms. -/
theorem twoBox_jump_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*}
    (S : Finset ι) (c : ι → ℝ)
    (T : ι → E → E) (Tt : E → E) (f : E)
    (hT : ∀ i, ‖T i (f - Tt f)‖ = ‖f - Tt f‖) :
    ∑ i ∈ S, c i * ‖(f - Tt f) - T i (f - Tt f)‖ ^ 2 =
      2 * ∑ i ∈ S, c i *
        (‖f - Tt f‖ ^ 2 -
          (inner ℂ (f - Tt f) (T i (f - Tt f))).re) := by
  exact GppBostConnesKms.jump_energy S c T (f - Tt f) hT

/-- If the compensated local weights are nonnegative, the finite two-box
collision sum is manifestly nonnegative before any diagonal subtraction. -/
theorem twoBox_collision_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*}
    (S : Finset ι) (c : ι → ℝ)
    (T : ι → E → E) (Tt : E → E) (f : E)
    (hc : ∀ i ∈ S, 0 ≤ c i) :
    0 ≤ ∑ i ∈ S, c i * ‖(f - Tt f) - T i (f - Tt f)‖ ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hc i hi) (sq_nonneg _)


/-! ## Quantitative prime-power moment discriminator

For local log-derivative moments b₁=Σᵢrᵢ and b₂=Σᵢrᵢ²,
the nonlinear prime defect b₁²-b₂ is zero for one channel and
equals 2r₊r₋ for two channels. In the complementary shifted-product
control r₊r₋=1/p, so the defect equals exactly 2/p.

Unlike the whitening-polynomial u² coefficient, this is a directly
normalized relation between the first TWO logarithmic prime-power
coefficients. A second invariant b₁b₃-b₂² detects unequal radii;
it vanishes at theta=0 even for the degree-two control.
The compensated identity below clears denominators, so no
division by potentially vanishing factors is smuggled into the proof.

These are local algebraic identities, not RH or a global Weil inequality.
-/

/-- The degree-one logarithmic prime-power channel has zero nonlinear defect. -/
theorem single_log_moment_defect (r : ℝ) :
    (r ^ 1) ^ 2 - r ^ 2 = 0 := by
  ring

/-- Quantitative two-channel defect in the first two prime-power moments. -/
theorem double_log_moment_defect (rPlus rMinus : ℝ) :
    (rPlus + rMinus) ^ 2 - (rPlus ^ 2 + rMinus ^ 2) =
      2 * rPlus * rMinus := by
  ring

/-- In complementary half-density radii the defect is exactly 2/p,
assuming the exact local product normalization r₊r₋=1/p. -/
theorem double_log_moment_defect_prime
    {p rPlus rMinus : ℝ} (hprod : rPlus * rMinus = p⁻¹) :
    (rPlus + rMinus) ^ 2 - (rPlus ^ 2 + rMinus ^ 2) =
      2 * p⁻¹ := by
  rw [double_log_moment_defect]
  calc
    2 * rPlus * rMinus = 2 * (rPlus * rMinus) := by ring
    _ = 2 * p⁻¹ := by rw [hprod]

/-- A finite positive prime-scale product makes the local defect strictly positive. -/
theorem double_log_moment_defect_prime_pos
    {p rPlus rMinus : ℝ} (hp : 0 < p)
    (hprod : rPlus * rMinus = p⁻¹) :
    0 < (rPlus + rMinus) ^ 2 - (rPlus ^ 2 + rMinus ^ 2) := by
  rw [double_log_moment_defect_prime hprod]
  positivity

/-- After radial compensation, the same defect survives with an
exact multiplicative scaling. This is the denominator-free identity
whose normalized quotient recovers 2 r₊r₋ when 0<q<1. -/
theorem double_compensated_log_moment_defect
    (q rPlus rMinus : ℝ) :
    ((1 - q) * (rPlus + rMinus)) ^ 2 * (1 - q ^ 2) -
        ((1 - q ^ 2) * (rPlus ^ 2 + rMinus ^ 2)) * (1 - q) ^ 2 =
      (2 * rPlus * rMinus) * (1 - q) ^ 2 * (1 - q ^ 2) := by
  ring

/-- The next Hankel minor measures unequal radii, separately from the
degree defect: it is r₊r₋(r₊-r₋)². -/
theorem double_log_third_moment_minor (rPlus rMinus : ℝ) :
    (rPlus + rMinus) * (rPlus ^ 3 + rMinus ^ 3) -
      (rPlus ^ 2 + rMinus ^ 2) ^ 2 =
        rPlus * rMinus * (rPlus - rMinus) ^ 2 := by
  ring

/-- With positive complementary radii and unequal shifts the Hankel
minor is strictly positive. For equal radii, this minor is zero. -/
theorem double_log_third_moment_minor_pos
    {rPlus rMinus : ℝ} (hplus : 0 < rPlus) (hminus : 0 < rMinus)
    (hne : rPlus ≠ rMinus) :
    0 < (rPlus + rMinus) * (rPlus ^ 3 + rMinus ^ 3) -
      (rPlus ^ 2 + rMinus ^ 2) ^ 2 := by
  rw [double_log_third_moment_minor]
  have hs : 0 < (rPlus - rMinus) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  positivity


end GppSelectedPrimeCompensation

#print axioms GppSelectedPrimeCompensation.compensatedOccupation_eq
#print axioms GppSelectedPrimeCompensation.single_radial_compensation
#print axioms GppSelectedPrimeCompensation.double_radial_compensation
#print axioms GppSelectedPrimeCompensation.quadraticResidualCoeff_ne_zero
#print axioms GppSelectedPrimeCompensation.shifted_radii_ne
#print axioms GppSelectedPrimeCompensation.shifted_product_quadratic_residual_ne_zero
#print axioms GppSelectedPrimeCompensation.shifted_two_radius_tfd_no_nonzero
#print axioms GppSelectedPrimeCompensation.twoBox_jump_energy
#print axioms GppSelectedPrimeCompensation.twoBox_collision_nonneg
