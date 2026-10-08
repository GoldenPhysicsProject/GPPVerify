import Mathlib.Tactic
import GppVerify.StandardModel.PatiSalamHypercharge
import GppVerify.StandardModel.PrimePatiSalamCartan

/-!
# Prime-carrier Pati-Salam spectrum: exact finite counts and charges

Assuming the candidate carrier dimensions selected by the prime incidence are

  V4 : dim 4
  VL : dim 2
  VR : dim 2,

the standard Pati-Salam representation arithmetic gives one Spin(10) chiral
family, the Spin(10) vector/Higgs sector, the adjoint, and the familiar E6/E8
dimension ladder.

This file proves only finite dimension and rational-charge identities.  It does
not prove the physical prime-to-gauge dictionary or exceptional-group branching.
-/

namespace GppPrimePatiSalamSpectrum

open GppPatiSalamHypercharge

/-- One chiral Pati-Salam family has 16 complex Weyl slots. -/
theorem chiral_family_dimension :
    (4 : ℕ) * 2 + 4 * 2 = 16 := by
  norm_num

/-- The Spin(10) vector decomposition 10 = Λ²4 + (2⊗2). -/
theorem vector_ten_dimension :
    Nat.choose 4 2 + 2 * 2 = 10 := by
  norm_num [Nat.choose]

/-- The Pati-Salam adjoint and mixed generators fill the Spin(10) adjoint. -/
theorem spin10_adjoint_dimension :
    (15 : ℕ) + 3 + 3 + 6 * 2 * 2 = 45 := by
  norm_num

/-- The mixed unification sector has dimension 24. -/
theorem mixed_sector_dimension :
    (6 : ℕ) * 2 * 2 = 24 := by
  norm_num

/-- Standard E6 fundamental dimension ladder. -/
theorem e6_fundamental_dimension :
    (16 : ℕ) + 10 + 1 = 27 := by
  norm_num

/-- Standard E6 adjoint dimension ladder. -/
theorem e6_adjoint_dimension :
    (45 : ℕ) + 16 + 16 + 1 = 78 := by
  norm_num

/-- Standard E8 -> E6 x SU(3) adjoint dimension ladder. -/
theorem e8_e6_su3_dimension :
    (78 : ℕ) + 8 + 27 * 3 + 27 * 3 = 248 := by
  norm_num

/-- Electric charge from twice-left-isospin l, twice-right-isospin r,
and X = 3(B-L). -/
def electricCharge (X l r : ℤ) : ℚ :=
  (l : ℚ) / 2 + (r : ℚ) / 2 + (X : ℚ) / 6

/-- Left-handed lepton doublet charges: neutrino 0, charged lepton -1. -/
theorem left_lepton_charges :
    electricCharge (-3) 1 0 = 0 ∧
    electricCharge (-3) (-1) 0 = -1 := by
  constructor <;> norm_num [electricCharge]

/-- Left-handed quark doublet charges: up 2/3, down -1/3. -/
theorem left_quark_charges :
    electricCharge 1 1 0 = (2 : ℚ) / 3 ∧
    electricCharge 1 (-1) 0 = -(1 : ℚ) / 3 := by
  constructor <;> norm_num [electricCharge]

/-- Right-handed lepton doublet charges in the physical-particle convention. -/
theorem right_lepton_charges :
    electricCharge (-3) 0 1 = 0 ∧
    electricCharge (-3) 0 (-1) = -1 := by
  constructor <;> norm_num [electricCharge]

/-- Right-handed quark doublet charges in the physical-particle convention. -/
theorem right_quark_charges :
    electricCharge 1 0 1 = (2 : ℚ) / 3 ∧
    electricCharge 1 0 (-1) = -(1 : ℚ) / 3 := by
  constructor <;> norm_num [electricCharge]

/-- Neutrino neutrality is an exact cancellation of weak isospin and B-L. -/
theorem neutrino_charge_cancellation :
    (1 : ℚ) / 2 + (-3 : ℚ) / 6 = 0 := by
  norm_num

/-- The one-generation mixed SU(2)^2-U(1)_Y anomaly coefficient vanishes:
three quark doublets with Y=1/6 cancel one lepton doublet with Y=-1/2. -/
theorem su2_sq_hypercharge_anomaly_zero :
    3 * ((1 : ℚ) / 6) + (-(1 : ℚ) / 2) = 0 := by
  norm_num

/-- In left-handed Weyl convention, the mixed SU(3)^2-U(1)_Y anomaly vanishes. -/
theorem su3_sq_hypercharge_anomaly_zero :
    2 * ((1 : ℚ) / 6) + (-(2 : ℚ) / 3) + (1 : ℚ) / 3 = 0 := by
  norm_num

/-- The gravitational-U(1)_Y anomaly vanishes for one generation including ν_R. -/
theorem gravitational_hypercharge_anomaly_zero :
    6 * ((1 : ℚ) / 6) +
    3 * (-(2 : ℚ) / 3) +
    3 * ((1 : ℚ) / 3) +
    2 * (-(1 : ℚ) / 2) +
    1 + 0 = 0 := by
  norm_num

/-- The cubic U(1)_Y anomaly vanishes for one generation including ν_R. -/
theorem cubic_hypercharge_anomaly_zero :
    6 * ((1 : ℚ) / 6) ^ 3 +
    3 * (-(2 : ℚ) / 3) ^ 3 +
    3 * ((1 : ℚ) / 3) ^ 3 +
    2 * (-(1 : ℚ) / 2) ^ 3 +
    1 ^ 3 + 0 ^ 3 = 0 := by
  norm_num

/-- Pati-Salam SU(4)^3 anomaly bookkeeping: two 4s and two 4bars cancel. -/
theorem su4_cubic_family_count :
    (2 : ℤ) - 2 = 0 := by
  norm_num

/-- Each SU(2) factor sees four Weyl doublets, an even number; this is the
finite parity count relevant to the Witten anomaly check. -/
theorem su2_doublet_count_even :
    (4 : ℕ) % 2 = 0 := by
  norm_num

end GppPrimePatiSalamSpectrum

#print axioms GppPrimePatiSalamSpectrum.chiral_family_dimension
#print axioms GppPrimePatiSalamSpectrum.left_lepton_charges
#print axioms GppPrimePatiSalamSpectrum.cubic_hypercharge_anomaly_zero
