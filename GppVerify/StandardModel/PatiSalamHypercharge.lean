import Mathlib.Tactic

/-!
# Pati-Salam singlet/doublet and hypercharge reconstruction

Finite arithmetic core accompanying Daniel Toupin,
"Which Way Is Forward?", v18.

With X = 3(B-L), define T3R = Y - X/6.
For one Standard-Model generation plus N_R this reconstructs the right-handed
SU(2)_R doublet weights exactly. The same normalization gives
Y = T3R + X/6, and an X=6, T3R=-1 order parameter is hypercharge-neutral.

This file formalizes only rational charge arithmetic. It does not construct
SU(2)_R as a gauge group or prove the dynamical symmetry breaking.
-/

namespace GppPatiSalamHypercharge

/-- Hypercharge from twice-right-isospin r = 2*T3R and X=3(B-L). -/
def hypercharge (X r : ℤ) : ℚ :=
  (r : ℚ) / 2 + (X : ℚ) / 6

/-- Twice-right-isospin reconstructed from Y and X. -/
def twiceT3R (Y : ℚ) (X : ℤ) : ℚ :=
  2 * (Y - (X : ℚ) / 6)

/-- Left quark doublet has T3R = 0 and Y = 1/6. -/
theorem qL_hypercharge :
    hypercharge 1 0 = (1 : ℚ) / 6 := by
  norm_num [hypercharge]

/-- Left lepton doublet has T3R = 0 and Y = -1/2. -/
theorem lL_hypercharge :
    hypercharge (-3) 0 = -(1 : ℚ) / 2 := by
  norm_num [hypercharge]

/-- Right up quark is the +1/2 member of an SU(2)_R doublet. -/
theorem uR_hypercharge :
    hypercharge 1 1 = (2 : ℚ) / 3 := by
  norm_num [hypercharge]

/-- Right down quark is the -1/2 member of an SU(2)_R doublet. -/
theorem dR_hypercharge :
    hypercharge 1 (-1) = -(1 : ℚ) / 3 := by
  norm_num [hypercharge]

/-- Right neutrino is the +1/2 member of the right lepton doublet. -/
theorem nR_hypercharge :
    hypercharge (-3) 1 = 0 := by
  norm_num [hypercharge]

/-- Right electron is the -1/2 member of the right lepton doublet. -/
theorem eR_hypercharge :
    hypercharge (-3) (-1) = -1 := by
  norm_num [hypercharge]

/-- Reconstructing twice T3R from the observed left-quark hypercharge gives zero. -/
theorem qL_reconstructs_singlet :
    twiceT3R ((1 : ℚ) / 6) 1 = 0 := by
  norm_num [twiceT3R]

/-- Reconstructing twice T3R from the observed left-lepton hypercharge gives zero. -/
theorem lL_reconstructs_singlet :
    twiceT3R (-(1 : ℚ) / 2) (-3) = 0 := by
  norm_num [twiceT3R]

/-- The observed right-quark hypercharges reconstruct opposite SU(2)_R weights. -/
theorem right_quark_doublet_weights :
    twiceT3R ((2 : ℚ) / 3) 1 = 1 ∧
    twiceT3R (-(1 : ℚ) / 3) 1 = -1 := by
  constructor <;> norm_num [twiceT3R]

/-- The observed right-lepton hypercharges reconstruct opposite SU(2)_R weights. -/
theorem right_lepton_doublet_weights :
    twiceT3R 0 (-3) = 1 ∧
    twiceT3R (-1) (-3) = -1 := by
  constructor <;> norm_num [twiceT3R]

/-- A right-handed triplet component with X=6 and T3R=-1 is hypercharge neutral. -/
theorem deltaR_neutral_component :
    hypercharge 6 (-2) = 0 := by
  norm_num [hypercharge]

/-- The two columns of an X=0 bidoublet have Standard-Model Higgs hypercharges ±1/2. -/
theorem higgs_bidoublet_columns :
    hypercharge 0 1 = (1 : ℚ) / 2 ∧
    hypercharge 0 (-1) = -(1 : ℚ) / 2 := by
  constructor <;> norm_num [hypercharge]

/-- Up-type Yukawa hypercharge is neutral: -Y_Q + Y_Htilde + Y_u = 0. -/
theorem up_yukawa_hypercharge_zero :
    -((1 : ℚ) / 6) + (-(1 : ℚ) / 2) + (2 : ℚ) / 3 = 0 := by
  norm_num

/-- Down-type Yukawa hypercharge is neutral. -/
theorem down_yukawa_hypercharge_zero :
    -((1 : ℚ) / 6) + (1 : ℚ) / 2 - (1 : ℚ) / 3 = 0 := by
  norm_num

/-- Charged-lepton Yukawa hypercharge is neutral. -/
theorem electron_yukawa_hypercharge_zero :
    -(-(1 : ℚ) / 2) + (1 : ℚ) / 2 - 1 = 0 := by
  norm_num

/-- Dirac-neutrino Yukawa hypercharge is neutral. -/
theorem neutrino_yukawa_hypercharge_zero :
    -(-(1 : ℚ) / 2) - (1 : ℚ) / 2 + 0 = 0 := by
  norm_num

end GppPatiSalamHypercharge
