import Mathlib.Tactic

namespace GppTwistorWeightDuality

def twistorWeight (n : ℤ) : ℤ := n - 2
def dualTwistorWeight (n : ℤ) : ℤ := -n - 2
def fourierWeight (k : ℤ) : ℤ := -k - 4

theorem fourierWeight_involutive (k : ℤ) :
    fourierWeight (fourierWeight k) = k := by
  unfold fourierWeight
  omega

theorem fourierWeight_twistor_eq_dual (n : ℤ) :
    fourierWeight (twistorWeight n) = dualTwistorWeight n := by
  unfold fourierWeight twistorWeight dualTwistorWeight
  omega

theorem dualWeight_eq_oppositeHelicityWeight (n : ℤ) :
    dualTwistorWeight n = twistorWeight (-n) := by
  unfold dualTwistorWeight twistorWeight
  omega

theorem fourierWeight_is_helicityFlip (n : ℤ) :
    fourierWeight (twistorWeight n) = twistorWeight (-n) := by
  rw [fourierWeight_twistor_eq_dual, dualWeight_eq_oppositeHelicityWeight]

theorem fourierWeight_fixed_iff (k : ℤ) :
    fourierWeight k = k ↔ k = -2 := by
  unfold fourierWeight
  omega

theorem scalar_weight_fixed : fourierWeight (twistorWeight 0) = twistorWeight 0 := by
  norm_num [fourierWeight, twistorWeight]

theorem photon_weight_pair :
    twistorWeight 2 = 0 ∧ fourierWeight (twistorWeight 2) = -4 := by
  norm_num [twistorWeight, fourierWeight]

theorem graviton_weight_pair :
    twistorWeight 4 = 2 ∧ fourierWeight (twistorWeight 4) = -6 := by
  norm_num [twistorWeight, fourierWeight]

end GppTwistorWeightDuality
