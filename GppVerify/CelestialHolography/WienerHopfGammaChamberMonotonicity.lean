import GppVerify.CelestialHolography.WienerHopfGammaChamberHierarchy
import Mathlib.Tactic

/-!
# Exact adjacent-chamber monotonicity

The Gamma/Mehler--Fock chamber recurrence multiplies chamber `k` by the positive
real factor `rhoStepFactor k x`.  Combined with strict positivity of the real
spectral density in every chamber, the factor threshold becomes an exact
comparison theorem for adjacent chambers themselves.

No convolution assumption is used.
-/

namespace GppWienerHopfGammaChamberMonotonicity

open GppSpectralRho
open GppWienerHopfGammaChamberHierarchy

private theorem rhoGamma_succ_re (k : ℕ) (x : ℝ) :
    (rhoGamma (k + 1) x).re = rhoStepFactor k x * (rhoGamma k x).re := by
  rw [rhoGamma_succ_stepFactor]
  simp

/-- Chamber `k+1` has larger real spectral density exactly above its transition
scale `2 x^2 = k+1`. -/
theorem rhoGamma_re_lt_succ_iff (k : ℕ) (x : ℝ) :
    (rhoGamma k x).re < (rhoGamma (k + 1) x).re ↔
      ((k : ℝ) + 1) < 2 * x ^ 2 := by
  rw [rhoGamma_succ_re]
  have hpos : 0 < (rhoGamma k x).re := rhoGamma_re_pos k x
  constructor
  · intro h
    apply (rhoStepFactor_gt_one_iff k x).1
    nlinarith
  · intro h
    have hfac : 1 < rhoStepFactor k x := (rhoStepFactor_gt_one_iff k x).2 h
    nlinarith

/-- Chamber `k+1` has smaller real spectral density exactly below its transition
scale. -/
theorem rhoGamma_succ_re_lt_iff (k : ℕ) (x : ℝ) :
    (rhoGamma (k + 1) x).re < (rhoGamma k x).re ↔
      2 * x ^ 2 < ((k : ℝ) + 1) := by
  rw [rhoGamma_succ_re]
  have hpos : 0 < (rhoGamma k x).re := rhoGamma_re_pos k x
  constructor
  · intro h
    apply (rhoStepFactor_lt_one_iff k x).1
    nlinarith
  · intro h
    have hfac : rhoStepFactor k x < 1 := (rhoStepFactor_lt_one_iff k x).2 h
    nlinarith

/-- Adjacent Gamma chambers cross exactly at `2 x^2 = k+1`. -/
theorem rhoGamma_succ_re_eq_iff (k : ℕ) (x : ℝ) :
    (rhoGamma (k + 1) x).re = (rhoGamma k x).re ↔
      2 * x ^ 2 = ((k : ℝ) + 1) := by
  rw [rhoGamma_succ_re]
  have hpos : 0 < (rhoGamma k x).re := rhoGamma_re_pos k x
  constructor
  · intro h
    apply (rhoStepFactor_eq_one_iff k x).1
    nlinarith
  · intro h
    have hfac : rhoStepFactor k x = 1 := (rhoStepFactor_eq_one_iff k x).2 h
    rw [hfac]
    ring

/-- For a nonzero chamber index, chamber `k` is a strict local maximum of the
real Gamma spectral density exactly when the transition coordinate `2 x^2`
lies strictly between `k` and `k+1`. -/
theorem rhoGamma_re_strict_local_max_iff
    {k : ℕ} (hk : 0 < k) (x : ℝ) :
    ((rhoGamma (k - 1) x).re < (rhoGamma k x).re ∧
      (rhoGamma (k + 1) x).re < (rhoGamma k x).re) ↔
      ((k : ℝ) < 2 * x ^ 2 ∧ 2 * x ^ 2 < (k : ℝ) + 1) := by
  have hkm1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  constructor
  · rintro ⟨hleft, hright⟩
    have hleft' := (rhoGamma_re_lt_succ_iff (k - 1) x).1 (by simpa [hkm1] using hleft)
    have hright' := (rhoGamma_succ_re_lt_iff k x).1 hright
    constructor
    · norm_num at hleft' ⊢
      simpa [hkm1] using hleft'
    · exact hright'
  · rintro ⟨hleft, hright⟩
    constructor
    · have h := (rhoGamma_re_lt_succ_iff (k - 1) x).2 (by
        norm_num
        simpa [hkm1] using hleft)
      simpa [hkm1] using h
    · exact (rhoGamma_succ_re_lt_iff k x).2 hright

end GppWienerHopfGammaChamberMonotonicity

#print axioms GppWienerHopfGammaChamberMonotonicity.rhoGamma_re_lt_succ_iff
#print axioms GppWienerHopfGammaChamberMonotonicity.rhoGamma_succ_re_lt_iff
#print axioms GppWienerHopfGammaChamberMonotonicity.rhoGamma_succ_re_eq_iff
#print axioms GppWienerHopfGammaChamberMonotonicity.rhoGamma_re_strict_local_max_iff
