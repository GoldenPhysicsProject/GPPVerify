import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Helicity under parity and time reversal

For a massless state the helicity numerator is `J · p`.  Under time reversal
both angular momentum and momentum reverse, so helicity is preserved.  Under
parity momentum reverses while angular momentum, being axial, does not; hence
helicity reverses.  This elementary distinction is the discrete-symmetry
constraint needed when comparing the celestial shadow map `J ↦ -J` with bulk
P/T/CPT operations.
-/

namespace GppDiscreteSymmetryHelicity

/-- Algebraic helicity numerator.  The normalization by `|p|` is irrelevant for
its transformation sign and is deliberately factored out. -/
def helicityNumerator {n : ℕ} (J p : Fin n → ℝ) : ℝ :=
  ∑ i, J i * p i

/-- Time reversal reverses both angular momentum and momentum, preserving the
helicity numerator. -/
theorem time_reversal_preserves_helicity_numerator {n : ℕ} (J p : Fin n → ℝ) :
    helicityNumerator (fun i => -J i) (fun i => -p i) = helicityNumerator J p := by
  unfold helicityNumerator
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Parity reverses momentum but leaves axial angular momentum unchanged, hence
it reverses the helicity numerator. -/
theorem parity_reverses_helicity_numerator {n : ℕ} (J p : Fin n → ℝ) :
    helicityNumerator J (fun i => -p i) = -helicityNumerator J p := by
  unfold helicityNumerator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A PT action reverses angular momentum while returning momentum to its
original sign; it therefore reverses helicity. -/
theorem pt_reverses_helicity_numerator {n : ℕ} (J p : Fin n → ℝ) :
    helicityNumerator (fun i => -J i) p = -helicityNumerator J p := by
  unfold helicityNumerator
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For a nonzero helicity value, a sign-reversing operation and a
helicity-preserving operation cannot agree.  This is the abstract no-go behind
the statement that the celestial shadow helicity flip cannot be pure time
reversal on a nonzero-helicity massless state. -/
theorem nonzero_flip_ne_preserve {h : ℝ} (hh : h ≠ 0) : -h ≠ h := by
  intro heq
  apply hh
  linarith

/-- In particular the graviton helicity labels are genuinely exchanged. -/
theorem graviton_flip_nontrivial : (-2 : ℝ) ≠ 2 := by norm_num

end GppDiscreteSymmetryHelicity

#print axioms GppDiscreteSymmetryHelicity.time_reversal_preserves_helicity_numerator
#print axioms GppDiscreteSymmetryHelicity.parity_reverses_helicity_numerator
#print axioms GppDiscreteSymmetryHelicity.pt_reverses_helicity_numerator
#print axioms GppDiscreteSymmetryHelicity.nonzero_flip_ne_preserve
