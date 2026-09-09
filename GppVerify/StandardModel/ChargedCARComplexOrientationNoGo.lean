import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import GppVerify.StandardModel.ChargedKahlerRelativeOrientation

/-!
# Charged CAR complex orientations: simultaneous reversal is anti-linear, not an internal unitary deck flip

The standard positive-energy quantization of a charged fermionic dynamics starts with a
complex phase space `Y`.  Let `I` denote its original scalar complex structure.  For a
nondegenerate self-adjoint dynamical generator `b`, set

    q = sgn b,
    J = I q,
    h = |b|.

Then `I^2=J^2=-1`, `[I,J]=0`, and

    q = - I J.

This is exactly the relative-orientation algebra sought by the project.  However, it also
forces an important correction to the earlier four-lift toy model.  Because `I` is the
ACTUAL scalar multiplication by `i`, every complex-linear operator commutes with `I`.
Therefore no nonzero complex-linear operator can reverse that complex orientation:

    D I = - I D  ==>  D = 0.

So `(I,J)->(-I,-J)` cannot be an ordinary nontrivial unitary/internal gauge operation on the
same complex Hilbert space.  The natural map relating the two presentations is anti-linear
complex conjugation.  In the finite two-sector standard form below, componentwise conjugation
anticommutes with both `I` and `J`, commutes with the relative charge grading `q`, and
preserves the norm.

This substantially sharpens the physical dictionary:

* the relative product `q=-IJ` is standard charged-field structure;
* simultaneous reversal of the two ABSOLUTE complex orientations is naturally a conjugate
  presentation / antiunitary relation, not automatically a second coherent state component;
* a literal `(|++>+|-->)/sqrt 2` physical doubling would therefore require additional
  degrees of freedom beyond standard charged CAR quantization.
-/

namespace GppChargedCARComplexOrientationNoGo

open scoped ComplexConjugate
open GppChargedKahlerRelativeOrientation

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2 := Fin 2 → ℂ

/-- Original charge-phase complex structure: ordinary scalar multiplication by `i`. -/
def phaseI : M2 := !![Complex.I,0;0,Complex.I]

/-- Relative particle/antiparticle sign. -/
def qSign : M2 := !![(1:ℂ),0;0,-1]

/-- Positive-energy one-particle complex structure `J = I q`. -/
def energyJ : M2 := phaseI * qSign

 theorem phaseI_sq : phaseI * phaseI = -(1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.I_mul_I]

 theorem qSign_sq : qSign * qSign = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qSign, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

 theorem phaseI_qSign_commute : phaseI * qSign = qSign * phaseI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseI, qSign, Matrix.mul_apply, Fin.sum_univ_two]

 theorem energyJ_explicit : energyJ = !![Complex.I,0;0,-Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [energyJ, phaseI, qSign, Matrix.mul_apply, Fin.sum_univ_two]

 theorem energyJ_sq : energyJ * energyJ = -(1 : M2) := by
  rw [energyJ_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.I_mul_I]

/-- The observable particle/antiparticle grading is exactly the relative complex orientation. -/
theorem qSign_eq_relative_orientation : qSign = -(phaseI * energyJ) := by
  rw [energyJ]
  calc
    qSign = (1 : M2) * qSign := by simp
    _ = -((-(1 : M2)) * qSign) := by simp
    _ = -((phaseI * phaseI) * qSign) := by rw [phaseI_sq]
    _ = -(phaseI * (phaseI * qSign)) := by simp [Matrix.mul_assoc]

/-- Reversing both formal complex orientations leaves the relative charge grading fixed. -/
theorem reverse_both_preserves_q :
    -((-phaseI) * (-energyJ)) = qSign := by
  rw [← qSign_eq_relative_orientation]
  simp

/-- Scalar `i` is central for every complex-linear matrix. -/
theorem every_complex_matrix_commutes_phaseI (D : M2) :
    D * phaseI = phaseI * D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseI, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- MAIN NO-GO: a complex-linear matrix that anticommutes with the actual scalar complex
    structure must vanish.  Therefore there is no nonzero internal/unitary deck operator
    implementing `I -> -I` on the same complex carrier. -/
theorem complex_linear_orientation_reversal_forces_zero
    (D : M2) (hrev : D * phaseI = -(phaseI * D)) :
    D = 0 := by
  have hcomm := every_complex_matrix_commutes_phaseI D
  rw [hcomm] at hrev
  ext i j
  have hij := congrArg (fun M : M2 => M i j) hrev
  fin_cases i <;> fin_cases j <;>
    simp [phaseI, Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢ <;>
    apply Complex.ext <;> norm_num at hij ⊢ <;> linarith

/-- Componentwise conjugation is the natural anti-linear relation between opposite complex
    presentations. -/
def conjV (v : V2) : V2 := ![conj (v 0), conj (v 1)]

 theorem conjV_involutive (v : V2) : conjV (conjV v) = v := by
  ext i
  fin_cases i <;> simp [conjV]

/-- Conjugation reverses the original scalar complex orientation. -/
theorem conjV_reverses_phaseI (v : V2) :
    conjV (phaseI *ᵥ v) = (-phaseI) *ᵥ conjV v := by
  ext i
  fin_cases i <;>
    simp [conjV, phaseI, Matrix.mulVec, Fin.sum_univ_two]

/-- It simultaneously reverses the positive-energy complex structure `J`. -/
theorem conjV_reverses_energyJ (v : V2) :
    conjV (energyJ *ᵥ v) = (-energyJ) *ᵥ conjV v := by
  rw [energyJ_explicit]
  ext i
  fin_cases i <;>
    simp [conjV, Matrix.mulVec, Fin.sum_univ_two]

/-- But the relative particle/antiparticle grading is unchanged. -/
theorem conjV_preserves_qSign (v : V2) :
    conjV (qSign *ᵥ v) = qSign *ᵥ conjV v := by
  ext i
  fin_cases i <;>
    simp [conjV, qSign, Matrix.mulVec, Fin.sum_univ_two]

/-- Euclidean one-particle norm on the two sectors. -/
def normSq2 (v : V2) : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1)

 theorem conjV_preserves_normSq2 (v : V2) : normSq2 (conjV v) = normSq2 v := by
  simp [normSq2, conjV]

/-- Capstone: standard charged-CAR orientation reversal has an anti-linear implementer that
    reverses both complex structures, preserves their relative charge product and preserves
    probability norm, while a nonzero complex-linear implementer is impossible. -/
theorem standard_orientation_reversal_package (v : V2) :
    conjV (phaseI *ᵥ v) = (-phaseI) *ᵥ conjV v ∧
    conjV (energyJ *ᵥ v) = (-energyJ) *ᵥ conjV v ∧
    conjV (qSign *ᵥ v) = qSign *ᵥ conjV v ∧
    normSq2 (conjV v) = normSq2 v := by
  exact ⟨conjV_reverses_phaseI v, conjV_reverses_energyJ v,
    conjV_preserves_qSign v, conjV_preserves_normSq2 v⟩

end GppChargedCARComplexOrientationNoGo
