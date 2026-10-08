import GppVerify.RiemannHypothesis.CasimirCriticalLine
import GppVerify.ThreadWeilParity.CrossResolvent
import Mathlib.Tactic

/-!
# Hermitian observer-Casimir survival forces the principal series

This file isolates the finite spectral core of the proposed observer-even
Casimir route.

Let

  c(s) = s(1-s).

If a nonreal arithmetic label `s` survives faithfully as an eigencharacter of
a Hermitian observer operator with eigenvalue `c(s)`, then `c(s)` must be
real. Since

  Im c(s) = Im(s) * (1 - 2 Re(s)),

a nonreal label is forced to `Re(s)=1/2`.

This theorem is deliberately finite-dimensional. It proves the algebraic
spectral implication without pretending to construct the zero-independent
infinite-dimensional arithmetic operator whose spectrum contains every zeta
zero. That construction remains the global Hilbert--Polya/observer-survival
target.
-/

namespace GppObserverCasimirSpectralSurvival

open Complex
open scoped ComplexOrder

/-- A nonzero complex vector has nonzero Hermitian norm-square. -/
lemma star_dot_self_ne_zero {n : Type*} [Fintype n]
    (v : n → ℂ) (hv : v ≠ 0) :
    dotProduct (star v) v ≠ 0 := by
  intro h
  apply hv
  have hflat : ∑ j, star (v j) * v j = 0 := by
    simpa only [dotProduct, Pi.star_apply] using h
  have hsum : ∑ j, Complex.normSq (v j) = 0 := by
    have hre := congrArg Complex.re hflat
    rw [Complex.re_sum] at hre
    simp only [Complex.star_def] at hre
    simpa only [Complex.zero_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, neg_mul, sub_neg_eq_add] using hre
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (v j))).mp hsum i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using hi

/-- Every eigenvalue carried by a nonzero eigenvector of a Hermitian complex
matrix is fixed by complex conjugation. -/
theorem hermitian_eigenvalue_star_fixed
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (mu : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (heig : M.mulVec v = mu • v) :
    star mu = mu := by
  have hvv : dotProduct (star v) v ≠ 0 := star_dot_self_ne_zero v hv
  have h1 : dotProduct (star v) (M.mulVec v) =
      mu * dotProduct (star v) v := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  have h2 : dotProduct (star v) (M.mulVec v) =
      star mu * dotProduct (star v) v := by
    simpa only using
      GppThreadWeilParity.hermitian_dotProduct_mulVec M hM mu v v heig
  have heq : mu * dotProduct (star v) v =
      star mu * dotProduct (star v) v := h1.symm.trans h2
  exact mul_right_cancel₀ hvv heq.symm

/-- A nonreal arithmetic label whose Casimir survives as a Hermitian eigenvalue
lies on the critical line. -/
theorem critical_of_hermitian_casimir_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (s : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (heig : M.mulVec v = GppCasimirCriticalLine.casimir s • v)
    (him : s.im ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  have hstar :
      star (GppCasimirCriticalLine.casimir s) =
        GppCasimirCriticalLine.casimir s :=
    hermitian_eigenvalue_star_fixed M hM _ v hv heig
  have hc : (GppCasimirCriticalLine.casimir s).im = 0 := by
    have hi := congrArg Complex.im hstar
    simp at hi
    linarith
  exact GppCasimirCriticalLine.real_casimir_forces_half s him hc

/-- The same hypothesis automatically puts the Casimir in the principal-series
real range once the critical line has been forced. -/
theorem hermitian_casimir_eigenvector_forces_principal_range
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (s : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (heig : M.mulVec v = GppCasimirCriticalLine.casimir s • v)
    (him : s.im ≠ 0) :
    (GppCasimirCriticalLine.casimir s).im = 0 ∧
      (1 : ℝ) / 4 ≤ (GppCasimirCriticalLine.casimir s).re := by
  have hs :=
    critical_of_hermitian_casimir_eigenvector M hM s v hv heig him
  exact (GppCasimirCriticalLine.casimir_ge_quarter_iff s).2 hs

end GppObserverCasimirSpectralSurvival

#print axioms GppObserverCasimirSpectralSurvival.hermitian_eigenvalue_star_fixed
#print axioms GppObserverCasimirSpectralSurvival.critical_of_hermitian_casimir_eigenvector
#print axioms GppObserverCasimirSpectralSurvival.hermitian_casimir_eigenvector_forces_principal_range
