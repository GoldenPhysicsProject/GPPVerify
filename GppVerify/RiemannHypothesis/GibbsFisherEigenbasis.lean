import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Finite Gibbs/Fisher algebra in the energy eigenbasis

Source: Codex, GPP-bridge PR #11 handoff of 2026-10-30 22:31Z (Priority 2: finite Gibbs/Fisher
algebra). Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and
Claude Code (formalization).

Work in the eigenbasis of a finite Hamiltonian `H = diag(E)`, with Gibbs weights
`p_i = e^{−β E_i} / Z`, `ρ_β = diag(p)`, and a Hermitian observable `A = (a_{ij})`. Put
`X = i[A, ρ_β]`, so `X_{ij} = i a_{ij} (p_j − p_i)`.

* `trace_double_commutator`: `Tr(ρ_β [A,[H,A]]) = Σ_{ij} p_i · 2 (E_j − E_i) |a_{ij}|²`, proved as a
  matrix-trace identity for `H`, `ρ_β` diagonal and `A` Hermitian.
* `fisher_form_eq`: with the divided difference `dlog p_i p_j = (log p_i − log p_j)/(p_i − p_j)`
  (and `1/p_i` when `p_i = p_j`, where `|X_{ij}| = 0` anyway),
  `Σ_{ij} |X_{ij}|² · dlog p_i p_j = β · Tr(ρ_β [A,[H,A]])`.
* `ground_double_commutator`: for the ground state `Ω = e_0` the diagonal entry
  `Σ_j 2 (E_j − E_0) |a_{0j}|²` equals `2 ⟨A_c Ω, (H − E_0) A_c Ω⟩` with
  `A_c Ω = AΩ − ⟨Ω, AΩ⟩ Ω`.

**Scope.** Finite-dimensional eigenbasis algebra only. This is the algebraic sum identity, **not**
the analytic statement that the Hessian of the relative entropy along `e^{isA} ρ_β e^{−isA}` is
`Q`; that derivative (matrix logarithm, second derivative in `s`) is not formalized. Zero-temperature
convergence and any infinite-dimensional or uniform-in-volume extension are not claimed. No claim
about RH or Yang–Mills.
-/

set_option autoImplicit false

open Finset Matrix Complex

namespace GppGibbsFisher

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Partition function `Z = Σ e^{−β E_j}`. -/
noncomputable def Z (β : ℝ) (E : ι → ℝ) : ℝ := ∑ j, Real.exp (-β * E j)

/-- Gibbs weights `p_i = e^{−β E_i} / Z`. -/
noncomputable def gibbs (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ := Real.exp (-β * E i) / Z β E

omit [DecidableEq ι] in
lemma Z_pos [Nonempty ι] (β : ℝ) (E : ι → ℝ) : 0 < Z β E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [DecidableEq ι] in
lemma gibbs_pos [Nonempty ι] (β : ℝ) (E : ι → ℝ) (i : ι) : 0 < gibbs β E i :=
  div_pos (Real.exp_pos _) (Z_pos β E)

omit [DecidableEq ι] in
/-- `log p_i − log p_j = −β (E_i − E_j)`. -/
lemma log_gibbs_sub [Nonempty ι] (β : ℝ) (E : ι → ℝ) (i j : ι) :
    Real.log (gibbs β E i) - Real.log (gibbs β E j) = -β * (E i - E j) := by
  unfold gibbs
  rw [Real.log_div (Real.exp_pos _).ne' (Z_pos β E).ne',
    Real.log_div (Real.exp_pos _).ne' (Z_pos β E).ne', Real.log_exp, Real.log_exp]
  ring

/-- Divided difference of `log`, with the continuous value `1/x` on the diagonal. -/
noncomputable def dlog (x y : ℝ) : ℝ :=
  if x = y then 1 / x else (Real.log x - Real.log y) / (x - y)

/-- Diagonal Hamiltonian, Gibbs state. -/
noncomputable def Hmat (E : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun i => (E i : ℂ)
noncomputable def rhoMat (β : ℝ) (E : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => (gibbs β E i : ℂ)

/-- `[A, B] = AB − BA`. -/
def comm (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * B - B * A

/-- `Tr(ρ_β [A,[H,A]])` in the eigenbasis. -/
theorem trace_double_commutator (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ)
    (hA : ∀ i j, A j i = (starRingEnd ℂ) (A i j)) :
    Matrix.trace (rhoMat β E * comm A (comm (Hmat E) A)) =
      (((∑ i, gibbs β E i * ∑ j, 2 * (E j - E i) * ‖A i j‖ ^ 2 : ℝ)) : ℂ) := by
  have hHA : ∀ i j, comm (Hmat E) A i j = ((E i : ℂ) - E j) * A i j := by
    intro i j
    simp [comm, Hmat, Matrix.sub_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  have hdiag : ∀ i, (rhoMat β E * comm A (comm (Hmat E) A)) i i =
      (gibbs β E i : ℂ) * (comm A (comm (Hmat E) A)) i i := by
    intro i
    simp [rhoMat, Matrix.diagonal_mul]
  obtain ⟨C, hC⟩ : ∃ C, C = comm (Hmat E) A := ⟨_, rfl⟩
  have hC' : ∀ i j, C i j = ((E i : ℂ) - E j) * A i j := fun i j => by rw [hC]; exact hHA i j
  have hinner : ∀ i, (comm A (comm (Hmat E) A)) i i =
      ∑ j, (2 * ((E j : ℂ) - E i) * (((‖A i j‖ ^ 2 : ℝ)) : ℂ)) := by
    intro i
    rw [← hC]
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : A i j * (starRingEnd ℂ) (A i j) = (((‖A i j‖ ^ 2 : ℝ)) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    rw [hC' j i, hC' i j, hA i j]
    linear_combination (2 * ((E j : ℂ) - E i)) * this
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag, hinner]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]

/-- `X = i[A, ρ_β]`. -/
noncomputable def Xmat (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Complex.I • comm A (rhoMat β E)

lemma Xmat_apply (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ) (i j : ι) :
    Xmat β E A i j = Complex.I * A i j * ((gibbs β E j : ℂ) - gibbs β E i) := by
  simp [Xmat, comm, rhoMat, Matrix.mul_apply, Matrix.diagonal_apply]
  ring

/-- Termwise: `|X_ij|² · dlog p_i p_j = β |a_ij|² (E_j − E_i)(p_i − p_j)`. -/
lemma fisher_term [Nonempty ι] (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ) (i j : ι) :
    ‖Xmat β E A i j‖ ^ 2 * dlog (gibbs β E i) (gibbs β E j) =
      β * ‖A i j‖ ^ 2 * ((E j - E i) * (gibbs β E i - gibbs β E j)) := by
  have hX : ‖Xmat β E A i j‖ ^ 2 = ‖A i j‖ ^ 2 * (gibbs β E i - gibbs β E j) ^ 2 := by
    rw [Xmat_apply, norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow]
    congr 1
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hX]
  by_cases h : gibbs β E i = gibbs β E j
  · simp [dlog, h]
  · have hne : gibbs β E i - gibbs β E j ≠ 0 := sub_ne_zero.mpr h
    simp only [dlog, if_neg h]
    rw [log_gibbs_sub]
    field_simp
    ring

/-- **Finite Fisher identity.** `Σ_ij |X_ij|² dlog p_i p_j = β · Tr(ρ_β [A,[H,A]])`, with the
trace given by `trace_double_commutator`. -/
theorem fisher_form_eq [Nonempty ι] (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ)
    (hA : ∀ i j, A j i = (starRingEnd ℂ) (A i j)) :
    ∑ i, ∑ j, ‖Xmat β E A i j‖ ^ 2 * dlog (gibbs β E i) (gibbs β E j) =
      β * ∑ i, gibbs β E i * ∑ j, 2 * (E j - E i) * ‖A i j‖ ^ 2 := by
  simp only [fisher_term]
  have hsym : ∀ i j, ‖A j i‖ = ‖A i j‖ := fun i j => by rw [hA i j, Complex.norm_conj]
  set c : ι → ι → ℝ := fun i j => ‖A i j‖ ^ 2 with hc
  have h1 : ∑ i, ∑ j, β * ‖A i j‖ ^ 2 * ((E j - E i) * (gibbs β E i - gibbs β E j)) =
      β * (∑ i, ∑ j, c i j * ((E j - E i) * gibbs β E i) -
        ∑ i, ∑ j, c i j * ((E j - E i) * gibbs β E j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [hc]; ring
  have h2 : ∑ i, ∑ j, c i j * ((E j - E i) * gibbs β E j) =
      -∑ i, ∑ j, c i j * ((E j - E i) * gibbs β E i) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hc, hsym j i]; ring
  have h3 : ∑ i, gibbs β E i * ∑ j, 2 * (E j - E i) * ‖A i j‖ ^ 2 =
      2 * ∑ i, ∑ j, c i j * ((E j - E i) * gibbs β E i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hc]; ring
  rw [h1, h2, h3]
  ring

/-- The ground-state diagonal entry: `Σ_j 2 (E_j − E_0)|a_0j|² = 2 ⟨A_c Ω, (H − E_0) A_c Ω⟩`
for `Ω = e_0` and `A_c Ω = AΩ − ⟨Ω, AΩ⟩ Ω` (entries `A_{j0}` for `j ≠ 0`, and `0` at `j = 0`). -/
theorem ground_double_commutator (E : ι → ℝ) (A : Matrix ι ι ℂ)
    (hA : ∀ i j, A j i = (starRingEnd ℂ) (A i j)) (i0 : ι) :
    ∑ j, 2 * (E j - E i0) * ‖A i0 j‖ ^ 2 =
      2 * ∑ j, (E j - E i0) *
        ‖A j i0 - (if j = i0 then A i0 i0 else 0)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : j = i0
  · subst h; simp
  · simp only [if_neg h, sub_zero]
    rw [hA i0 j, Complex.norm_conj]
    ring

end GppGibbsFisher
