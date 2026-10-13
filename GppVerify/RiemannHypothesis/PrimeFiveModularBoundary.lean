import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Prime 5 is the last integral local boost

Source: Codex, GPP-bridge PR #11 comment 6139796379 and
`work/codex/2026-10-13_prime5_integral_boost_modular_boundary.md`, answering Daniel Toupin's
question "is 5 the boundary?".

The local TFD angle has `q_p = 1/√p = tanh κ_p`. Its boost `λ_p = e^{2κ_p} = (√p+1)/(√p−1)` has
reciprocal-pair trace `λ_p + λ_p⁻¹ = 2 + 4/(p−1)` (`boost_trace`). Since `λ_p` is irrational, it
is an eigenvalue of a hyperbolic `SL₂(ℤ)` matrix exactly when this trace is an integer. That
happens **iff `p ∈ {2, 3, 5}`** (`trace_int_iff`, through `dvd_four_iff`), with traces `6, 4, 3`.
The companion matrix `[[t, −1], [1, 0]]` has determinant `1` and carries `λ_p` as an eigenvalue
(`companion_det`, `boost_quadratic`).

At `p = 5` the boost is `φ²`, the eigenvalue of the shortest modular geodesic
`A = [[2,1],[1,1]] = UV` (`A_eq_UV`). The Weyl element `S` inverts it: `S A = A⁻¹ S`, with
`S² = −1` (`S_conj`, `S_sq`). Reduced mod 5 (`A5`, `S5`):
* `(A + 1)² = 0`, so `A⁵ = −1` and `A` has order `10` (`A5_unipotent`, `A5_pow_five`,
  `A5_sq_ne_one`);
* `S A S⁻¹ = A⁹`, with `S² = A⁵`;
* the twenty products `Aⁱ Sʲ` (`i < 10`, `j < 2`) are distinct (`dic5_card`). Together with the
  relations above, this makes `⟨A, S⟩` the dicyclic group of order 20.

**Scope.** The integrality criterion *assumes* integral modular compatibility; it is not forced by
Haar measure or by any global positivity. That the quartic Dirichlet doublet is the same
representation is not proved. The `A₅ ⊂ PSL₂(𝔽₅)` embedding and the Tate/Maass–Selberg transfer are
not formalized. **No RH claim.**
-/

namespace GppPrimeFiveBoundary

open Matrix

/-- For a prime `p`, `p − 1 ∣ 4` iff `p ∈ {2, 3, 5}`. -/
theorem dvd_four_iff {p : ℕ} (hp : p.Prime) : (p - 1) ∣ 4 ↔ p = 2 ∨ p = 3 ∨ p = 5 := by
  constructor
  · intro h
    have hle : p - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) h
    have h2 := hp.two_le
    have h5 : p ≤ 5 := by omega
    interval_cases p <;> first | decide | (norm_num at h)
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- The local boost `λ_p = (√p+1)/(√p−1)`. -/
noncomputable def boost (p : ℕ) : ℝ := (Real.sqrt p + 1) / (Real.sqrt p - 1)

theorem sqrt_gt_one {p : ℕ} (hp : 1 < p) : 1 < Real.sqrt p := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp)

/-- **Reciprocal-pair trace**: `λ_p + λ_p⁻¹ = 2 + 4/(p−1)`. -/
theorem boost_trace {p : ℕ} (hp : 1 < p) :
    boost p + (boost p)⁻¹ = 2 + 4 / ((p : ℝ) - 1) := by
  have hs := sqrt_gt_one hp
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  unfold boost
  set r := Real.sqrt p with hr
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : r + 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) - 1 ≠ 0 := by rw [← hsq]; nlinarith
  rw [inv_div, ← hsq]
  have h3' : r ^ 2 - 1 ≠ 0 := by rwa [hsq]
  field_simp
  ring

/-- **The integrality criterion**: the trace is an integer iff `p ∈ {2, 3, 5}`. -/
theorem trace_int_iff {p : ℕ} (hp : p.Prime) :
    (∃ t : ℤ, (t : ℝ) = 2 + 4 / ((p : ℝ) - 1)) ↔ p = 2 ∨ p = 3 ∨ p = 5 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  constructor
  · rintro ⟨t, ht⟩
    have hR : ((t - 2) * ((p : ℤ) - 1) : ℤ) = (4 : ℤ) := by
      have : ((t : ℝ) - 2) * ((p : ℝ) - 1) = 4 := by
        rw [ht]
        field_simp
        ring
      exact_mod_cast this
    have hdvd : ((p - 1 : ℕ) : ℤ) ∣ ((4 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hp.one_lt.le]
      exact ⟨t - 2, by push_cast; linarith⟩
    exact (dvd_four_iff hp).mp (Int.natCast_dvd_natCast.mp hdvd)
  · rintro (rfl | rfl | rfl)
    · exact ⟨6, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨3, by norm_num⟩

/-- The companion matrix `[[t, −1], [1, 0]]` lies in `SL₂(ℤ)`. -/
theorem companion_det (t : ℤ) : (!![t, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp [det_fin_two]

/-- `λ_p` is a root of `x² − t x + 1` (`t` the trace): the eigenvalue of the companion matrix. -/
theorem boost_quadratic {p : ℕ} (hp : 1 < p) :
    boost p ^ 2 - (2 + 4 / ((p : ℝ) - 1)) * boost p + 1 = 0 := by
  have hb : boost p ≠ 0 := by
    have := sqrt_gt_one hp
    unfold boost
    exact div_ne_zero (by linarith) (by linarith)
  rw [← boost_trace hp]
  field_simp
  ring

/-- Cusp shears and the shortest modular geodesic. -/
def U : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
def V : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]
def A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]
def Ainv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, 2]
def S : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

theorem A_eq_UV : A = U * V := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, U, V, mul_apply, Fin.sum_univ_two]

theorem A_trace_det : A 0 0 + A 1 1 = 3 ∧ A.det = 1 := by
  refine ⟨by simp [A], by simp [A, det_fin_two]⟩

theorem A_mul_Ainv : A * Ainv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, Ainv, mul_apply, Fin.sum_univ_two]

/-- The Weyl element inverts the golden geodesic: `S A = A⁻¹ S`. -/
theorem S_conj : S * A = Ainv * S := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A, Ainv, S, mul_apply, Fin.sum_univ_two]

theorem S_sq : S * S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S, mul_apply, Fin.sum_univ_two]

/-- `A` and `S` reduced mod 5. -/
def A5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![2, 1; 1, 1]
def S5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, -1; 1, 0]

/-- **Characteristic-five degeneracy**: `(A + 1)² = 0` mod 5. -/
theorem A5_unipotent : (A5 + 1) ^ 2 = 0 := by decide

theorem A5_pow_five : A5 ^ 5 = -1 := by decide

theorem A5_sq_ne_one : A5 ^ 2 ≠ 1 := by decide

theorem S5_conj : S5 * A5 = A5 ^ 9 * S5 := by decide

theorem S5_sq : S5 ^ 2 = A5 ^ 5 := by decide

/-- **The twenty elements `Aⁱ Sʲ` are distinct** (dicyclic group `Dic₅` of order 20). -/
theorem dic5_card :
    ((Finset.univ : Finset (Fin 10 × Fin 2)).image
      (fun ij => A5 ^ (ij.1 : ℕ) * S5 ^ (ij.2 : ℕ))).card = 20 := by decide

end GppPrimeFiveBoundary
