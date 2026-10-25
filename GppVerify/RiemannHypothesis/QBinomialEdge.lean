import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The q-binomial annihilator and its pole cancellation

Source: Codex, `work/codex/2026-10-23_wave234_full_s1_annihilator_pnt_residual_q_binomial.md`
(GPP-bridge; Discovery2 PR #12), New theorem 1 and the `B_K = 0` step of New theorem 2.
Daniel Toupin / Golden Physics Project, with AI assistance from Codex (statement) and Claude Code
(formalization).

Let `r_m = r₀ q^m`. Codex's annihilator polynomial is `P(z) = ∏_{m<M} (z − r_m)`.

* `gauss`: the Gaussian binomial `[M, j]_q`, defined by the q-Pascal rule
  `[M+1, j+1] = [M, j+1] + q^{M−j} [M, j]`.
* `gauss_mul_prod`: the closed form, with denominators cleared:
  `[M, j]_q · ∏_{l<j} (1 − q^{l+1}) = ∏_{l<j} (1 − q^{M−l})`.
* `prod_expand`: the homogeneous finite q-binomial theorem
  `∏_{m<M} (z − r₀ q^m w) = Σ_{j≤M} (−r₀)^j q^{j(j−1)/2} [M, j]_q z^{M−j} w^j`.
* `prod_eq_sum_vK`: hence `P(z) = Σ_j v_j z^j` with `v_{M−j} = (−r₀)^j q^{j(j−1)/2} [M, j]_q`
  (Codex's New theorem 1).
* `laplace_train`: for a bump `b` and the train `V = Σ_j v_j b(· − a₀ − jδ)`,
  `∫ e^{σu} V(u) du = e^{σa₀} (∫ e^{σu} b) · Σ_j v_j (e^{σδ})^j`.
* `laplace_train_annihilated`: if `Σ_j v_j z^j = ∏_{m<M} (z − r₀ q^m)` with `M ≥ 1` and
  `r₀ = e^{σδ}`, the Laplace moment at `σ` vanishes. With `σ = −1/2` and `δ = 7/10` this is
  Codex's `B_K = 0`.

**Scope.** The `K → ∞` edge limit `w_j = (−r₀)^j q^{j(j−1)/2}/(q;q)_j` is not formalized. Neither
is the sewing convolution `C_V = V_K ∗ V_K` and its Laplace square `A_K²` (the single-bump midpoint
step is `GppSine2Convolution`), nor any PNT comparison of `ε_K`. Nothing here bears on the location
of the zeros, and no claim is made about RH.
-/

open Finset

namespace GppQBinomialEdge

section Algebra

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial `[M, j]_q` via the q-Pascal rule. -/
def gauss (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | M + 1, j + 1 => gauss q M (j + 1) + q ^ (M - j) * gauss q M j

@[simp] lemma gauss_zero_right (q : R) (M : ℕ) : gauss q M 0 = 1 := by cases M <;> rfl

@[simp] lemma gauss_zero_succ (q : R) (j : ℕ) : gauss q 0 (j + 1) = 0 := rfl

lemma gauss_succ_succ (q : R) (M j : ℕ) :
    gauss q (M + 1) (j + 1) = gauss q M (j + 1) + q ^ (M - j) * gauss q M j := rfl

lemma gauss_eq_zero_of_lt (q : R) {M j : ℕ} (h : M < j) : gauss q M j = 0 := by
  induction M generalizing j with
  | zero => obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0); rfl
  | succ M ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [gauss_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

/-- Closed form of the Gaussian binomial, denominators cleared. -/
theorem gauss_mul_prod (q : R) (M j : ℕ) :
    gauss q M j * ∏ l ∈ range j, (1 - q ^ (l + 1)) = ∏ l ∈ range j, (1 - q ^ (M - l)) := by
  induction M generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ j =>
      rw [gauss_zero_succ, zero_mul, eq_comm]
      exact prod_eq_zero (i := 0) (by simp) (by simp)
  | succ M ih =>
    cases j with
    | zero => simp
    | succ j =>
      have e1 := ih (j + 1)
      have e2 := ih j
      rw [prod_range_succ, prod_range_succ] at e1
      rw [gauss_succ_succ, prod_range_succ, prod_range_succ']
      have hshift : ∏ l ∈ range j, (1 - q ^ (M + 1 - (l + 1))) = ∏ l ∈ range j, (1 - q ^ (M - l)) :=
        prod_congr rfl fun l _ => by rw [Nat.add_sub_add_right]
      rw [hshift, Nat.sub_zero]
      set N := ∏ l ∈ range j, (1 - q ^ (M - l))
      rcases le_or_gt j M with hj | hj
      · have hp : q ^ (M - j) * q ^ (j + 1) = q ^ (M + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination e1 + q ^ (M - j) * (1 - q ^ (j + 1)) * e2 - N * hp
      · have h0 : N = 0 := prod_eq_zero (i := M) (mem_range.mpr hj) (by simp)
        linear_combination e1 + q ^ (M - j) * (1 - q ^ (j + 1)) * e2 +
          (q ^ (M + 1) - q ^ (M - j) * q ^ (j + 1)) * h0

/-- The coefficient `(−r₀)^j q^{j(j−1)/2} [M, j]_q`. -/
def coef (r₀ q : R) (M j : ℕ) : R := (-r₀) ^ j * q ^ j.choose 2 * gauss q M j

lemma coef_succ_succ (r₀ q : R) {M j : ℕ} (hj : j ≤ M) :
    coef r₀ q (M + 1) (j + 1) = coef r₀ q M (j + 1) + (-r₀ * q ^ M) * coef r₀ q M j := by
  unfold coef
  rw [gauss_succ_succ, Nat.choose_succ_succ', Nat.choose_one_right]
  have hp : q ^ (j + j.choose 2) * q ^ (M - j) = q ^ M * q ^ j.choose 2 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  linear_combination (-r₀) ^ (j + 1) * gauss q M j * hp

lemma coef_eq_zero_of_lt (r₀ q : R) {M j : ℕ} (h : M < j) : coef r₀ q M j = 0 := by
  rw [coef, gauss_eq_zero_of_lt q h, mul_zero]

/-- **Homogeneous finite q-binomial theorem.** -/
theorem prod_expand (r₀ q z w : R) (M : ℕ) :
    ∏ m ∈ range M, (z - r₀ * q ^ m * w) =
      ∑ j ∈ range (M + 1), coef r₀ q M j * z ^ (M - j) * w ^ j := by
  induction M with
  | zero => simp [coef]
  | succ M ih =>
    rw [prod_range_succ, ih]
    set S := ∑ j ∈ range (M + 1), coef r₀ q M j * z ^ (M - j) * w ^ j
    have hR : ∑ j ∈ range (M + 1 + 1), coef r₀ q (M + 1) j * z ^ (M + 1 - j) * w ^ j =
        ∑ j ∈ range (M + 1), coef r₀ q M (j + 1) * z ^ (M - j) * w ^ (j + 1) +
          ∑ j ∈ range (M + 1), (-r₀ * q ^ M) * (coef r₀ q M j * z ^ (M - j) * w ^ j) * w +
          z ^ (M + 1) := by
      rw [sum_range_succ', ← sum_add_distrib]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [coef_succ_succ r₀ q (Nat.lt_succ_iff.mp (mem_range.mp hj)), Nat.add_sub_add_right]
        ring
      · simp [coef]
    have hL : S * z = ∑ j ∈ range (M + 1), coef r₀ q M (j + 1) * z ^ (M - j) * w ^ (j + 1) +
        z ^ (M + 1) := by
      rw [sum_mul, sum_range_succ', sum_range_succ (fun j => coef r₀ q M (j + 1) * _ * _) M,
        coef_eq_zero_of_lt r₀ q (Nat.lt_succ_self M)]
      have h0 : coef r₀ q M 0 * z ^ (M - 0) * w ^ 0 * z = z ^ (M + 1) := by
        simp [coef, pow_succ]
      rw [h0, zero_mul, zero_mul, add_zero]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      have : M - j = M - (j + 1) + 1 := by have := mem_range.mp hj; omega
      rw [this, pow_succ]; ring
    have h3 : ∑ j ∈ range (M + 1), (-r₀ * q ^ M) * (coef r₀ q M j * z ^ (M - j) * w ^ j) * w =
        (-r₀ * q ^ M * w) * S := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [hR]
    linear_combination hL - h3

/-- **Codex's New theorem 1.** `∏_{m<M} (z − r₀ q^m) = Σ_{j≤M} v_j z^j` with
`v_j = (−r₀)^{M−j} q^{(M−j)(M−j−1)/2} [M, M−j]_q`, i.e. `v_{M−j} = (−r₀)^j q^{j(j−1)/2} [M, j]_q`. -/
theorem prod_eq_sum_vK (r₀ q z : R) (M : ℕ) :
    ∏ m ∈ range M, (z - r₀ * q ^ m) = ∑ j ∈ range (M + 1), coef r₀ q M (M - j) * z ^ j := by
  have h := prod_expand r₀ q z 1 M
  simp only [mul_one, one_pow] at h
  rw [h, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [show M + 1 - 1 - j = M - j by omega, show M - (M - j) = j by omega]

end Algebra

section Laplace

open MeasureTheory Real

/-- Laplace moment of a translated bump train. -/
theorem laplace_train (b : ℝ → ℝ) (σ a₀ δ : ℝ) (v : ℕ → ℝ) (N : ℕ)
    (hb : Integrable (fun u => exp (σ * u) * b u)) :
    ∫ u, exp (σ * u) * ∑ j ∈ range N, v j * b (u - (a₀ + j * δ)) =
      exp (σ * a₀) * (∫ u, exp (σ * u) * b u) * ∑ j ∈ range N, v j * exp (σ * δ) ^ j := by
  have key : ∀ (c w : ℝ), (fun u => exp (σ * u) * (w * b (u - c))) =
      fun u => (w * exp (σ * c)) * (exp (σ * (u - c)) * b (u - c)) := by
    intro c w; ext u
    rw [show σ * u = σ * c + σ * (u - c) by ring, exp_add]; ring
  simp_rw [mul_sum]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun j _ => ?_
    rw [key, integral_const_mul,
      integral_sub_right_eq_self (fun u => exp (σ * u) * b u) (a₀ + j * δ),
      mul_add, exp_add, show σ * (j * δ) = j * (σ * δ) by ring, exp_nat_mul]
    ring
  · intro j _
    rw [key]
    exact (hb.comp_sub_right _).const_mul _

/-- **Pole cancellation.** If the train's coefficients are those of `∏_{m<M} (z − r₀ q^m)` with
`M ≥ 1` and `r₀ = e^{σδ}`, the Laplace moment at `σ` vanishes. -/
theorem laplace_train_annihilated (b : ℝ → ℝ) (σ a₀ δ r₀ q : ℝ) (v : ℕ → ℝ) (N M : ℕ)
    (hb : Integrable (fun u => exp (σ * u) * b u)) (hM : 1 ≤ M)
    (hv : ∀ z : ℝ, ∑ j ∈ range N, v j * z ^ j = ∏ m ∈ range M, (z - r₀ * q ^ m))
    (hr : r₀ = exp (σ * δ)) :
    ∫ u, exp (σ * u) * ∑ j ∈ range N, v j * b (u - (a₀ + j * δ)) = 0 := by
  rw [laplace_train b σ a₀ δ v N hb, hv, prod_eq_zero (i := 0) (mem_range.mpr hM) (by simp [hr]),
    mul_zero]

/-- **Codex's `B_K = 0`.** For Codex's lattice `δ = 7/10`, `r₀ = e^{−7/20}` and any ratio `q`,
the q-binomial train has vanishing `e^{−u/2}` moment. -/
theorem codex_B_K_eq_zero (b : ℝ → ℝ) (a₀ q : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hb : Integrable (fun u => exp (-(1 / 2) * u) * b u)) :
    ∫ u, exp (-(1 / 2) * u) * ∑ j ∈ range (M + 1),
      coef (exp (-(7 / 20))) q M (M - j) * b (u - (a₀ + j * (7 / 10))) = 0 :=
  laplace_train_annihilated b _ a₀ _ _ q _ _ M hb hM
    (fun z => (prod_eq_sum_vK _ q z M).symm) (by norm_num)

end Laplace

end GppQBinomialEdge
