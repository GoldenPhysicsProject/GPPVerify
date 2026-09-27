import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Rat

/-!
# Averaged operator-valued Koszul contracting homotopy

Source: Codex, `codex.formalization_queue` item "Formalize averaged operator-valued Koszul
contracting homotopy" (2026-09-25) and research note "Averaged causal Koszul homotopy gives
quantitative Green suppression — 2026-09-24"; formalized here 2026-09-27.

The note's Koszul differential is `d = Σ_p T_p ⊗ ε_p` (with `T_p = I - p^{-s} V_{log p}` and CAR
creation operators `ε_p`), and its averaged homotopy is `h = (1/N) Σ_p T_p⁻¹ ⊗ ι_p`.

## Proved here

* `koszul_homotopy`: in any `ℚ`-algebra, if the coefficients `T_q` commute with the inverses
  `B_p = T_p⁻¹`, all coefficients commute with the fermionic generators (the tensor-factor
  structure), and `ε_q ι_p + ι_p ε_q = δ_{pq}` (CAR), then `d h + h d = 1` exactly.
  Commutation of `T_q` with `T_p^*` is **not** assumed; only `T_q B_p = B_p T_q`.
* `koszul_sq_zero`: under pairwise commuting `T_p` and anticommuting `ε_p`, `d² = 0`.
* `norm_le_of_contracting_homotopy`: on a complex Hilbert space, if `d² = 0` and `d h + h d = 1`,
  then `‖ψ‖ ≤ √2 ‖h‖ ‖(d + d*) ψ‖` for every `ψ`, i.e. `‖D⁻¹‖ ≤ √2 ‖h‖` for the Dirac operator
  `D = d + d*` (it is bounded below by `(√2 ‖h‖)⁻¹`).

## Not formalized here

The quantitative estimate `‖h‖² ≤ C₀²/N + C₀⁴/N² (S₁² - S₂)`, which uses
`‖[T_p, T_q^*]‖ ≤ 1/√(pq)` and Chebyshev-type prime counting to reach `‖h‖ = O(√L e^{-L/2})`,
is not formalized; nor is the identification of `T_p` with the causal prime shifts. The
remaining step the note itself names — connecting the completed relative causal boundary anomaly
to this contraction — is open. Nothing here is a step that proves RH.
-/

open Finset

namespace GppKoszulHomotopy

section Algebra

variable {R : Type*} [Ring R] [Algebra ℚ R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Koszul differential `d = Σ_q T_q ε_q`. -/
def koszulD (T ε : ι → R) : R := ∑ q, T q * ε q

/-- The averaged homotopy `h = (1/N) Σ_p B_p ι_p`, with `N = |ι|`. -/
noncomputable def koszulH (B ι' : ι → R) : R :=
  ((Fintype.card ι : ℚ)⁻¹) • ∑ p, B p * ι' p

/-- **Exact contracting homotopy.** `d h + h d = 1`. -/
theorem koszul_homotopy [Nonempty ι] (T B ε ι' : ι → R)
    (hTB : ∀ p q, T q * B p = B p * T q) (hinv : ∀ p, T p * B p = 1)
    (hBε : ∀ p q, B p * ε q = ε q * B p) (hTι : ∀ p q, T q * ι' p = ι' p * T q)
    (hCAR : ∀ p q, ε q * ι' p + ι' p * ε q = if p = q then 1 else 0) :
    koszulD T ε * koszulH B ι' + koszulH B ι' * koszulD T ε = 1 := by
  unfold koszulD koszulH
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, sum_mul_sum, sum_mul_sum, sum_comm
    (s := univ) (t := univ) (f := fun p q => B p * ι' p * (T q * ε q)), ← sum_add_distrib]
  have key : ∀ q p, T q * ε q * (B p * ι' p) + B p * ι' p * (T q * ε q) =
      if p = q then 1 else 0 := by
    intro q p
    have e1 : T q * ε q * (B p * ι' p) = T q * B p * (ε q * ι' p) := by
      rw [mul_assoc, ← mul_assoc (ε q), ← hBε p q, mul_assoc, ← mul_assoc]
    have e2 : B p * ι' p * (T q * ε q) = T q * B p * (ι' p * ε q) := by
      rw [mul_assoc, ← mul_assoc (ι' p), ← hTι p q, mul_assoc, ← mul_assoc, hTB p q]
    rw [e1, e2, ← mul_add, hCAR p q]
    split_ifs with h
    · subst h; rw [mul_one, hinv]
    · rw [mul_zero]
  simp_rw [← sum_add_distrib, key]
  simp only [sum_ite_eq', mem_univ, if_true, sum_const, card_univ]
  have hN : (Fintype.card ι : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN, one_smul]

omit [DecidableEq ι] in
/-- **`d² = 0`** for pairwise commuting coefficients (commuting with the generators) and
anticommuting `ε_p` (including `ε_p² = 0`). -/
theorem koszul_sq_zero (T ε : ι → R) (hTT : ∀ p q, T p * T q = T q * T p)
    (hTε : ∀ p q, ε p * T q = T q * ε p) (hεε : ∀ p q, ε p * ε q + ε q * ε p = 0) :
    koszulD T ε * koszulD T ε = 0 := by
  unfold koszulD
  rw [sum_mul_sum]
  set S := ∑ p, ∑ q, T p * ε p * (T q * ε q) with hS
  have hterm : ∀ p q, T p * ε p * (T q * ε q) = T p * T q * (ε p * ε q) := by
    intro p q
    rw [mul_assoc, ← mul_assoc (ε p), hTε p q, mul_assoc, ← mul_assoc]
  have h2 : S + S = 0 := by
    have hswap : S = ∑ p, ∑ q, T p * T q * (ε q * ε p) := by
      rw [hS, sum_comm]
      refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
      rw [hterm, hTT q p]
    calc S + S = ∑ p, ∑ q, T p * T q * (ε p * ε q) + ∑ p, ∑ q, T p * T q * (ε q * ε p) := by
          rw [← hswap]; congr 1
          exact sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => hterm p q))
      _ = 0 := by
          rw [← sum_add_distrib]
          refine sum_eq_zero (fun p _ => ?_)
          rw [← sum_add_distrib]
          refine sum_eq_zero (fun q _ => ?_)
          rw [← mul_add, hεε p q, mul_zero]
  have : (2 : ℚ) • S = 0 := by rw [two_smul, h2]
  have h := congrArg (fun x => ((2 : ℚ)⁻¹) • x) this
  simpa [smul_smul] using h

end Algebra

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Abstract inverse bound.** If `d ∘ d = 0` and `d h + h d = 1`, then
`‖ψ‖ ≤ √2 ‖h‖ ‖(d + d*) ψ‖`. -/
theorem norm_le_of_contracting_homotopy (d h : E →L[ℂ] E) (hd2 : d.comp d = 0)
    (hhom : d.comp h + h.comp d = ContinuousLinearMap.id ℂ E) (ψ : E) :
    ‖ψ‖ ≤ Real.sqrt 2 * ‖h‖ * ‖(d + ContinuousLinearMap.adjoint d) ψ‖ := by
  set a := ‖d ψ‖
  set b := ‖ContinuousLinearMap.adjoint d ψ‖
  -- `‖ψ‖² ≤ ‖h‖ ‖ψ‖ (a + b)`
  have hψ : ψ = d (h ψ) + h (d ψ) := by
    have := congrArg (fun A : E →L[ℂ] E => A ψ) hhom
    simpa using this.symm
  have hsq : ‖ψ‖ ^ 2 ≤ ‖h‖ * ‖ψ‖ * (a + b) := by
    have e' : ‖ψ‖ ^ 2 = (inner ℂ (ContinuousLinearMap.adjoint d ψ) (h ψ) +
        inner ℂ (ContinuousLinearMap.adjoint h ψ) (d ψ)).re := by
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
        ← inner_add_right, ← hψ]
      exact @norm_sq_eq_re_inner ℂ E _ _ _ ψ
    rw [e', Complex.add_re]
    have i1 := (Complex.re_le_norm (inner ℂ (ContinuousLinearMap.adjoint d ψ) (h ψ))).trans
      (norm_inner_le_norm _ _)
    have i2 := (Complex.re_le_norm (inner ℂ (ContinuousLinearMap.adjoint h ψ) (d ψ))).trans
      (norm_inner_le_norm _ _)
    have n1 : ‖h ψ‖ ≤ ‖h‖ * ‖ψ‖ := h.le_opNorm ψ
    have n2 : ‖ContinuousLinearMap.adjoint h ψ‖ ≤ ‖h‖ * ‖ψ‖ := by
      have := (ContinuousLinearMap.adjoint h).le_opNorm ψ
      rwa [ContinuousLinearMap.adjoint.norm_map] at this
    have hb0 : 0 ≤ b := norm_nonneg _
    have ha0 : 0 ≤ a := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left n1 hb0, mul_le_mul_of_nonneg_right n2 ha0]
  -- `‖(d + d*) ψ‖² = a² + b²` since `⟪dψ, d*ψ⟫ = ⟪d d ψ, ψ⟫ = 0`
  have hcross : inner ℂ (d ψ) (ContinuousLinearMap.adjoint d ψ) = 0 := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    have : d (d ψ) = 0 := by
      have := congrArg (fun A : E →L[ℂ] E => A ψ) hd2
      simpa using this
    rw [this, inner_zero_left]
  have hD : ‖(d + ContinuousLinearMap.adjoint d) ψ‖ ^ 2 = a ^ 2 + b ^ 2 := by
    change ‖d ψ + ContinuousLinearMap.adjoint d ψ‖ ^ 2 = a ^ 2 + b ^ 2
    rw [@norm_add_sq ℂ, hcross]
    simp [a, b]
  -- combine: `a + b ≤ √2 √(a² + b²)`
  have hab : a + b ≤ Real.sqrt 2 * ‖(d + ContinuousLinearMap.adjoint d) ψ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg ((d + ContinuousLinearMap.adjoint d) ψ)), hD,
      ← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (a - b)]
  rcases eq_or_lt_of_le (norm_nonneg ψ) with h0 | hpos
  · rw [← h0]; positivity
  · have : ‖ψ‖ ≤ ‖h‖ * (a + b) := by
      have := hsq
      rw [sq, mul_comm ‖h‖ ‖ψ‖, mul_assoc] at this
      exact le_of_mul_le_mul_left this hpos
    calc ‖ψ‖ ≤ ‖h‖ * (a + b) := this
      _ ≤ ‖h‖ * (Real.sqrt 2 * ‖(d + ContinuousLinearMap.adjoint d) ψ‖) :=
          mul_le_mul_of_nonneg_left hab (norm_nonneg _)
      _ = _ := by ring

end Hilbert

end GppKoszulHomotopy
