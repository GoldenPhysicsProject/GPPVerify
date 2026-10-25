import Mathlib.Tactic

/-!
# The su(2) ladder on the equator modes `H_N`

Source: Codex, GPP-bridge PR #11 comment 6392046099 (Discovery2 PR #23), item 1, a finite
model of Daniel's "fundamental information lives on the 1D equator" hypothesis. Daniel Toupin /
Golden Physics Project, with AI assistance from Codex (statement) and Claude Code (formalization).

Write a vector of `H_N = span{e^{ikφ} : 0 ≤ k < N}` as a coefficient sequence `c : ℕ → K`
(`c k` the coefficient of `e_k`). Codex's operators `E e_k = k e_{k−1}`,
`F e_k = (N−1−k) e_{k+1}` and `H e_k = (N−1−2k) e_k` act on coefficients as
`(E c)_k = (k+1) c_{k+1}`, `(F c)_k = (N−k) c_{k−1}` (and `0` at `k = 0`), `(H c)_k = (N−1−2k) c_k`.

* `comm_HE`, `comm_HF`, `comm_EF`: `[H, E] = 2E`, `[H, F] = −2F`, `[E, F] = H`, on every
  sequence (any commutative ring).
* `F_preserves`, `E_preserves`, `H_preserves`: the span of `e_0, …, e_{N−1}` (support below `N`)
  is invariant, so these are the operators on `H_N`.
* `casimir`: `H² + 2(EF + FE) = (N−1)(N+1)`, i.e. `(H/2)² + (EF + FE)/2 = j(j+1)` with
  `j = (N−1)/2`, on every sequence.
* `detailed_balance` and `adjoint`: with weights `w_k = 1/C(N−1, k)`, `⟨E c, d⟩_w = ⟨c, F d⟩_w`
  for `c, d ∈ H_N`. So `E† = F` for this positive metric.

**Context.** The equator thread belongs to the existing holographic-chain programme (Daniel's
March 2026 Holographic Chain paper; `GppHolographicChain`). It is not a new project. The
`d = 1` equator and `d = 2` horizon principal axes `Re Δ = 1/2, 1` are already formalized in
`GppConformalShadowPrincipalSeries`, and the half-density dilation behind them in every `d` is in
`GppHalfDensityDilation` (Codex correction, PR #11 comment 6392669042). This file is a finite toy
inside that programme.

**Scope.** This is the spin-`j` representation in the standard binomial basis, a classical fact.
The generation of `Mat_N`, the `End(V_j) = ⊕ V_ℓ` decomposition, the CAR Fock singlet count
`ln d_N = N² ln 2 + O(ln N)`, the thermal falsifier and the quarter-coefficient discussion are not
formalized here. No black-hole microstate claim is made, and no claim about RH or BSD.
-/

set_option autoImplicit false

open Finset

namespace GppEquatorSU2

variable {K : Type*} [CommRing K] (N : ℕ)

/-- Lowering `(E c)_k = (k+1) c_{k+1}`. -/
def E (c : ℕ → K) (k : ℕ) : K := ((k : K) + 1) * c (k + 1)

/-- Raising `(F c)_k = (N−k) c_{k−1}`, `0` at `k = 0`. -/
def F (c : ℕ → K) : ℕ → K
  | 0 => 0
  | k + 1 => ((N : K) - (k + 1)) * c k

/-- Weight `(H c)_k = (N−1−2k) c_k`. -/
def H (c : ℕ → K) (k : ℕ) : K := ((N : K) - 1 - 2 * k) * c k

variable {N}

theorem comm_HE (c : ℕ → K) (k : ℕ) : H N (E c) k - E (H N c) k = 2 * E c k := by
  simp only [H, E]; push_cast; ring

theorem comm_HF (c : ℕ → K) (k : ℕ) : H N (F N c) k - F N (H N c) k = -2 * F N c k := by
  cases k with
  | zero => simp [H, F]
  | succ k => simp only [H, F]; push_cast; ring

theorem comm_EF (c : ℕ → K) (k : ℕ) : E (F N c) k - F N (E c) k = H N c k := by
  cases k with
  | zero => simp only [E, F, H]; push_cast; ring
  | succ k => simp only [E, F, H]; push_cast; ring

/-- Support below `N`: the coefficient sequences of `H_N`. -/
def InHN (N : ℕ) (c : ℕ → K) : Prop := ∀ k, N ≤ k → c k = 0

theorem E_preserves {c : ℕ → K} (hc : InHN N c) : InHN N (E c) := by
  intro k hk; simp [E, hc (k + 1) (by omega)]

theorem H_preserves {c : ℕ → K} (hc : InHN N c) : InHN N (H N c) := by
  intro k hk; simp [H, hc k hk]

theorem F_preserves {c : ℕ → K} (hc : InHN N c) : InHN N (F N c) := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k =>
    simp only [F]
    rcases Nat.lt_or_ge k N with h | h
    · have : k + 1 = N := by omega
      subst this; push_cast; ring
    · rw [hc k h, mul_zero]

/-- **Casimir.** `H² + 2(EF + FE) = (N − 1)(N + 1)`, i.e. `J² = j(j+1)` with `j = (N−1)/2`. -/
theorem casimir (c : ℕ → K) (k : ℕ) :
    H N (H N c) k + 2 * (E (F N c) k + F N (E c) k) = ((N : K) - 1) * ((N : K) + 1) * c k := by
  cases k with
  | zero => simp only [H, E, F]; push_cast; ring
  | succ k => simp only [H, E, F]; push_cast; ring

section Metric

variable {L : Type*} [Field L] [CharZero L]

/-- The weight `w_k = 1/C(N−1, k)`. -/
noncomputable def w (N k : ℕ) : L := ((Nat.choose (N - 1) k : ℕ) : L)⁻¹

/-- **Detailed balance.** For `k + 1 < N`, `w_k (k+1) = w_{k+1} (N − (k+1))`. -/
theorem detailed_balance {N k : ℕ} (hk : k + 1 < N) :
    w (L := L) N k * ((k : L) + 1) = w N (k + 1) * ((N : L) - (k + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [w, Nat.add_sub_cancel]
  have h1 : (n.choose k : L) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h2 : (n.choose (k + 1) : L) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hc : ((n.choose (k + 1) : ℕ) : L) * ((k : L) + 1) = (n.choose k : L) * ((n : L) - k) := by
    have := congrArg (Nat.cast (R := L)) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub (show k ≤ n by omega)] at this
    exact this
  field_simp
  push_cast
  linear_combination hc

/-- **`E† = F`** for the metric `⟨c, d⟩_w = Σ_{k<N} w_k c_k d_k` on `H_N`. -/
theorem adjoint {N : ℕ} {c d : ℕ → L} (hc : InHN N c) :
    ∑ k ∈ range N, w N k * E c k * d k = ∑ k ∈ range N, w N k * c k * F N d k := by
  rcases N with _ | n
  · simp
  rw [sum_range_succ, sum_range_succ']
  simp only [E, F, hc (n + 1) le_rfl, mul_zero, zero_mul, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have := detailed_balance (L := L) (N := n + 1) (k := k) (by have := mem_range.mp hk; omega)
  push_cast at this ⊢
  linear_combination c (k + 1) * d k * this

end Metric

end GppEquatorSU2
