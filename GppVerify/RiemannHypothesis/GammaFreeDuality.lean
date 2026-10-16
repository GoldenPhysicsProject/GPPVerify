import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The gamma-free prime barrier is exactly a Legendre-dual family of inequalities

Source: Astra, `work/2026-10-16_astra_global_entropy_duality.md` (bridge), in the setting of Codex's
Suzuki gamma-free pivot. Astra's note says "No Lean verification claimed"; this file supplies it,
for **finite truncations** of the prime-power list.

Data: `w j ≥ 0` (the weights `Λ(n_j)/√n_j`) and a monotone `u j` (the logs `log n_j`). Put
`B k = Σ_{j<k} w j`, `C k = Σ_{j<k} w j · u j`, `A K t = Σ_{j<K} w j · (t − u j)₊`,
`V t = 8(cosh(t/2) − 1)` and `V* B = 2B·arsinh(B/4) − 2√(B²+16) + 8`.

* `fenchel`: `B·t − V* B ≤ V t` for `B ≥ 0`, with equality at `t = 2 arsinh(B/4)` (`fenchel_eq`).
* `A_eq_sup`: `A K t = max_{k ≤ K} (B k · t − C k)`, shown as `≤` for every prefix and attained.
* `barrier_iff`: for every finite `K`, `(∀ t ≥ 0, A K t ≤ V t) ↔ (∀ k ≤ K, V* (B k) ≤ C k)`.

**Scope, stated plainly.** This is an exact reformulation of the gamma-free all-time positivity
`T(t) = V(t) − A(t) ≥ 0` for a *finite* list of events. It does not say the actual von Mangoldt
sequence satisfies either side (that is the open arithmetic barrier), does not handle the infinite
list, and says nothing about the converse "RH ⇒ all-time positivity" or Suzuki's eventual-sign
criterion. No RH claim.
-/

namespace GppGammaFreeDuality

open Finset Real

/-- The gamma-free reference cumulant generator `V(t) = 8 (cosh (t/2) − 1)`. -/
noncomputable def V (t : ℝ) : ℝ := 8 * (cosh (t / 2) - 1)

/-- Its Legendre transform on `B ≥ 0`. -/
noncomputable def Vstar (B : ℝ) : ℝ := 2 * B * arsinh (B / 4) - 2 * √(B ^ 2 + 16) + 8

/-- Tangent line of `cosh` at `s ≥ 0`. -/
theorem cosh_tangent {s : ℝ} (hs : 0 ≤ s) (τ : ℝ) :
    cosh s + (τ - s) * sinh s ≤ cosh τ := by
  have hsh : 0 ≤ sinh s := sinh_nonneg_iff.mpr hs
  have hch : 0 < cosh s := cosh_pos s
  have hle : sinh s ≤ cosh s := (sinh_lt_cosh s).le
  obtain ⟨d, rfl⟩ : ∃ d, τ = s + d := ⟨τ - s, by ring⟩
  rw [cosh_add]
  have key : 0 ≤ cosh s * (cosh d - 1) + sinh s * (sinh d - d) := by
    rcases le_total 0 d with hd | hd
    · have h1 : d ≤ sinh d := self_le_sinh_iff.mpr hd
      have h2 : 1 ≤ cosh d := one_le_cosh d
      nlinarith [mul_nonneg hch.le (sub_nonneg.mpr h2), mul_nonneg hsh (sub_nonneg.mpr h1)]
    · set x := -d with hx
      have hx0 : 0 ≤ x := by linarith
      have h1 : x ≤ sinh x := self_le_sinh_iff.mpr hx0
      have h3 : sinh x - x ≤ cosh x - 1 := by
        have h4 := Real.add_one_le_exp (-x)
        have h5 := Real.cosh_sub_sinh x
        linarith
      have e1 : cosh d = cosh x := by rw [hx, cosh_neg]
      have e2 : sinh d - d = -(sinh x - x) := by rw [hx, sinh_neg]; ring
      rw [e1, e2]
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr h1),
        mul_nonneg hch.le (sub_nonneg.mpr h3)]
  nlinarith [key]

/-- Closed form of `V*` through `s = arsinh (B/4)`: `V* B = 8 s sinh s − 8 cosh s + 8`. -/
theorem Vstar_eq (B : ℝ) :
    Vstar B = 8 * arsinh (B / 4) * (B / 4) - 8 * cosh (arsinh (B / 4)) + 8 := by
  have hsq : cosh (arsinh (B / 4)) ^ 2 = (B / 4) ^ 2 + 1 := by
    rw [cosh_sq, sinh_arsinh]
  have : √(B ^ 2 + 16) = 4 * cosh (arsinh (B / 4)) := by
    rw [show B ^ 2 + 16 = (4 * cosh (arsinh (B / 4))) ^ 2 by nlinarith [hsq]]
    exact Real.sqrt_sq (by have := cosh_pos (arsinh (B / 4)); linarith)
  rw [Vstar, this]
  ring

/-- **Fenchel–Young** for `V`: `B t − V* B ≤ V t` for `B ≥ 0`. -/
theorem fenchel {B : ℝ} (hB : 0 ≤ B) (t : ℝ) : B * t - Vstar B ≤ V t := by
  have hs : 0 ≤ arsinh (B / 4) := arsinh_nonneg_iff.mpr (by linarith)
  have hT := cosh_tangent hs (t / 2)
  rw [Vstar_eq B, V]
  rw [sinh_arsinh] at hT
  nlinarith [hT]

/-- Equality at the tilt `t = 2 arsinh (B/4)`. -/
theorem fenchel_eq (B : ℝ) :
    B * (2 * arsinh (B / 4)) - Vstar B = V (2 * arsinh (B / 4)) := by
  rw [Vstar_eq B, V, show 2 * arsinh (B / 4) / 2 = arsinh (B / 4) by ring]
  ring

theorem Vstar_zero : Vstar 0 = 0 := by
  have h : √((0 : ℝ) ^ 2 + 16) = 4 := by
    rw [show ((0 : ℝ) ^ 2 + 16) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  unfold Vstar
  rw [h]
  simp
  norm_num

/-! ### The finite-event sums -/

/-- `A K t = Σ_{j<K} w j (t − u j)₊`. -/
noncomputable def A (w u : ℕ → ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ range K, w j * max (t - u j) 0

noncomputable def Bs (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, w j

noncomputable def Cs (w u : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, w j * u j

theorem affine_eq (w u : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    Bs w k * t - Cs w u k = ∑ j ∈ range k, w j * (t - u j) := by
  simp only [Bs, Cs, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Every prefix affine function lies below `A`. -/
theorem affine_le_A {w u : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) {K k : ℕ} (hk : k ≤ K) (t : ℝ) :
    Bs w k * t - Cs w u k ≤ A w u K t := by
  rw [affine_eq]
  calc ∑ j ∈ range k, w j * (t - u j) ≤ ∑ j ∈ range k, w j * max (t - u j) 0 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw j)
    _ ≤ A w u K t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          fun j _ _ => mul_nonneg (hw j) (le_max_right _ _)

/-- ... and some prefix attains it (the last active event), for monotone `u`. -/
theorem A_attained {w u : ℕ → ℝ} (hu : Monotone u) (K : ℕ) (t : ℝ) :
    ∃ k ≤ K, A w u K t = Bs w k * t - Cs w u k := by
  induction K with
  | zero => exact ⟨0, le_rfl, by simp [A, Bs, Cs]⟩
  | succ K ih =>
    by_cases h : t ≤ u K
    · obtain ⟨k, hk, hk'⟩ := ih
      refine ⟨k, hk.trans (Nat.le_succ K), ?_⟩
      rw [A, Finset.sum_range_succ, ← A, hk', max_eq_right (by linarith)]
      ring
    · refine ⟨K + 1, le_rfl, ?_⟩
      rw [affine_eq, A]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : u j ≤ u K := hu (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [max_eq_left (by linarith)]

/-- **The gamma-free barrier, finite truncation.** For `w ≥ 0`, `u` monotone, and every `K`,
`A_K ≤ V` on `t ≥ 0` iff `V* (B k) ≤ C k` for every prefix `k ≤ K`. -/
theorem barrier_iff {w u : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hu : Monotone u) (K : ℕ) :
    (∀ t, 0 ≤ t → A w u K t ≤ V t) ↔ ∀ k ≤ K, Vstar (Bs w k) ≤ Cs w u k := by
  have hB : ∀ k, 0 ≤ Bs w k := fun k => Finset.sum_nonneg fun j _ => hw j
  constructor
  · intro h k hk
    have h1 := affine_le_A (u := u) hw hk (2 * arsinh (Bs w k / 4))
    have h2 := h (2 * arsinh (Bs w k / 4))
      (by have := arsinh_nonneg_iff.mpr (show 0 ≤ Bs w k / 4 by linarith [hB k]); linarith)
    have h3 := fenchel_eq (Bs w k)
    linarith
  · intro h t _
    obtain ⟨k, hk, hk'⟩ := A_attained (w := w) hu K t
    have := fenchel (hB k) t
    have := h k hk
    linarith

end GppGammaFreeDuality
