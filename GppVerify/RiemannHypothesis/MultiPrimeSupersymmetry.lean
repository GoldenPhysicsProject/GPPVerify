import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

/-!
# Multi-prime supersymmetric pairing with Klein factors

`ArithmeticFermionSector` gave the explicit single-prime pairing `Q² = 0`, `{Q, Q†} = N_b + N_f`
and noted that the multi-prime version needs Klein factors. This file supplies them.

For `m` modes (primes labelled `Fin m`) the state space is functions on
`Cfg m = (Fin m → ℕ) × (Fin m → Bool)` (boson occupations `k_i`, fermion occupations `b_i`). The
**Klein factor** `kl i b = ∏_{j<i} (−1)^{b_j}` counts the fermions in earlier modes. The operators

* `(Q_i ψ)(k,b) = [b_i = false ∧ k_i ≠ 0] · kl_i(b) · √(k_i) · ψ(k − e_i, b + f_i)`,
* `(Q_i† ψ)(k,b) = [b_i = true] · kl_i(b) · √(k_i + 1) · ψ(k + e_i, b − f_i)`

(same conventions as the single-prime file) satisfy, for all `i ≠ j`:

* `Q_cross`: `Q_i Q_j + Q_j Q_i = 0`; `Qd_cross`: `Q_i† Q_j† + Q_j† Q_i† = 0`;
* `anticomm_cross`: `Q_i Q_j† + Q_j† Q_i = 0`;

and for each `i`: `Q_sq`: `Q_i² = 0` and `anticomm_self`: `Q_i Q_i† + Q_i† Q_i = N_i`
(`N_i = k_i + b_i`). Hence `Q = Σ_i Q_i` has `Q² = 0` and `{Q, Q†} = Σ_i N_i`.

## Scope

Algebra of finitely many modes with the standard Jordan–Wigner-type sign. It does **not** say the
primes are physical modes of a supersymmetric theory, it has no annihilation dynamics, and it says
nothing about zeros. No RH claim.
-/

open Function

namespace GppMultiPrimeSusy

variable {m : ℕ}

/-- Boson occupations and fermion occupations of `m` modes. -/
abbrev Cfg (m : ℕ) := (Fin m → ℕ) × (Fin m → Bool)

/-- The Klein factor `∏_{j<i} (−1)^{b_j}`. -/
def kl (i : Fin m) (b : Fin m → Bool) : ℂ :=
  ∏ j ∈ Finset.univ.filter (· < i), (if b j then (-1 : ℂ) else 1)

noncomputable def Q (i : Fin m) (ψ : Cfg m → ℂ) : Cfg m → ℂ := fun s =>
  if s.2 i = false ∧ s.1 i ≠ 0 then
    kl i s.2 * (Real.sqrt (s.1 i) : ℂ) * ψ (update s.1 i (s.1 i - 1), update s.2 i true)
  else 0

noncomputable def Qd (i : Fin m) (ψ : Cfg m → ℂ) : Cfg m → ℂ := fun s =>
  if s.2 i = true then
    kl i s.2 * (Real.sqrt (s.1 i + 1) : ℂ) * ψ (update s.1 i (s.1 i + 1), update s.2 i false)
  else 0

/-- The number operator of mode `i`. -/
def N (i : Fin m) (ψ : Cfg m → ℂ) : Cfg m → ℂ := fun s =>
  ((s.1 i + (if s.2 i then 1 else 0) : ℕ) : ℂ) * ψ s

/-- The Klein factor of mode `i` does not see mode `i`. -/
theorem kl_update_self (i : Fin m) (b : Fin m → Bool) (v : Bool) :
    kl i (update b i v) = kl i b := by
  unfold kl
  refine Finset.prod_congr rfl fun j hj => ?_
  have : j ≠ i := (Finset.mem_filter.mp hj).2.ne
  simp [update_of_ne this]

theorem kl_update_gt {i j : Fin m} (h : i < j) (b : Fin m → Bool) (v : Bool) :
    kl i (update b j v) = kl i b := by
  unfold kl
  refine Finset.prod_congr rfl fun l hl => ?_
  have : l ≠ j := (lt_trans (Finset.mem_filter.mp hl).2 h).ne
  simp [update_of_ne this]

/-- Flipping an earlier fermion flips the sign of the Klein factor. -/
theorem kl_update_lt {i j : Fin m} (h : j < i) (b : Fin m → Bool) (hb : b j = false) :
    kl i (update b j true) = - kl i b := by
  unfold kl
  have hj : j ∈ Finset.univ.filter (· < i) := by simp [h]
  rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ (fun l => if b l then (-1 : ℂ) else 1) hj]
  have : ∏ l ∈ (Finset.univ.filter (· < i)).erase j, (if update b j true l then (-1 : ℂ) else 1) =
      ∏ l ∈ (Finset.univ.filter (· < i)).erase j, (if b l then (-1 : ℂ) else 1) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    simp [update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]; simp [hb]

theorem kl_update_lt' {i j : Fin m} (h : j < i) (b : Fin m → Bool) (hb : b j = true) :
    kl i (update b j false) = - kl i b := by
  have := kl_update_lt h (update b j false) (by simp)
  rw [update_idem] at this
  rw [update_eq_self_iff.mpr hb.symm] at this
  linear_combination this

theorem kl_sq (i : Fin m) (b : Fin m → Bool) : kl i b * kl i b = 1 := by
  unfold kl
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  split_ifs <;> norm_num

theorem Q_cross_lt {i j : Fin m} (h : i < j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Q j ψ) s + Q j (Q i ψ) s = 0 := by
  obtain ⟨k, b⟩ := s
  have hij : i ≠ j := h.ne
  have hji : j ≠ i := hij.symm
  by_cases hbi : b i = false <;> by_cases hbj : b j = false <;>
    by_cases hki : k i = 0 <;> by_cases hkj : k j = 0 <;>
    simp [Q, hij, hji, hbi, hbj, hki, hkj, update_of_ne, update_comm hij,
      kl_update_gt h, kl_update_lt h] <;> ring

/-- **`Q_i Q_j + Q_j Q_i = 0`** for distinct modes (this is what the Klein factors are for). -/
theorem Q_cross {i j : Fin m} (hij : i ≠ j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Q j ψ) s + Q j (Q i ψ) s = 0 := by
  rcases hij.lt_or_gt with h | h
  · exact Q_cross_lt h ψ s
  · rw [add_comm]; exact Q_cross_lt h ψ s

theorem Qd_cross_lt {i j : Fin m} (h : i < j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Qd i (Qd j ψ) s + Qd j (Qd i ψ) s = 0 := by
  obtain ⟨k, b⟩ := s
  have hij : i ≠ j := h.ne
  have hji : j ≠ i := hij.symm
  by_cases hbi : b i = false <;> by_cases hbj : b j = false <;>
    by_cases hki : k i = 0 <;> by_cases hkj : k j = 0 <;>
    simp [Q, Qd, hij, hji, hbi, hbj, hki, hkj, update_of_ne, update_comm hij,
      kl_update_gt h, kl_update_lt h, kl_update_lt' h] <;> ring

theorem Qd_cross {i j : Fin m} (hij : i ≠ j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Qd i (Qd j ψ) s + Qd j (Qd i ψ) s = 0 := by
  rcases hij.lt_or_gt with h | h
  · exact Qd_cross_lt h ψ s
  · rw [add_comm]; exact Qd_cross_lt h ψ s

theorem anticomm_cross_lt {i j : Fin m} (h : i < j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Qd j ψ) s + Qd j (Q i ψ) s = 0 := by
  obtain ⟨k, b⟩ := s
  have hij : i ≠ j := h.ne
  have hji : j ≠ i := hij.symm
  by_cases hbi : b i = false <;> by_cases hbj : b j = false <;>
    by_cases hki : k i = 0 <;> by_cases hkj : k j = 0 <;>
    simp [Q, Qd, hij, hji, hbi, hbj, hki, hkj, update_of_ne, update_comm hij,
      kl_update_gt h, kl_update_lt h, kl_update_lt' h] <;> ring

theorem anticomm_cross_gt {i j : Fin m} (h : j < i) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Qd j ψ) s + Qd j (Q i ψ) s = 0 := by
  obtain ⟨k, b⟩ := s
  have hij : i ≠ j := h.ne'
  have hji : j ≠ i := hij.symm
  by_cases hbi : b i = false <;> by_cases hbj : b j = false <;>
    by_cases hki : k i = 0 <;> by_cases hkj : k j = 0 <;>
    simp [Q, Qd, hij, hji, hbi, hbj, hki, hkj, update_of_ne, update_comm hij,
      kl_update_gt h, kl_update_lt h, kl_update_lt' h] <;> ring

/-- **`Q_i Q_j† + Q_j† Q_i = 0`** for distinct modes. -/
theorem anticomm_cross {i j : Fin m} (hij : i ≠ j) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Qd j ψ) s + Qd j (Q i ψ) s = 0 := by
  rcases hij.lt_or_gt with h | h
  · exact anticomm_cross_lt h ψ s
  · exact anticomm_cross_gt h ψ s

theorem Q_sq (i : Fin m) (ψ : Cfg m → ℂ) : Q i (Q i ψ) = 0 := by
  funext ⟨k, b⟩
  by_cases h : b i = false <;> simp [Q, h]

theorem Qd_sq (i : Fin m) (ψ : Cfg m → ℂ) : Qd i (Qd i ψ) = 0 := by
  funext ⟨k, b⟩
  by_cases h : b i = true <;> simp [Qd, h]

private lemma sqrt_mul_self_succ (k : ℕ) :
    ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) = (k : ℂ) + 1 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring

/-- **`{Q_i, Q_i†} = N_i`** (`N_i = k_i + b_i`). -/
theorem anticomm_self (i : Fin m) (ψ : Cfg m → ℂ) (s : Cfg m) :
    Q i (Qd i ψ) s + Qd i (Q i ψ) s = N i ψ s := by
  obtain ⟨k, b⟩ := s
  have hkl := kl_sq i b
  have key : ∀ a c x : ℂ, a * c * (a * c * x) = (a * a) * (c * c) * x := by intros; ring
  cases hb : b i
  · have e2 : update b i false = b := update_eq_self_iff.mpr hb.symm
    by_cases hk : k i = 0
    · simp [Q, Qd, N, hb, hk]
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have h := sqrt_mul_self_succ j
      have e1 : update k i (j + 1) = k := update_eq_self_iff.mpr hj.symm
      simp [Q, Qd, N, hb, hk, hj, kl_update_self, e1, e2]
      rw [key, hkl, h]; ring
  · have hne : k i + 1 ≠ 0 := by omega
    have e2 : update b i true = b := update_eq_self_iff.mpr hb.symm
    have h := sqrt_mul_self_succ (k i)
    simp [Q, Qd, N, hb, kl_update_self, e2]
    rw [key, hkl, h]; ring

/-! ### The total supercharge -/

/-- The total supercharge `Q = Σ_i Q_i`. -/
noncomputable def Qt (ψ : Cfg m → ℂ) : Cfg m → ℂ := fun s => ∑ i, Q i ψ s

/-- Its adjoint `Q† = Σ_i Q_i†`. -/
noncomputable def Qdt (ψ : Cfg m → ℂ) : Cfg m → ℂ := fun s => ∑ i, Qd i ψ s

theorem Q_sum (i : Fin m) {ι : Type*} (S : Finset ι) (g : ι → Cfg m → ℂ) (s : Cfg m) :
    Q i (fun t => ∑ j ∈ S, g j t) s = ∑ j ∈ S, Q i (g j) s := by
  unfold Q
  split_ifs
  · rw [Finset.mul_sum]
  · simp

theorem Qd_sum (i : Fin m) {ι : Type*} (S : Finset ι) (g : ι → Cfg m → ℂ) (s : Cfg m) :
    Qd i (fun t => ∑ j ∈ S, g j t) s = ∑ j ∈ S, Qd i (g j) s := by
  unfold Qd
  split_ifs
  · rw [Finset.mul_sum]
  · simp

/-- If `f(i,j) + f(j,i) = 0` for all `i, j` then `Σ_{i,j} f(i,j) = 0`. -/
private lemma double_sum_antisymm (f : Fin m → Fin m → ℂ) (h : ∀ i j, f i j + f j i = 0) :
    ∑ i, ∑ j, f i j = 0 := by
  have h1 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, f j i := Finset.sum_comm
  have h2 : (∑ i, ∑ j, f i j) + ∑ i, ∑ j, f j i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => h i j
  rw [← h1] at h2
  have : (2 : ℂ) * ∑ i, ∑ j, f i j = 0 := by linear_combination h2
  simpa using this

/-- **`Q² = 0`** for the total supercharge. -/
theorem Qt_sq (ψ : Cfg m → ℂ) (s : Cfg m) : Qt (Qt ψ) s = 0 := by
  unfold Qt
  simp only [Q_sum]
  apply double_sum_antisymm
  intro i j
  by_cases hij : i = j
  · subst hij; rw [show Q i (Q i ψ) s = 0 from by rw [Q_sq]; rfl]; simp
  · exact Q_cross hij ψ s

/-- **`{Q, Q†} = Σ_i N_i`** for the total supercharge. -/
theorem anticomm_total (ψ : Cfg m → ℂ) (s : Cfg m) :
    Qt (Qdt ψ) s + Qdt (Qt ψ) s = ∑ i, N i ψ s := by
  unfold Qt Qdt
  simp only [Q_sum, Qd_sum]
  rw [Finset.sum_comm (f := fun j i => Qd j (Q i ψ) s)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · exact anticomm_self i ψ s
  · intro j _ hji; exact anticomm_cross hji.symm ψ s
  · intro h; exact absurd (Finset.mem_univ i) h

end GppMultiPrimeSusy
