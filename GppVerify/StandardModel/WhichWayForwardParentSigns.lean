import Mathlib.Tactic
import GppVerify.StandardModel.WhichWayForwardPauliStrings
import GppVerify.StandardModel.WhichWayForwardFamilySigns

/-!
# *Which Way Is Forward?*: parent charge-conjugation signs (G4)

The generators of the Pauli tensor construction, their squares,
conjugation eigenvalues, and pairwise anticommutation, plus the
movement lemmas behind the intertwining uniformity.

The generator with index `j` (of `2k`, for signature `(2k - 2, 2)`)
has `Z` below slot `j / 2`, `X` (even `j`) or `Y` (odd `j`) at that
slot, and `I` above it; the last two generators are scaled by `i`.
Its square is `-1` exactly when scaled, and its conjugation
eigenvalue `δ` is `(-1)` raised to its `Y` count, times `-1` when
scaled. Distinct generators anticommute, checked per pair from the
slot data by the string engine's odd-anticommute criterion.
-/

namespace GppWhichWayForwardParentSigns

open GppWhichWayForwardPauliStrings Matrix
open scoped Kronecker

/-- The `j`-th generator string in `k` slots: `Z` below slot `j / 2`,
`X` or `Y` at it according to the parity of `j`, `I` above. -/
def genString (k j : ℕ) (i : Fin k) : Pauli :=
  if (i : ℕ) < j / 2 then Pauli.Z
  else if (i : ℕ) = j / 2 then (if Even j then Pauli.X else Pauli.Y)
  else Pauli.I

/-- The scaling of generator `j`: the last two (the `q = 2` block)
carry a factor `i`. -/
def genScale (k j : ℕ) : ℂ := if 2 * k - 2 ≤ j then Complex.I else 1

/-- The `j`-th generator matrix. -/
def genMatrix (k j : ℕ) : Matrix (idx k) (idx k) ℂ :=
  genScale k j • stringMatrix k (genString k j)

/-- A generator squares to `-1` when scaled, `+1` when not. -/
theorem genMatrix_sq (k j : ℕ) :
    genMatrix k j * genMatrix k j
      = (if 2 * k - 2 ≤ j then -1 else 1) • 1 := by
  unfold genMatrix genScale
  rw [Matrix.smul_mul, Matrix.mul_smul, stringMatrix_sq, smul_smul]
  by_cases h : 2 * k - 2 ≤ j <;> simp [h, Complex.I_mul_I]

/-- The conjugation phase of a generator string is its `Y` parity:
only the special slot contributes, through `Y` at odd `j`. -/
theorem conjPhaseF_genString (k j : ℕ) (hj : j < 2 * k) :
    conjPhaseF (genString k j) = if Even j then 1 else -1 := by
  have hk : j / 2 < k := by omega
  set i0 : Fin k := ⟨j / 2, hk⟩ with hi0
  have hprod : conjPhaseF (genString k j)
      = ∏ i, slotConj (genString k j i) := rfl
  rw [hprod, Finset.prod_eq_single i0]
  · by_cases he : Even j <;> simp [genString, hi0, he, slotConj]
  · intro i _ hii
    have hi : (i : ℕ) ≠ j / 2 := by
      intro he
      apply hii
      exact Fin.ext he
    by_cases hlt : (i : ℕ) < j / 2 <;> simp [genString, hi, hlt, slotConj]
  · simp

/-- The conjugation eigenvalue of a generator: the `Y` parity, times
`-1` when scaled. -/
def genDelta (k j : ℕ) : ℂ :=
  (if 2 * k - 2 ≤ j then -1 else 1) * conjPhaseF (genString k j)

/-- Conjugation of a generator is its eigenvalue times itself. -/
theorem genMatrix_conj (k j : ℕ) :
    (genMatrix k j).map (starRingEnd ℂ) = genDelta k j • genMatrix k j := by
  have hmap : ∀ (c : ℂ) (M : Matrix (idx k) (idx k) ℂ),
      (c • M).map (starRingEnd ℂ)
        = (starRingEnd ℂ) c • M.map (starRingEnd ℂ) := by
    intro c M
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  unfold genMatrix genDelta
  rw [hmap, stringMatrix_conj]
  by_cases h : 2 * k - 2 ≤ j
  · have hstar : (starRingEnd ℂ) (genScale k j) = -Complex.I := by
      simp [genScale, h, Complex.conj_I]
    rw [hstar]
    simp only [smul_smul]
    congr 1
    simp only [genScale, h, if_true, if_false]
    ring
  · have hstar : (starRingEnd ℂ) (genScale k j) = 1 := by
      simp [genScale, h]
    rw [hstar]
    simp only [smul_smul]
    congr 1
    simp only [genScale, h, if_true, if_false]
    ring

/-- Two generators whose anticommuting-slot count is odd anticommute
as matrices. -/
theorem genMatrix_anticommute_of_odd {k a b : ℕ}
    (h : Odd (antiCountF (genString k a) (genString k b))) :
    genMatrix k a * genMatrix k b
      = - (genMatrix k b * genMatrix k a) := by
  have hS := stringMatrix_anticommute_of_odd (n := k) h
  unfold genMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, hS, smul_neg,
    mul_comm (genScale k a) (genScale k b)]

/-- Two such generators are different matrices: anticommutation plus
a square of `±1` forbids equality. -/
theorem genMatrix_ne {k a b : ℕ}
    (h : Odd (antiCountF (genString k a) (genString k b))) :
    genMatrix k a ≠ genMatrix k b := by
  intro heq
  have hanti := genMatrix_anticommute_of_odd h
  rw [heq] at hanti
  have hsq := genMatrix_sq k b
  rw [hsq] at hanti
  have h01 := congrArg
    (fun M : Matrix (idx k) (idx k) ℂ => M (idxDefault k) (idxDefault k)) hanti
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h01
  by_cases hb : 2 * k - 2 ≤ b <;>
    simp only [hb, if_true, if_false, neg_neg] at h01 <;>
    norm_num [Complex.ext_iff] at h01

/-- The reverse pass-through, derived from layer A's
`prod_mul_of_anticommutes` by the self-inverse sign. -/
theorem mul_prod_of_anticommutes {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (L : List (Matrix n n ℂ))
    (h : ∀ B ∈ L, A * B = -(B * A)) :
    A * L.prod = (-1 : ℂ) ^ L.length • (L.prod * A) := by
  have h1 := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes L h
  have h2 : ((-1 : ℂ) ^ L.length) * ((-1 : ℂ) ^ L.length) = 1 := by
    rw [← pow_add, ← two_mul]
    exact Even.neg_one_pow ⟨L.length, by ring⟩
  calc A * L.prod
      = ((-1 : ℂ) ^ L.length) • (((-1 : ℂ) ^ L.length) • (A * L.prod)) := by
        rw [smul_smul, h2, one_smul]
    _ = ((-1 : ℂ) ^ L.length) • (L.prod * A) := by rw [h1]

/-- **Intertwining, member case.** If `γ` is a member of a pairwise
anticommuting, duplicate-free family `L`, then moving `γ` across the
family product `B` costs `(-1)^(m-1)`, independent of its position:
`B * γ = (-1)^(m-1) • (γ * B)`. -/
theorem prod_mul_of_mem {n : Type*} [Fintype n] [DecidableEq n]
    {L : List (Matrix n n ℂ)} {γ : Matrix n n ℂ} (hγ : γ ∈ L) (hnd : L.Nodup)
    (hanti : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → A * B = -(B * A)) :
    L.prod * γ = (-1 : ℂ) ^ (L.length - 1) • (γ * L.prod) := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hγ
  have hγ2 : γ ∉ L₂ := by
    have hnd2 : (γ :: L₂).Nodup := (List.nodup_append.mp hnd).2.1
    exact (List.nodup_cons.mp hnd2).1
  have hγmem : γ ∈ L₁ ++ γ :: L₂ :=
    List.mem_append_right L₁ List.mem_cons_self
  have hanti₂ : ∀ B ∈ L₂, γ * B = -(B * γ) := by
    intro B hB
    apply hanti γ hγmem B
      (List.mem_append_right L₁ (List.mem_cons_of_mem γ hB))
    intro hBeq
    exact hγ2 (hBeq ▸ hB)
  have hanti₁ : ∀ B ∈ L₁, γ * B = -(B * γ) := by
    intro B hB
    apply hanti γ hγmem B (List.mem_append_left (γ :: L₂) hB)
    intro hBeq
    have hdisj := (List.nodup_append.mp hnd).2.2
    exact hdisj B hB γ List.mem_cons_self hBeq.symm
  have hlen : (L₁ ++ γ :: L₂).length - 1 = L₁.length + L₂.length := by
    simp [List.length_append]
  rw [hlen]
  have hprod : (L₁ ++ γ :: L₂).prod = L₁.prod * (γ * L₂.prod) := by
    rw [List.prod_append, List.prod_cons]
  rw [hprod]
  have stepR := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes L₂ hanti₂
  have stepL := mul_prod_of_anticommutes L₁ hanti₁
  have e1 : L₁.prod * (γ * L₂.prod) * γ
      = (-1 : ℂ) ^ L₂.length • (L₁.prod * ((γ * γ) * L₂.prod)) := by
    calc L₁.prod * (γ * L₂.prod) * γ
        = L₁.prod * (γ * (L₂.prod * γ)) := by simp only [mul_assoc]
      _ = L₁.prod * (γ * (((-1 : ℂ) ^ L₂.length) • (γ * L₂.prod))) := by rw [stepR]
      _ = (-1 : ℂ) ^ L₂.length • (L₁.prod * ((γ * γ) * L₂.prod)) := by
          rw [Matrix.mul_smul, Matrix.mul_smul]
          simp only [mul_assoc]
  have e2 : γ * (L₁.prod * (γ * L₂.prod))
      = (-1 : ℂ) ^ L₁.length • (L₁.prod * ((γ * γ) * L₂.prod)) := by
    calc γ * (L₁.prod * (γ * L₂.prod))
        = (γ * L₁.prod) * (γ * L₂.prod) := by simp only [mul_assoc]
      _ = (((-1 : ℂ) ^ L₁.length) • (L₁.prod * γ)) * (γ * L₂.prod) := by rw [stepL]
      _ = (-1 : ℂ) ^ L₁.length • (L₁.prod * ((γ * γ) * L₂.prod)) := by
          rw [Matrix.smul_mul]
          simp only [mul_assoc]
  rw [e1, e2, smul_smul, ← pow_add]
  congr 1
  rw [show L₁.length + L₂.length + L₁.length = L₂.length + 2 * L₁.length from by omega,
    pow_add, pow_mul]
  norm_num

end GppWhichWayForwardParentSigns
