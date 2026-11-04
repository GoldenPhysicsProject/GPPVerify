import Mathlib.Tactic
import GppVerify.StandardModel.WhichWayForwardParentSigns
import GppVerify.StandardModel.WhichWayForwardFamilySigns

/-!
# *Which Way Is Forward?*: the parent families at (6,2) and (10,2)

The real and imaginary families of the Pauli tensor construction,
fed through layer A (`WhichWayForwardFamilySigns`) and the movement
lemmas of `WhichWayForwardParentSigns`.

The theorem `parentquaternionic`, as stated in the paper: for the
product `B` of either family,
`B * conj(B) = s • 1` with `s = -1` for both families at (6,2)
(quaternionic) and `s = +1` for both families at (10,2) (real), and
`B` intertwines with every generator with one uniform sign per
family: `B * conj(γ) = ε • (γ * B)`, `ε = -1` for a real family and
`ε = +1` for an imaginary family, at both signatures.
-/

namespace GppWhichWayForwardParentFamilies

open GppWhichWayForwardPauliStrings GppWhichWayForwardParentSigns Matrix
open scoped Kronecker

/-! ## The (6,2) families -/

/-- Generator indices of the real family at (6,2). -/
def fam62realIdx : List ℕ := [0, 2, 4, 7]

/-- Generator indices of the imaginary family at (6,2). -/
def fam62imagIdx : List ℕ := [1, 3, 5, 6]

/-- The real family at (6,2), as matrices. -/
def fam62real : List (Matrix (idx 4) (idx 4) ℂ) := fam62realIdx.map (genMatrix 4)

/-- The imaginary family at (6,2), as matrices. -/
def fam62imag : List (Matrix (idx 4) (idx 4) ℂ) := fam62imagIdx.map (genMatrix 4)

theorem fam62real_pairwise :
    ∀ A ∈ fam62real, ∀ B ∈ fam62real, A ≠ B → A * B = -(B * A) := by
  intro A hA B hB hne
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  simp only [fam62realIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact genMatrix_anticommute_of_odd (by decide)

theorem fam62imag_pairwise :
    ∀ A ∈ fam62imag, ∀ B ∈ fam62imag, A ≠ B → A * B = -(B * A) := by
  intro A hA B hB hne
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  simp only [fam62imagIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact genMatrix_anticommute_of_odd (by decide)

theorem fam62real_nodup : fam62real.Nodup := by
  apply List.Nodup.map_on _ (by decide : fam62realIdx.Nodup)
  intro x hx y hy hxy
  simp only [fam62realIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    (try rfl) <;> exact absurd hxy (genMatrix_ne (by decide))

theorem fam62imag_nodup : fam62imag.Nodup := by
  apply List.Nodup.map_on _ (by decide : fam62imagIdx.Nodup)
  intro x hx y hy hxy
  simp only [fam62imagIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    (try rfl) <;> exact absurd hxy (genMatrix_ne (by decide))

/-- The square function for the (6,2) real family: `-1` at the scaled
member `7`, `+1` elsewhere. -/
noncomputable def sq62real : Matrix (idx 4) (idx 4) ℂ → ℂ :=
  fun A => if A = genMatrix 4 7 then -1 else 1

/-- The square function for the (6,2) imaginary family: `-1` at the
scaled member `6`, `+1` elsewhere. -/
noncomputable def sq62imag : Matrix (idx 4) (idx 4) ℂ → ℂ :=
  fun A => if A = genMatrix 4 6 then -1 else 1

theorem fam62real_sq : ∀ A ∈ fam62real, A * A = sq62real A • 1 := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam62realIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · have hne : genMatrix 4 0 ≠ genMatrix 4 7 := genMatrix_ne (by decide)
    simp [sq62real, genMatrix_sq, hne]
  · have hne : genMatrix 4 2 ≠ genMatrix 4 7 := genMatrix_ne (by decide)
    simp [sq62real, genMatrix_sq, hne]
  · have hne : genMatrix 4 4 ≠ genMatrix 4 7 := genMatrix_ne (by decide)
    simp [sq62real, genMatrix_sq, hne]
  · simp [sq62real, genMatrix_sq]

theorem fam62imag_sq : ∀ A ∈ fam62imag, A * A = sq62imag A • 1 := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam62imagIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · have hne : genMatrix 4 1 ≠ genMatrix 4 6 := genMatrix_ne (by decide)
    simp [sq62imag, genMatrix_sq, hne]
  · have hne : genMatrix 4 3 ≠ genMatrix 4 6 := genMatrix_ne (by decide)
    simp [sq62imag, genMatrix_sq, hne]
  · have hne : genMatrix 4 5 ≠ genMatrix 4 6 := genMatrix_ne (by decide)
    simp [sq62imag, genMatrix_sq, hne]
  · simp [sq62imag, genMatrix_sq]

theorem fam62real_conj :
    ∀ A ∈ fam62real, A.map (starRingEnd ℂ) = (fun _ => (1 : ℂ)) A • A := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam62realIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp [genMatrix_conj, genDelta, conjPhaseF_genString, Nat.even_iff]

theorem fam62imag_conj :
    ∀ A ∈ fam62imag, A.map (starRingEnd ℂ) = (fun _ => (-1 : ℂ)) A • A := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam62imagIdx, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp [genMatrix_conj, genDelta, conjPhaseF_genString, Nat.even_iff]

/-- **(6,2), real family:** `B * conj(B) = -1`, the quaternionic sign. -/
theorem fam62real_prod_conj :
    fam62real.prod * fam62real.prod.map (starRingEnd ℂ) = (-1 : ℂ) • 1 := by
  have h := GppWhichWayForwardFamilySigns.prod_mul_map_starRingEnd_prod
    (sq := sq62real) (δ := fun _ => (1 : ℂ)) fam62real fam62real_nodup
    fam62real_pairwise fam62real_sq fam62real_conj
  rw [h]
  have hpairs : GppWhichWayForwardFamilySigns.pairs fam62real = 6 := by decide
  have hδprod : (fam62real.map (fun _ => (1 : ℂ))).prod = 1 := by
    simp [fam62real, fam62realIdx]
  have e0 : sq62real (genMatrix 4 0) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e2 : sq62real (genMatrix 4 2) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e4 : sq62real (genMatrix 4 4) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e7 : sq62real (genMatrix 4 7) = -1 := if_pos rfl
  have hsqprod : (fam62real.map sq62real).prod = -1 := by
    simp [fam62real, fam62realIdx, e0, e2, e4, e7]
  rw [hpairs, hδprod, hsqprod]
  norm_num

/-- **(6,2), imaginary family:** `B * conj(B) = -1`, the quaternionic
sign. -/
theorem fam62imag_prod_conj :
    fam62imag.prod * fam62imag.prod.map (starRingEnd ℂ) = (-1 : ℂ) • 1 := by
  have h := GppWhichWayForwardFamilySigns.prod_mul_map_starRingEnd_prod
    (sq := sq62imag) (δ := fun _ => (-1 : ℂ)) fam62imag fam62imag_nodup
    fam62imag_pairwise fam62imag_sq fam62imag_conj
  rw [h]
  have hpairs : GppWhichWayForwardFamilySigns.pairs fam62imag = 6 := by decide
  have hδprod : (fam62imag.map (fun _ => (-1 : ℂ))).prod = 1 := by
    simp [fam62imag, fam62imagIdx]
  have e1 : sq62imag (genMatrix 4 1) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e3 : sq62imag (genMatrix 4 3) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e5 : sq62imag (genMatrix 4 5) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e6 : sq62imag (genMatrix 4 6) = -1 := if_pos rfl
  have hsqprod : (fam62imag.map sq62imag).prod = -1 := by
    simp [fam62imag, fam62imagIdx, e1, e3, e5, e6]
  rw [hpairs, hδprod, hsqprod]
  norm_num

/-- The conjugation eigenvalue of every (6,2) generator, relative to
the real family: `+1` on the family, `-1` off it. -/
theorem genDelta62real (j : ℕ) (hj : j < 8) :
    genDelta 4 j = if j ∈ fam62realIdx then 1 else -1 := by
  rw [genDelta, conjPhaseF_genString 4 j (by omega)]
  interval_cases j <;> simp [fam62realIdx, Nat.even_iff]

/-- The conjugation eigenvalue of every (6,2) generator, relative to
the imaginary family: `-1` on the family, `+1` off it. -/
theorem genDelta62imag (j : ℕ) (hj : j < 8) :
    genDelta 4 j = if j ∈ fam62imagIdx then -1 else 1 := by
  rw [genDelta, conjPhaseF_genString 4 j (by omega)]
  interval_cases j <;> simp [fam62imagIdx, Nat.even_iff]

/-- **(6,2) intertwining, real family:** one uniform sign `-1` for
every generator. -/
theorem fam62real_intertwining (j : ℕ) (hj : j < 8) :
    fam62real.prod * (genMatrix 4 j).map (starRingEnd ℂ)
      = (-1 : ℂ) • (genMatrix 4 j * fam62real.prod) := by
  rw [show fam62real = List.map (genMatrix 4) fam62realIdx from rfl,
    genMatrix_conj, genDelta62real j hj, Matrix.mul_smul]
  by_cases hmem : j ∈ fam62realIdx
  · rw [if_pos hmem]
    have key := prod_mul_of_mem
      (List.mem_map_of_mem hmem) fam62real_nodup fam62real_pairwise
    have hlen : (List.map (genMatrix 4) fam62realIdx).length = 4 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num
  · rw [if_neg hmem]
    have hanti_out : ∀ A ∈ fam62real,
        genMatrix 4 j * A = -(A * genMatrix 4 j) := by
      intro A hA
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
      simp only [fam62realIdx, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at ha
      interval_cases j <;>
        first
          | exact (hmem (by decide)).elim
          | (rcases ha with rfl | rfl | rfl | rfl <;>
              exact genMatrix_anticommute_of_odd (by decide))
    have key := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes
      fam62real hanti_out
    simp only [fam62real] at key
    have hlen : (List.map (genMatrix 4) fam62realIdx).length = 4 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num

/-- **(6,2) intertwining, imaginary family:** one uniform sign `+1`
for every generator. -/
theorem fam62imag_intertwining (j : ℕ) (hj : j < 8) :
    fam62imag.prod * (genMatrix 4 j).map (starRingEnd ℂ)
      = (1 : ℂ) • (genMatrix 4 j * fam62imag.prod) := by
  rw [show fam62imag = List.map (genMatrix 4) fam62imagIdx from rfl,
    genMatrix_conj, genDelta62imag j hj, Matrix.mul_smul]
  by_cases hmem : j ∈ fam62imagIdx
  · rw [if_pos hmem]
    have key := prod_mul_of_mem
      (List.mem_map_of_mem hmem) fam62imag_nodup fam62imag_pairwise
    have hlen : (List.map (genMatrix 4) fam62imagIdx).length = 4 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num
  · rw [if_neg hmem]
    have hanti_out : ∀ A ∈ fam62imag,
        genMatrix 4 j * A = -(A * genMatrix 4 j) := by
      intro A hA
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
      simp only [fam62imagIdx, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at ha
      interval_cases j <;>
        first
          | exact (hmem (by decide)).elim
          | (rcases ha with rfl | rfl | rfl | rfl <;>
              exact genMatrix_anticommute_of_odd (by decide))
    have key := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes
      fam62imag hanti_out
    simp only [fam62imag] at key
    have hlen : (List.map (genMatrix 4) fam62imagIdx).length = 4 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num

/-! ## The (10,2) families -/

/-- Generator indices of the real family at (10,2). -/
def fam102realIdx : List ℕ := [0, 2, 4, 6, 8, 11]

/-- Generator indices of the imaginary family at (10,2). -/
def fam102imagIdx : List ℕ := [1, 3, 5, 7, 9, 10]

/-- The real family at (10,2), as matrices. -/
def fam102real : List (Matrix (idx 6) (idx 6) ℂ) := fam102realIdx.map (genMatrix 6)

/-- The imaginary family at (10,2), as matrices. -/
def fam102imag : List (Matrix (idx 6) (idx 6) ℂ) := fam102imagIdx.map (genMatrix 6)

theorem fam102real_pairwise :
    ∀ A ∈ fam102real, ∀ B ∈ fam102real, A ≠ B → A * B = -(B * A) := by
  intro A hA B hB hne
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  simp only [fam102realIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact genMatrix_anticommute_of_odd (by decide)

theorem fam102imag_pairwise :
    ∀ A ∈ fam102imag, ∀ B ∈ fam102imag, A ≠ B → A * B = -(B * A) := by
  intro A hA B hB hne
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  simp only [fam102imagIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne) <;>
    exact genMatrix_anticommute_of_odd (by decide)

theorem fam102real_nodup : fam102real.Nodup := by
  apply List.Nodup.map_on _ (by decide : fam102realIdx.Nodup)
  intro x hx y hy hxy
  simp only [fam102realIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try rfl) <;> exact absurd hxy (genMatrix_ne (by decide))

theorem fam102imag_nodup : fam102imag.Nodup := by
  apply List.Nodup.map_on _ (by decide : fam102imagIdx.Nodup)
  intro x hx y hy hxy
  simp only [fam102imagIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try rfl) <;> exact absurd hxy (genMatrix_ne (by decide))

/-- The square function for the (10,2) real family: `-1` at the scaled
member `11`, `+1` elsewhere. -/
noncomputable def sq102real : Matrix (idx 6) (idx 6) ℂ → ℂ :=
  fun A => if A = genMatrix 6 11 then -1 else 1

/-- The square function for the (10,2) imaginary family: `-1` at the
scaled member `10`, `+1` elsewhere. -/
noncomputable def sq102imag : Matrix (idx 6) (idx 6) ℂ → ℂ :=
  fun A => if A = genMatrix 6 10 then -1 else 1

theorem fam102real_sq : ∀ A ∈ fam102real, A * A = sq102real A • 1 := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam102realIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · have hne : genMatrix 6 0 ≠ genMatrix 6 11 := genMatrix_ne (by decide)
    simp [sq102real, genMatrix_sq, hne]
  · have hne : genMatrix 6 2 ≠ genMatrix 6 11 := genMatrix_ne (by decide)
    simp [sq102real, genMatrix_sq, hne]
  · have hne : genMatrix 6 4 ≠ genMatrix 6 11 := genMatrix_ne (by decide)
    simp [sq102real, genMatrix_sq, hne]
  · have hne : genMatrix 6 6 ≠ genMatrix 6 11 := genMatrix_ne (by decide)
    simp [sq102real, genMatrix_sq, hne]
  · have hne : genMatrix 6 8 ≠ genMatrix 6 11 := genMatrix_ne (by decide)
    simp [sq102real, genMatrix_sq, hne]
  · simp [sq102real, genMatrix_sq]

theorem fam102imag_sq : ∀ A ∈ fam102imag, A * A = sq102imag A • 1 := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam102imagIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · have hne : genMatrix 6 1 ≠ genMatrix 6 10 := genMatrix_ne (by decide)
    simp [sq102imag, genMatrix_sq, hne]
  · have hne : genMatrix 6 3 ≠ genMatrix 6 10 := genMatrix_ne (by decide)
    simp [sq102imag, genMatrix_sq, hne]
  · have hne : genMatrix 6 5 ≠ genMatrix 6 10 := genMatrix_ne (by decide)
    simp [sq102imag, genMatrix_sq, hne]
  · have hne : genMatrix 6 7 ≠ genMatrix 6 10 := genMatrix_ne (by decide)
    simp [sq102imag, genMatrix_sq, hne]
  · have hne : genMatrix 6 9 ≠ genMatrix 6 10 := genMatrix_ne (by decide)
    simp [sq102imag, genMatrix_sq, hne]
  · simp [sq102imag, genMatrix_sq]

theorem fam102real_conj :
    ∀ A ∈ fam102real, A.map (starRingEnd ℂ) = (fun _ => (1 : ℂ)) A • A := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam102realIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [genMatrix_conj, genDelta, conjPhaseF_genString, Nat.even_iff]

theorem fam102imag_conj :
    ∀ A ∈ fam102imag, A.map (starRingEnd ℂ) = (fun _ => (-1 : ℂ)) A • A := by
  intro A hA
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  simp only [fam102imagIdx, List.mem_cons, List.mem_singleton,
    List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [genMatrix_conj, genDelta, conjPhaseF_genString, Nat.even_iff]

/-- **(10,2), real family:** `B * conj(B) = +1`, the real sign. -/
theorem fam102real_prod_conj :
    fam102real.prod * fam102real.prod.map (starRingEnd ℂ) = (1 : ℂ) • 1 := by
  have h := GppWhichWayForwardFamilySigns.prod_mul_map_starRingEnd_prod
    (sq := sq102real) (δ := fun _ => (1 : ℂ)) fam102real fam102real_nodup
    fam102real_pairwise fam102real_sq fam102real_conj
  rw [h]
  have hpairs : GppWhichWayForwardFamilySigns.pairs fam102real = 15 := by decide
  have hδprod : (fam102real.map (fun _ => (1 : ℂ))).prod = 1 := by
    simp [fam102real, fam102realIdx]
  have e0 : sq102real (genMatrix 6 0) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e2 : sq102real (genMatrix 6 2) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e4 : sq102real (genMatrix 6 4) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e6 : sq102real (genMatrix 6 6) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e8 : sq102real (genMatrix 6 8) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e11 : sq102real (genMatrix 6 11) = -1 := if_pos rfl
  have hsqprod : (fam102real.map sq102real).prod = -1 := by
    simp [fam102real, fam102realIdx, e0, e2, e4, e6, e8, e11]
  rw [hpairs, hδprod, hsqprod]
  norm_num

/-- **(10,2), imaginary family:** `B * conj(B) = +1`, the real sign. -/
theorem fam102imag_prod_conj :
    fam102imag.prod * fam102imag.prod.map (starRingEnd ℂ) = (1 : ℂ) • 1 := by
  have h := GppWhichWayForwardFamilySigns.prod_mul_map_starRingEnd_prod
    (sq := sq102imag) (δ := fun _ => (-1 : ℂ)) fam102imag fam102imag_nodup
    fam102imag_pairwise fam102imag_sq fam102imag_conj
  rw [h]
  have hpairs : GppWhichWayForwardFamilySigns.pairs fam102imag = 15 := by decide
  have hδprod : (fam102imag.map (fun _ => (-1 : ℂ))).prod = 1 := by
    simp [fam102imag, fam102imagIdx]
  have e1 : sq102imag (genMatrix 6 1) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e3 : sq102imag (genMatrix 6 3) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e5 : sq102imag (genMatrix 6 5) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e7 : sq102imag (genMatrix 6 7) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e9 : sq102imag (genMatrix 6 9) = 1 :=
    if_neg (genMatrix_ne (by decide))
  have e10 : sq102imag (genMatrix 6 10) = -1 := if_pos rfl
  have hsqprod : (fam102imag.map sq102imag).prod = -1 := by
    simp [fam102imag, fam102imagIdx, e1, e3, e5, e7, e9, e10]
  rw [hpairs, hδprod, hsqprod]
  norm_num

/-- The conjugation eigenvalue of every (10,2) generator, relative to
the real family: `+1` on the family, `-1` off it. -/
theorem genDelta102real (j : ℕ) (hj : j < 12) :
    genDelta 6 j = if j ∈ fam102realIdx then 1 else -1 := by
  rw [genDelta, conjPhaseF_genString 6 j (by omega)]
  interval_cases j <;> simp [fam102realIdx, Nat.even_iff]

/-- The conjugation eigenvalue of every (10,2) generator, relative to
the imaginary family: `-1` on the family, `+1` off it. -/
theorem genDelta102imag (j : ℕ) (hj : j < 12) :
    genDelta 6 j = if j ∈ fam102imagIdx then -1 else 1 := by
  rw [genDelta, conjPhaseF_genString 6 j (by omega)]
  interval_cases j <;> simp [fam102imagIdx, Nat.even_iff]

/-- **(10,2) intertwining, real family:** one uniform sign `-1` for
every generator. -/
theorem fam102real_intertwining (j : ℕ) (hj : j < 12) :
    fam102real.prod * (genMatrix 6 j).map (starRingEnd ℂ)
      = (-1 : ℂ) • (genMatrix 6 j * fam102real.prod) := by
  rw [show fam102real = List.map (genMatrix 6) fam102realIdx from rfl,
    genMatrix_conj, genDelta102real j hj, Matrix.mul_smul]
  by_cases hmem : j ∈ fam102realIdx
  · rw [if_pos hmem]
    have key := prod_mul_of_mem
      (List.mem_map_of_mem hmem) fam102real_nodup fam102real_pairwise
    have hlen : (List.map (genMatrix 6) fam102realIdx).length = 6 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num
  · rw [if_neg hmem]
    have hanti_out : ∀ A ∈ fam102real,
        genMatrix 6 j * A = -(A * genMatrix 6 j) := by
      intro A hA
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
      simp only [fam102realIdx, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at ha
      interval_cases j <;>
        first
          | exact (hmem (by decide)).elim
          | (rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
              exact genMatrix_anticommute_of_odd (by decide))
    have key := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes
      fam102real hanti_out
    simp only [fam102real] at key
    have hlen : (List.map (genMatrix 6) fam102realIdx).length = 6 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num

/-- **(10,2) intertwining, imaginary family:** one uniform sign `+1`
for every generator. -/
theorem fam102imag_intertwining (j : ℕ) (hj : j < 12) :
    fam102imag.prod * (genMatrix 6 j).map (starRingEnd ℂ)
      = (1 : ℂ) • (genMatrix 6 j * fam102imag.prod) := by
  rw [show fam102imag = List.map (genMatrix 6) fam102imagIdx from rfl,
    genMatrix_conj, genDelta102imag j hj, Matrix.mul_smul]
  by_cases hmem : j ∈ fam102imagIdx
  · rw [if_pos hmem]
    have key := prod_mul_of_mem
      (List.mem_map_of_mem hmem) fam102imag_nodup fam102imag_pairwise
    have hlen : (List.map (genMatrix 6) fam102imagIdx).length = 6 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num
  · rw [if_neg hmem]
    have hanti_out : ∀ A ∈ fam102imag,
        genMatrix 6 j * A = -(A * genMatrix 6 j) := by
      intro A hA
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
      simp only [fam102imagIdx, List.mem_cons, List.mem_singleton,
        List.mem_nil_iff, or_false] at ha
      interval_cases j <;>
        first
          | exact (hmem (by decide)).elim
          | (rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
              exact genMatrix_anticommute_of_odd (by decide))
    have key := GppWhichWayForwardFamilySigns.prod_mul_of_anticommutes
      fam102imag hanti_out
    simp only [fam102imag] at key
    have hlen : (List.map (genMatrix 6) fam102imagIdx).length = 6 := by decide
    rw [hlen] at key
    rw [key, smul_smul]
    congr 1
    norm_num

end GppWhichWayForwardParentFamilies
