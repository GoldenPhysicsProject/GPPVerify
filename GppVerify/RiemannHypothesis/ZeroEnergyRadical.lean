import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# Zero-energy vectors and the radical of a symmetric bilinear form

Let `B` be a symmetric bilinear form on a real vector space `V`, and let `a, h : V` with
`B(a, a) = 0` and `B(a, h) ≠ 0`. Then:

* `not_forall_radical_of_pairing_ne_zero` (1): `a` is not in the radical of `B`.
* `gram2_eq` (2): the Gram determinant of `B` on `span {a, h}` is `-B(a, h)^2`, and it is negative
  (`gram2_neg`); `exists_indefinite_pair` gives vectors `x, y ∈ span {a, h}` with
  `B(x, x) = 1` and `B(y, y) = -1`, so the restriction is indefinite whatever `B(h, h)` is.
* `radical_of_posSemidef_of_zero_energy` (3), the contrapositive: if `B(x, x) ≥ 0` for every `x`,
  every vector `a` with `B(a, a) = 0` satisfies `B(a, y) = 0` for all `y`.

No analytic hypotheses are used.
-/

namespace GppZeroEnergy

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Gram determinant of `B` on the pair `a, h`. -/
def gram2 (B : LinearMap.BilinForm ℝ V) (a h : V) : ℝ :=
  B a a * B h h - B a h * B h a

/-- (1) A zero-energy vector with a nonzero pairing is not in the radical. -/
theorem not_forall_radical_of_pairing_ne_zero (B : LinearMap.BilinForm ℝ V) {a h : V}
    (hah : B a h ≠ 0) : ¬ ∀ y, B a y = 0 :=
  fun H => hah (H h)

/-- (2) The Gram determinant on `{a, h}` is `-B(a,h)^2` when `B(a,a) = 0`. -/
theorem gram2_eq (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {a h : V}
    (haa : B a a = 0) : gram2 B a h = -(B a h) ^ 2 := by
  unfold gram2
  rw [haa, hB h a]; ring

/-- (2) The Gram determinant is strictly negative when `B(a,h) ≠ 0`. -/
theorem gram2_neg (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {a h : V}
    (haa : B a a = 0) (hah : B a h ≠ 0) : gram2 B a h < 0 := by
  rw [gram2_eq B hB haa]
  have : 0 < (B a h) ^ 2 := by positivity
  linarith

/-- (2) The restriction of `B` to `span {a, h}` is indefinite, independently of `B(h, h)`. -/
theorem exists_indefinite_pair (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {a h : V} (haa : B a a = 0) (hah : B a h ≠ 0) :
    ∃ x ∈ Submodule.span ℝ {a, h}, ∃ y ∈ Submodule.span ℝ {a, h}, B x x = 1 ∧ B y y = -1 := by
  have key : ∀ t : ℝ, B (h + t • a) (h + t • a) = B h h + 2 * t * B a h := by
    intro t
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB h a, haa]; ring
  have hmem : ∀ t : ℝ, h + t • a ∈ Submodule.span ℝ {a, h} := fun t =>
    Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  refine ⟨h + ((1 - B h h) / (2 * B a h)) • a, hmem _, h + ((-1 - B h h) / (2 * B a h)) • a,
    hmem _, ?_, ?_⟩
  · rw [key]; field_simp; ring
  · rw [key]; field_simp; ring

/-- (3) If `B` is positive semidefinite, every zero-energy vector lies in the radical. -/
theorem radical_of_posSemidef_of_zero_energy (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hpsd : ∀ x, 0 ≤ B x x) {a : V} (haa : B a a = 0) :
    ∀ y, B a y = 0 := by
  intro y
  by_contra hne
  set c := B a y with hc
  set d := B y y with hd
  have hd0 : 0 ≤ d := hpsd y
  have hq : ∀ t : ℝ, B (a + t • y) (a + t • y) = 2 * t * c + t ^ 2 * d := by
    intro t
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hB y a, haa]; ring
  have h1 := hpsd (a + (-c / (d + 1)) • y)
  rw [hq] at h1
  have hd1 : 0 < d + 1 := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
    field_simp; ring
  rw [this] at h1
  have hneg : -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · positivity
  linarith

#print axioms not_forall_radical_of_pairing_ne_zero
#print axioms gram2_eq
#print axioms gram2_neg
#print axioms exists_indefinite_pair
#print axioms radical_of_posSemidef_of_zero_energy

end GppZeroEnergy
