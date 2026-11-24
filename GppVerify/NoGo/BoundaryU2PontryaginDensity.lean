import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The canonical U(2) boundary curvature has no degree-four density: `F ∧ F = 0` pointwise

Part (A) of the Discovery 2 note `boundary_color_instanton_obstruction_2026-11-14.md` (GPPDiscovery2,
`codex/discovery-workbench` 5a9deeb), audited by Turbo on the bridge (CONVERSATION.md, 2026-11-14).

On `U(2)`, the graph frame `V(U) = (I, U)ᵀ/√2` has tautological connection `A = θ/2`,
`θ = U⁻¹dU`, and curvature `F = dA + A ∧ A = -¼ θ ∧ θ` (Maurer–Cartan). At each point `θ` is a
linear map from the tangent space into `u(2)`, the skew-Hermitian `2 × 2` matrices.

**What is proved here**, for *every* real vector space `V` and *every* linear `θ : V → M₂(ℂ)` with
skew-Hermitian values (`θ x)ᴴ = -θ x`):

* `F θ x y := -¼ (θx θy - θy θx)`, i.e. `F = -¼ θ ∧ θ` evaluated on `(x, y)`;
* `curvWedge θ X := Σ_{σ ∈ S₄} sign σ · F(X_{σ0}, X_{σ1}) F(X_{σ2}, X_{σ3})`, the alternation of
  `F ⊗ F`, i.e. `F ∧ F` evaluated on `X₀, …, X₃` (up to the convention-dependent factor `1/4`);
* **`curvWedge_eq_zero`**: `curvWedge θ X = 0` for all `X`;
* **`curvature_ne_zero`**: the curvature itself is not zero — for `θ` the identity of `su(2)`, i.e.
  the Maurer–Cartan form at any point, `F(iσ₁, iσ₂) = ½ iσ₃ ≠ 0`.

The mechanism is the one in the note, made exact. The central part of `θ` drops out of every
commutator (`F θ = F θ₀`, `θ₀ = θ - (tr θ/2)·1`). `θ₀` takes values in `su(2)`, which has real
dimension `3` (`traceless_mem_range`). `curvWedge` is `¼` of the alternation of the 4-fold product of
`θ₀`-values (`curvWedge_eq`), and an alternating 4-linear map vanishes on four vectors of a
3-dimensional space (`alt4_eq_zero_of_mem`, via `AlternatingMap.map_linearDependent`).

 The note's part (B) (`c₂ = 0` for the pullback of `G₂ → S⁶`) needs Chern classes and
`H⁴(S⁶; ℤ) = 0`, which Mathlib does not have. No `sorry`, no axioms.
-/

namespace GppBoundaryU2

open Equiv Finset Matrix Complex

/-- `2 × 2` complex matrices, as a real algebra. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-! ### The alternation of a 4-fold product, and its vanishing on a small subspace -/

/-- `a₀ a₁ a₂ a₃`. -/
def prod4 (a : Fin 4 → M2) : M2 := a 0 * a 1 * a 2 * a 3

/-- `Σ_{σ ∈ S₄} sign σ · a_{σ0} a_{σ1} a_{σ2} a_{σ3}`. -/
def alt4 (a : Fin 4 → M2) : M2 := ∑ σ : Perm (Fin 4), ((Perm.sign σ : ℤ) • prod4 (a ∘ σ))

/-- The alternating map behind `alt4`. -/
noncomputable def Ω : M2 [⋀^Fin 4]→ₗ[ℝ] M2 :=
  MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℝ 4 M2)

theorem alt4_eq_Ω (a : Fin 4 → M2) : alt4 a = Ω a := by
  unfold alt4 Ω
  rw [MultilinearMap.alternatization_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply]
  simp [prod4, List.ofFn_succ, mul_assoc]

/-- **An alternating 4-form fed from a space of dimension `< 4` vanishes.** -/
theorem alt4_eq_zero_of_mem (S : Submodule ℝ M2) (hS : Module.finrank ℝ S < 4) (a : Fin 4 → M2)
    (ha : ∀ i, a i ∈ S) : alt4 a = 0 := by
  rw [alt4_eq_Ω]
  apply AlternatingMap.map_linearDependent
  intro hli
  have h1 := finrank_span_eq_card hli
  have hle : Submodule.span ℝ (Set.range a) ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ha i
  have h2 := Submodule.finrank_mono hle
  simp only [Fintype.card_fin] at h1
  omega

/-- Right-translating the permutation multiplies the alternation by the sign. -/
theorem sum_comp_mul (a : Fin 4 → M2) (τ : Perm (Fin 4)) :
    ∑ σ : Perm (Fin 4), ((Perm.sign σ : ℤ) • prod4 (a ∘ ⇑(σ * τ))) =
      (Perm.sign τ : ℤ) • alt4 a := by
  unfold alt4
  rw [← Equiv.sum_comp (Equiv.mulRight τ) (fun ρ => ((Perm.sign ρ : ℤ) • prod4 (a ∘ ρ))), smul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [Equiv.coe_mulRight, Perm.sign_mul, Units.val_mul, smul_smul]
  congr 1
  rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> rw [h] <;> simp

/-- `[c₀, c₁][c₂, c₃]` as four ordered products. -/
theorem comm_mul_comm (c : Fin 4 → M2) :
    (c 0 * c 1 - c 1 * c 0) * (c 2 * c 3 - c 3 * c 2) =
      prod4 c - prod4 (c ∘ ⇑(swap (2 : Fin 4) 3)) - prod4 (c ∘ ⇑(swap (0 : Fin 4) 1))
        + prod4 (c ∘ ⇑(swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3)) := by
  have h1 : prod4 (c ∘ ⇑(swap (2 : Fin 4) 3)) = c 0 * c 1 * c 3 * c 2 := by
    simp [prod4, swap_apply_of_ne_of_ne]
  have h2 : prod4 (c ∘ ⇑(swap (0 : Fin 4) 1)) = c 1 * c 0 * c 2 * c 3 := by
    simp [prod4, swap_apply_of_ne_of_ne]
  have h3 : prod4 (c ∘ ⇑(swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3)) = c 1 * c 0 * c 3 * c 2 := by
    simp [prod4, swap_apply_of_ne_of_ne]
  rw [h1, h2, h3, prod4]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-! ### The curvature and its wedge square -/

/-- `F = -¼ θ ∧ θ` on `(x, y)`. -/
noncomputable def F {V : Type*} (θ : V → M2) (x y : V) : M2 := (-(1 / 4 : ℝ)) • (θ x * θ y - θ y * θ x)

/-- `F ∧ F` on `(X₀, …, X₃)`: the alternation of `F ⊗ F`. -/
noncomputable def curvWedge {V : Type*} (θ : V → M2) (X : Fin 4 → V) : M2 :=
  ∑ σ : Perm (Fin 4), ((Perm.sign σ : ℤ) • (F θ (X (σ 0)) (X (σ 1)) * F θ (X (σ 2)) (X (σ 3))))

/-- The traceless part. -/
noncomputable def θ0 {V : Type*} (θ : V → M2) (x : V) : M2 := θ x - ((θ x).trace / 2) • (1 : M2)

/-- Scalars drop out of the commutator. -/
theorem F_eq_θ0 {V : Type*} (θ : V → M2) (x y : V) : F θ x y = F (θ0 θ) x y := by
  unfold F θ0
  congr 1
  set s := (θ x).trace / 2
  set t := (θ y).trace / 2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul,
    mul_comm s t]
  abel

theorem curvWedge_eq {V : Type*} (θ : V → M2) (X : Fin 4 → V) :
    curvWedge θ X = (1 / 4 : ℝ) • alt4 (θ0 θ ∘ X) := by
  set b := θ0 θ ∘ X
  have hterm : ∀ σ : Perm (Fin 4), F θ (X (σ 0)) (X (σ 1)) * F θ (X (σ 2)) (X (σ 3)) =
      (1 / 16 : ℝ) • (prod4 (b ∘ σ) - prod4 (b ∘ ⇑(σ * swap (2 : Fin 4) 3))
        - prod4 (b ∘ ⇑(σ * swap (0 : Fin 4) 1))
        + prod4 (b ∘ ⇑(σ * (swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3)))) := by
    intro σ
    rw [F_eq_θ0 θ, F_eq_θ0 θ]
    unfold F
    rw [smul_mul_smul_comm]
    have := comm_mul_comm (b ∘ σ)
    rw [show (b ∘ σ) ∘ ⇑(swap (2 : Fin 4) 3) = b ∘ ⇑(σ * swap (2 : Fin 4) 3) by rfl,
      show (b ∘ σ) ∘ ⇑(swap (0 : Fin 4) 1) = b ∘ ⇑(σ * swap (0 : Fin 4) 1) by rfl,
      show (b ∘ σ) ∘ ⇑(swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3) =
        b ∘ ⇑(σ * (swap (0 : Fin 4) 1 * swap (2 : Fin 4) 3)) by rfl] at this
    simp only [b, Function.comp_apply] at this
    rw [this]
    norm_num
    rfl
  unfold curvWedge
  simp_rw [hterm, smul_comm ((Perm.sign _ : ℤ)) ((1 / 16 : ℝ)), ← smul_sum, smul_add, smul_sub,
    sum_add_distrib, sum_sub_distrib]
  rw [sum_comp_mul, sum_comp_mul, sum_comp_mul]
  change (1 / 16 : ℝ) • (alt4 b - _ - _ + _) = _
  have h23 : Perm.sign (swap (2 : Fin 4) 3) = -1 := Perm.sign_swap (by decide)
  have h01 : Perm.sign (swap (0 : Fin 4) 1) = -1 := Perm.sign_swap (by decide)
  rw [Perm.sign_mul, h23, h01]
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, mul_neg, mul_one, neg_neg]
  rw [show alt4 b - -alt4 b - -alt4 b + alt4 b = (4 : ℝ) • alt4 b by
    rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num]; simp only [add_smul, one_smul]; abel]
  rw [smul_smul]; norm_num

/-! ### `su(2)` is three-dimensional -/

/-- `iσ₁, iσ₂, iσ₃`. -/
def E : Fin 3 → M2
  | 0 => !![0, I; I, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![I, 0; 0, -I]

/-- `w ↦ Σ_a w_a iσ_a`. -/
noncomputable def e : (Fin 3 → ℝ) →ₗ[ℝ] M2 :=
  ∑ a : Fin 3, (LinearMap.proj a : (Fin 3 → ℝ) →ₗ[ℝ] ℝ).smulRight (E a)

theorem e_apply (w : Fin 3 → ℝ) : e w = !![(w 2 : ℂ) * I, (w 0 : ℂ) * I + w 1;
    (w 0 : ℂ) * I - w 1, -((w 2 : ℂ) * I)] := by
  simp only [e, Fin.sum_univ_three, E]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul]; ring

/-- **The traceless part of a skew-Hermitian matrix lies in `su(2) = range e`.** -/
theorem traceless_mem_range (A : M2) (hA : Aᴴ = -A) :
    A - (A.trace / 2) • (1 : M2) ∈ LinearMap.range e := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  simp only [conjTranspose_apply, Matrix.neg_apply, RCLike.star_def] at h00 h11 h01
  have r00 : (A 0 0).re = 0 := by
    have := congrArg Complex.re h00; simp at this; linarith
  have r11 : (A 1 1).re = 0 := by
    have := congrArg Complex.re h11; simp at this; linarith
  have r10 : (A 1 0).re = -(A 0 1).re := by
    have := congrArg Complex.re h01; simp at this; linarith
  have i10 : (A 1 0).im = (A 0 1).im := by
    have := congrArg Complex.im h01; simp at this; linarith
  refine ⟨![(A 0 1).im, (A 0 1).re, ((A 0 0).im - (A 1 1).im) / 2], ?_⟩
  rw [e_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two] <;>
    apply Complex.ext <;> simp <;> linarith

theorem finrank_range_e_lt : Module.finrank ℝ (LinearMap.range e) < 4 := by
  have := LinearMap.finrank_range_le e
  simp only [Module.finrank_fin_fun] at this
  omega

/-! ### The theorem -/

/-- **`F ∧ F = 0` pointwise** for every `u(2)`-valued 1-form `θ` and `F = -¼ θ ∧ θ`. -/
theorem curvWedge_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (θ : V →ₗ[ℝ] M2)
    (hθ : ∀ x, (θ x)ᴴ = -θ x) (X : Fin 4 → V) : curvWedge θ X = 0 := by
  rw [curvWedge_eq, alt4_eq_zero_of_mem (LinearMap.range e) finrank_range_e_lt, smul_zero]
  intro i
  exact traceless_mem_range _ (hθ _)

theorem e_skew (w : Fin 3 → ℝ) : (e w)ᴴ = -e w := by
  rw [e_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply] <;> apply Complex.ext <;> simp

/-- **The curvature is not flat.** For `θ = e` (the Maurer–Cartan form at a point, in the basis
`iσ₁, iσ₂, iσ₃`), `F(iσ₁, iσ₂) = ½ iσ₃ ≠ 0`. -/
theorem curvature_ne_zero : F (fun w => e w) (Pi.single 0 1) (Pi.single 1 1) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  unfold F at h00
  simp only [e_apply] at h00
  simp at h00
  have := congrArg Complex.im h00
  norm_num at this

end GppBoundaryU2

#print axioms GppBoundaryU2.curvWedge_eq_zero
#print axioms GppBoundaryU2.curvature_ne_zero
