import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The twisted action on Schwartz-Bruhat functions of a matrix space

Let `k` be a non-archimedean local field, `a` and `b` finite index types, and `SB` the space of
locally constant compactly supported functions `Matrix b a k → ℂ`. The group
`GL_a(k) × GL_b(k)` acts on it through the Weil-representation type formula

  `(om μ g h Φ)(x) = μ(det g) μ(det h)⁻¹ |det g|^{|b|/2} |det h|^{-|a|/2} Φ(h⁻¹ x g)`,

where `μ : kˣ →* ℂˣ` is a character and `|·|` is the normalized absolute value of `k`, the
distributive Haar character of `kˣ` acting on `k`.

* `nabs k` is that absolute value on `kˣ`.
* `omCoeff μ g h` is the scalar prefactor; `omCoeff_mul` records its multiplicativity in
  `(g, h)` and `omCoeff_one` its value `1` at the identity.
* `om μ g h` is the action on functions; `om_mul` is the left-action law
  `om μ (g₁ g₂) (h₁ h₂) Φ = om μ g₁ h₁ (om μ g₂ h₂ Φ)` and `om_one` is `om μ 1 1 = id`.
* `SB` is the submodule of locally constant compactly supported functions; `om_mem_SB` shows
  `om μ g h` preserves it, and `omSB` is the restricted linear map.

The shape of the formula follows the local type II theta correspondence of GL_r × GL_n in the
literature on local theta lifts; this module restates it in its own authoring.
-/

open MeasureTheory

namespace GppLocalTheta

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [IsTopologicalRing k]

/-- The normalized absolute value of `k` on its units: the distributive Haar character of `kˣ`
acting on `k`. -/
noncomputable def nabs : kˣ →* NNReal := distribHaarChar k

variable {k} {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The scalar prefactor of the twisted action. -/
noncomputable def omCoeff (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
    (((nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) : NNReal) : ℝ) : ℂ) *
    (((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2) : NNReal) : ℝ) : ℂ)

theorem omCoeff_mul (μ : kˣ →* ℂˣ) (g₁ g₂ : Matrix.GeneralLinearGroup a k)
    (h₁ h₂ : Matrix.GeneralLinearGroup b k) :
    omCoeff μ (g₁ * g₂) (h₁ * h₂) = omCoeff μ g₁ h₁ * omCoeff μ g₂ h₂ := by
  unfold omCoeff
  simp only [map_mul, NNReal.mul_rpow, mul_inv, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
  ring

theorem omCoeff_one (μ : kˣ →* ℂˣ) :
    omCoeff μ (1 : Matrix.GeneralLinearGroup a k) (1 : Matrix.GeneralLinearGroup b k) = 1 := by
  unfold omCoeff
  simp

/-- The twisted action of `GL_a(k) × GL_b(k)` on functions on `Matrix b a k`. -/
noncomputable def om (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ :=
  fun x => omCoeff μ g h * Φ ((↑h⁻¹ : Matrix b b k) * x * (↑g : Matrix a a k))

/-- The action law: `om` is a left action of `GL_a(k) × GL_b(k)`. -/
theorem om_mul (μ : kˣ →* ℂˣ) (g₁ g₂ : Matrix.GeneralLinearGroup a k)
    (h₁ h₂ : Matrix.GeneralLinearGroup b k) (Φ : Matrix b a k → ℂ) :
    om μ (g₁ * g₂) (h₁ * h₂) Φ = om μ g₁ h₁ (om μ g₂ h₂ Φ) := by
  funext x
  simp only [om, omCoeff_mul, mul_inv_rev, Units.val_mul]
  rw [mul_assoc]
  congr 2
  simp only [Matrix.mul_assoc]

theorem om_one (μ : kˣ →* ℂˣ) (Φ : Matrix b a k → ℂ) :
    om μ (1 : Matrix.GeneralLinearGroup a k) (1 : Matrix.GeneralLinearGroup b k) Φ = Φ := by
  funext x
  simp [om, omCoeff_one]

/-- Schwartz-Bruhat functions on `Matrix b a k`: locally constant with compact support. -/
def SB (k : Type*) [Field k] [TopologicalSpace k] (b a : Type*) : Submodule ℂ (Matrix b a k → ℂ) where
  carrier := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}
  add_mem' := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨h1.add h3, h2.add h4⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ := fun ⟨h1, h2⟩ =>
    ⟨h1.comp (fun z : ℂ => c • z), h2.smul_left⟩

/-- The change of variable `x ↦ h⁻¹ x g` as a homeomorphism of `Matrix b a k`. -/
def matHomeo (g : Matrix.GeneralLinearGroup a k) (h : Matrix.GeneralLinearGroup b k) :
    Matrix b a k ≃ₜ Matrix b a k where
  toFun x := (↑h⁻¹ : Matrix b b k) * x * (↑g : Matrix a a k)
  invFun x := (↑h : Matrix b b k) * x * (↑g⁻¹ : Matrix a a k)
  left_inv x := by simp [Matrix.mul_assoc]
  right_inv x := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem om_mem_SB (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB k b a) :
    om μ g h Φ ∈ SB k b a := by
  obtain ⟨h1, h2⟩ := hΦ
  have hc : IsLocallyConstant (Φ ∘ matHomeo g h) := h1.comp_continuous (matHomeo g h).continuous
  have hs : HasCompactSupport (Φ ∘ matHomeo g h) := h2.comp_homeomorph (matHomeo g h)
  exact ⟨hc.comp (fun z : ℂ => omCoeff μ g h * z), hs.mul_left⟩

/-- The twisted action as a linear endomorphism of `SB`. -/
noncomputable def omSB (μ : kˣ →* ℂˣ) (g : Matrix.GeneralLinearGroup a k)
    (h : Matrix.GeneralLinearGroup b k) : SB k b a →ₗ[ℂ] SB k b a where
  toFun Φ := ⟨om μ g h Φ.1, om_mem_SB μ g h Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x; simp [om, mul_add]
  map_smul' c Φ := by
    apply Subtype.ext; funext x; simp [om]; ring

#print axioms omCoeff_mul
#print axioms omCoeff_one
#print axioms om_mul
#print axioms om_one
#print axioms om_mem_SB
#print axioms omSB

end GppLocalTheta
