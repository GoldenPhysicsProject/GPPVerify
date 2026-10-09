import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# Peter–Weyl for finite abelian groups: Fourier expansion and Plancherel

Instance of the stub `open_peter_weyl_decomposition` (`HaarPositivityWeil.lean`) for a finite abelian
group `α`: the additive characters `AddChar α ℂ` are an orthonormal basis of `α → ℂ` for the
normalised inner product `⟪f,g⟫ = 𝔼_a conj(f a) g a` (the Haar-probability inner product on the finite
group), so

* `fourier_expansion`: `f = ∑_ψ ⟪ψ,f⟫ • ψ`;
* `plancherel`: `𝔼_a ‖f a‖² = ∑_ψ ‖⟪ψ,f⟫‖²`.

Both follow from Mathlib's `AddChar.complexBasis` and `AddChar.wInner_cWeight_eq_boole`.

## Scope

Finite abelian groups only. The general compact-group Peter–Weyl theorem (matrix coefficients of
irreducible unitary representations of a compact group, density in `C(G)`) is not in Mathlib and
is not proved here; the stub `open_peter_weyl_decomposition` records that statement.
-/

open scoped BigOperators ComplexConjugate

namespace GppFinitePeterWeyl

variable {α : Type*} [AddCommGroup α] [Fintype α]

open Finset in
/-- Orthonormality of characters for the Haar-probability inner product. -/
theorem orth (ψ φ : AddChar α ℂ) :
    𝔼 a, conj (ψ a) * φ a = if ψ = φ then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole (G := α) (R := ℂ) ψ φ
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simpa [RCLike.inner_apply, mul_comm] using h

open Finset in
/-- Fourier coefficient `f̂(ψ) = 𝔼_a conj(ψ a) · f a`. -/
noncomputable def coeff (f : α → ℂ) (ψ : AddChar α ℂ) : ℂ := 𝔼 a, conj (ψ a) * f a

open Finset in
/-- **Fourier expansion**: `f = ∑_ψ f̂(ψ) • ψ`. -/
theorem fourier_expansion (f : α → ℂ) : f = ∑ ψ : AddChar α ℂ, coeff f ψ • (ψ : α → ℂ) := by
  have h := (AddChar.complexBasis α).sum_repr f
  have hc : ∀ ψ : AddChar α ℂ, (AddChar.complexBasis α).repr f ψ = coeff f ψ := by
    intro ψ
    have e : ∀ a, f a = ∑ φ : AddChar α ℂ, (AddChar.complexBasis α).repr f φ * φ a := by
      intro a
      have := congr_fun h a
      simpa [AddChar.coe_complexBasis, Fintype.sum_apply] using this.symm
    unfold coeff
    symm
    calc 𝔼 a, conj (ψ a) * f a
        = 𝔼 a, ∑ φ : AddChar α ℂ, (AddChar.complexBasis α).repr f φ * (conj (ψ a) * φ a) := by
          refine Finset.expect_congr rfl (fun a _ => ?_)
          rw [e a, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun φ _ => by ring)
      _ = ∑ φ : AddChar α ℂ, (AddChar.complexBasis α).repr f φ * 𝔼 a, conj (ψ a) * φ a := by
          rw [Finset.expect_sum_comm]
          exact Finset.sum_congr rfl (fun φ _ => by rw [Finset.mul_expect])
      _ = (AddChar.complexBasis α).repr f ψ := by
          simp [orth]
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rw [hc ψ, AddChar.coe_complexBasis]

open Finset in
/-- **Plancherel**: `𝔼_a conj(f a) f a = ∑_ψ conj(f̂ ψ) f̂ ψ`, i.e. `𝔼‖f‖² = ∑‖f̂‖²`. -/
theorem plancherel (f : α → ℂ) :
    𝔼 a, conj (f a) * f a = ∑ ψ : AddChar α ℂ, conj (coeff f ψ) * coeff f ψ := by
  have e : ∀ a, f a = ∑ φ : AddChar α ℂ, coeff f φ * φ a := by
    intro a
    have := congr_fun (fourier_expansion f) a
    simpa [Fintype.sum_apply] using this
  have e' : ∀ a, conj (f a) = ∑ ψ : AddChar α ℂ, conj (coeff f ψ) * conj (ψ a) := by
    intro a
    conv_lhs => rw [e a]
    simp [map_sum]
  calc 𝔼 a, conj (f a) * f a
      = 𝔼 a, ∑ ψ : AddChar α ℂ, ∑ φ : AddChar α ℂ,
          conj (coeff f ψ) * coeff f φ * (conj (ψ a) * φ a) := by
        refine Finset.expect_congr rfl (fun a _ => ?_)
        rw [e' a]
        conv_lhs => rw [e a]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun φ _ => by ring)
    _ = ∑ ψ : AddChar α ℂ, ∑ φ : AddChar α ℂ,
          conj (coeff f ψ) * coeff f φ * 𝔼 a, conj (ψ a) * φ a := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        rw [Finset.expect_sum_comm]
        exact Finset.sum_congr rfl (fun φ _ => by rw [Finset.mul_expect])
    _ = ∑ ψ : AddChar α ℂ, conj (coeff f ψ) * coeff f ψ := by
        simp [orth]

end GppFinitePeterWeyl
