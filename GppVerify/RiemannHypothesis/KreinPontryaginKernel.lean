/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat), 2026-11-14, takeover shift for Claude Code's lane.

# The Pontryagin core at kernel level: every Toeplitz form of an even
# `κ ≤ 1` kernel splits off at most one negative square

Applies `GppKreinPontryaginFinite.pontryagin_finite` to the Gram (Toeplitz)
form of a kernel configuration. For an even kernel `K` (`K (-d) = K d`) and a
configuration `x : Fin n → ℝ`, the polarised Toeplitz form

  `kbilin K x c d = ∑ i, ∑ j, c i * d j * K (x i - x j)`

is a symmetric bilinear form in `(c, d)` whose diagonal is the tree's
`GppKreinBridge.kform K x`. If moreover `AtMostOneNegSq K` (the antecedent of
the named premise `KreinDecomp`, here a hypothesis — the antecedent itself is
OPEN), then every finite Toeplitz form of `K` is either positive
semidefinite, or splits along a negative configuration vector `c₀` as

  `kform K x c = kform K x (c - t • c₀) + t * kbilin K x c c₀`,
  `t = kbilin K x c c₀ / kform K x c₀`,

with the first term `≥ 0` for all `c` and the second a single negative square
(`t * kbilin K x c c₀ = kbilin K x c c₀ ^ 2 / kform K x c₀ ≤ 0`). This is the
finite-dimensional shadow of `KreinDecomp`'s conclusion shape — the negative
part of the kernel's form is carried by one explicit direction — proved here
at the level of finite configurations, which is where `AtMostOneNegSq` lives.

No `sorry`. The only hypothesis beyond evenness is `AtMostOneNegSq K` itself,
carried as a hypothesis, not discharged. Standard axioms only.
-/
import GppVerify.RiemannHypothesis.KreinPontryaginFinite

namespace GppKreinPontryaginKernel

open GppKreinBridge Finset

variable {n : ℕ}

/-- The polarised Toeplitz form of a kernel on a configuration:
`∑ i, ∑ j, c i * d j * K (x i - x j)`. Its diagonal is `kform K x`. -/
def kbilin (K : ℝ → ℝ) (x : Fin n → ℝ) (c d : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * d j * K (x i - x j)

theorem kbilin_diag (K : ℝ → ℝ) (x : Fin n → ℝ) (c : Fin n → ℝ) :
    kbilin K x c c = kform K x c := rfl

theorem kbilin_add_right (K : ℝ → ℝ) (x : Fin n → ℝ) (c d₁ d₂ : Fin n → ℝ) :
    kbilin K x c (d₁ + d₂) = kbilin K x c d₁ + kbilin K x c d₂ := by
  unfold kbilin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

theorem kbilin_smul_right (K : ℝ → ℝ) (x : Fin n → ℝ) (r : ℝ) (c d : Fin n → ℝ) :
    kbilin K x c (r • d) = r * kbilin K x c d := by
  unfold kbilin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem kbilin_add_left (K : ℝ → ℝ) (x : Fin n → ℝ) (c₁ c₂ d : Fin n → ℝ) :
    kbilin K x (c₁ + c₂) d = kbilin K x c₁ d + kbilin K x c₂ d := by
  unfold kbilin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

theorem kbilin_smul_left (K : ℝ → ℝ) (x : Fin n → ℝ) (r : ℝ) (c d : Fin n → ℝ) :
    kbilin K x (r • c) d = r * kbilin K x c d := by
  unfold kbilin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The Gram bilinear form of the configuration `x` for the kernel `K`. -/
def gramBilin (K : ℝ → ℝ) (x : Fin n → ℝ) : LinearMap.BilinForm ℝ (Fin n → ℝ) where
  toFun := fun c =>
    { toFun := fun d => kbilin K x c d
      map_add' := fun d₁ d₂ => kbilin_add_right K x c d₁ d₂
      map_smul' := fun r d => kbilin_smul_right K x r c d }
  map_add' := fun c₁ c₂ => LinearMap.ext fun d => kbilin_add_left K x c₁ c₂ d
  map_smul' := fun r c => LinearMap.ext fun d => kbilin_smul_left K x r c d

theorem gramBilin_apply (K : ℝ → ℝ) (x : Fin n → ℝ) (c d : Fin n → ℝ) :
    gramBilin K x c d = kbilin K x c d := rfl

theorem kbilin_symm {K : ℝ → ℝ} (hK : ∀ d, K (-d) = K d) (x : Fin n → ℝ)
    (c d : Fin n → ℝ) : kbilin K x c d = kbilin K x d c := by
  unfold kbilin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hKab : K (x a - x b) = K (x b - x a) := by
    have h := hK (x b - x a)
    rwa [show -(x b - x a) = x a - x b by ring] at h
  rw [hKab]
  ring

/-- **Kernel-level Pontryagin decomposition.** Let `K` be an even kernel with
`AtMostOneNegSq K`. For every configuration `x`, the Toeplitz form `kform K x`
is either positive semidefinite, or it splits along a negative configuration
vector `c₀` into a positive semidefinite part (on the projected vector
`c - (kbilin K x c c₀ / kform K x c₀) • c₀`) plus the single negative square
`(kbilin K x c c₀ / kform K x c₀) * kbilin K x c c₀`. -/
theorem kform_pontryagin {K : ℝ → ℝ} (hK : ∀ d, K (-d) = K d)
    (hK1 : AtMostOneNegSq K) (x : Fin n → ℝ) :
    (∀ c, 0 ≤ kform K x c) ∨
    ∃ c₀ : Fin n → ℝ, kform K x c₀ < 0 ∧ ∀ c,
      0 ≤ kform K x (c - (kbilin K x c c₀ / kform K x c₀) • c₀) ∧
      kform K x c = kform K x (c - (kbilin K x c c₀ / kform K x c₀) • c₀)
        + (kbilin K x c c₀ / kform K x c₀) * kbilin K x c c₀ := by
  have hNP : NoNegPlane (fun c => gramBilin K x c c) := by
    have h := hK1 n x
    have hfun : (fun c => gramBilin K x c c) = kform K x :=
      funext fun c => kbilin_diag K x c
    rw [hfun]
    exact h
  have hsymm : ∀ c d, gramBilin K x c d = gramBilin K x d c :=
    fun c d => kbilin_symm hK x c d
  rcases GppKreinPontryaginFinite.pontryagin_finite hsymm hNP with h | ⟨c₀, hc₀, hdec⟩
  · refine Or.inl fun c => ?_
    have := h c
    rwa [gramBilin_apply, kbilin_diag] at this
  · refine Or.inr ⟨c₀, ?_, fun c => ?_⟩
    · rwa [gramBilin_apply, kbilin_diag] at hc₀
    · obtain ⟨hnn, hid⟩ := hdec c
      constructor
      · rwa [gramBilin_apply, kbilin_diag] at hnn
      · have e1 : gramBilin K x c c₀ = kbilin K x c c₀ := rfl
        have e2 : gramBilin K x c₀ c₀ = kform K x c₀ := kbilin_diag K x c₀
        rw [e1, e2] at hid
        rwa [gramBilin_apply, kbilin_diag] at hid

end GppKreinPontryaginKernel
