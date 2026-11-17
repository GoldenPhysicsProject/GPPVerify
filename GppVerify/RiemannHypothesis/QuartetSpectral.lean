/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (GPPDiscovery3 seat), 2026-11-13.

# The spectral side of the semilocal defect form: finite core

For a finite configuration `(x, c)`, `x c : Fin n → ℝ`, set

  `tri u = max (1 - |u|) 0`,   `Fc x c u = ∑ i, c i * tri (u - x i)`,
  `Fhat x c s = ∫ u, Fc x c u * exp (-(s - 1/2) * u)`,

the Mellin–Laplace transform of the test function the configuration defines
(the triangle autocorrelation of `Fc` is the kernel `Kpsi` of `KreinHPsi`:
`triG = tri ⋆ tri`). The Guinand–Weil explicit formula for this test function
is the identity (C1): on `ker ℓ_c` (`∑ i, c i * cosh (x i / 2) = 0`),

  `kform Kpsi x c = ∑_ρ Fhat x c ρ * Fhat x c (1 - ρ)`,

the sum over the nontrivial zeros `ρ` of `ζ`, grouped in quartets
`{ρ, conj ρ, 1 - ρ, 1 - conj ρ}`.

Labels:
* `Fhat_conj` — PROVED: `Fhat x c (conj s) = conj (Fhat x c s)`, since `Fc` is
  real-valued.
* `quartetSum_online` — PROVED: for `ρ = 1/2 + iγ` on the line, the quartet
  contribution is the square `4 * normSq (Fhat x c ρ)`, hence nonnegative.
* `O2` — OPEN, stated only: (C1) as convergence of the finite partial sums
  `Sfin x c (Z k)` along any exhaustion `Z` of the nontrivial zeros.
* `O3` — OPEN, stated only: positivity of the total spectral sum on `ker ℓ_c`.

Convention: `quartetSum` sums over the quartet as a multiset with four slots
`{ρ, conj ρ, 1 - ρ, 1 - conj ρ}`; on the line the two distinct terms each equal
`normSq (Fhat x c ρ)` and the remaining slots repeat them, giving the factor
`4`. In `Sfin` each zero of the finset is counted once.
-/

import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Filter ComplexConjugate
open scoped Topology

namespace GppQuartetSpectral

open GppKreinBridge GppKreinHPsi

/-- The triangle `tri u = max (1 - |u|) 0`, supported on `[-1, 1]`
(the same function as `triPsi` in `KreinHPsi`). -/
noncomputable def tri (u : ℝ) : ℝ := max (1 - |u|) 0

/-- The test function of a finite configuration,
`Fc x c u = ∑ i, c i * tri (u - x i)`: real-valued, compactly supported,
Lipschitz. -/
noncomputable def Fc {n : ℕ} (x c : Fin n → ℝ) (u : ℝ) : ℝ :=
  ∑ i, c i * tri (u - x i)

/-- The Mellin–Laplace transform of `Fc`,
`Fhat x c s = ∫ u, Fc x c u * exp (-(s - 1/2) * u)`. The integral converges
absolutely for every `s`, since `Fc x c` has compact support. -/
noncomputable def Fhat {n : ℕ} (x c : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, (Fc x c u : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))

/-- Conjugation symmetry of `Fhat`, from `Fc` being real-valued:
`Fhat x c (conj s) = conj (Fhat x c s)`. -/
theorem Fhat_conj {n : ℕ} (x c : Fin n → ℝ) (s : ℂ) :
    Fhat x c (conj s) = conj (Fhat x c s) := by
  have hexp : ∀ u : ℝ, -(conj s - 1 / 2) * (u : ℂ) = conj (-(s - 1 / 2) * (u : ℂ)) := by
    intro u
    rw [Complex.ext_iff]
    simp [Complex.mul_re, Complex.mul_im]
  have hpoint : ∀ u : ℝ, (Fc x c u : ℂ) * Complex.exp (-(conj s - 1 / 2) * (u : ℂ))
      = conj ((Fc x c u : ℂ) * Complex.exp (-(s - 1 / 2) * (u : ℂ))) := by
    intro u
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hexp]
  unfold Fhat
  rw [← integral_conj]
  exact integral_congr_ae (ae_of_all _ hpoint)

/-- The quartet contribution of `ρ`, summed over the quartet as a multiset
`{ρ, conj ρ, 1 - ρ, 1 - conj ρ}` (four slots):
`quartetSum x c ρ = ∑_{s ∈ Q} Fhat x c s * Fhat x c (1 - s)`. -/
noncomputable def quartetSum {n : ℕ} (x c : Fin n → ℝ) (ρ : ℂ) : ℂ :=
  Fhat x c ρ * Fhat x c (1 - ρ)
    + Fhat x c (conj ρ) * Fhat x c (1 - conj ρ)
    + Fhat x c (1 - ρ) * Fhat x c ρ
    + Fhat x c (1 - conj ρ) * Fhat x c (conj ρ)

private lemma one_sub_online (γ : ℝ) :
    1 - ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))
      = conj ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) := by
  rw [Complex.ext_iff]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  constructor <;> norm_num [Complex.div_re, Complex.div_im]

private lemma quartetSum_eq {n : ℕ} (x c : Fin n → ℝ) {ρ : ℂ} (hρ : 1 - ρ = conj ρ) :
    quartetSum x c ρ = ((4 * Complex.normSq (Fhat x c ρ) : ℝ) : ℂ) := by
  have h2 : 1 - conj ρ = ρ := by rw [← hρ]; ring
  have hF : Fhat x c (conj ρ) = conj (Fhat x c ρ) := Fhat_conj x c ρ
  have e1 : Fhat x c ρ * conj (Fhat x c ρ) = ((Complex.normSq (Fhat x c ρ) : ℝ) : ℂ) :=
    Complex.mul_conj _
  have e2 : conj (Fhat x c ρ) * Fhat x c ρ = ((Complex.normSq (Fhat x c ρ) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj _
  unfold quartetSum
  rw [hρ, h2, hF, e1, e2]
  push_cast
  ring

/-- **On-line square identity** (PROVED): for `ρ = 1/2 + iγ` on the line
(`1 - ρ = conj ρ`), the quartet contribution is a square,
`quartetSum x c ρ = 4 * |Fhat x c ρ|²` with `|z|² = normSq z`. -/
theorem quartetSum_online (γ : ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    quartetSum x c ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))
      = ((4 * Complex.normSq (Fhat x c ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))) : ℝ) : ℂ) :=
  quartetSum_eq x c (one_sub_online γ)

/-- The on-line quartet contribution is a nonnegative real. -/
theorem quartetSum_online_nonneg (γ : ℝ) {n : ℕ} (x c : Fin n → ℝ) :
    0 ≤ (quartetSum x c ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))).re := by
  rw [quartetSum_online, Complex.ofReal_re]
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

/-- The finite partial spectral sum over an explicit finite set of zeros,
`Sfin x c Z = ∑ ρ ∈ Z, Fhat x c ρ * Fhat x c (1 - ρ)`. Each zero of `Z` is
counted once; if `Z` is quartet-closed, the sum is the sum of the quartet
contributions of its two-element (on the line) and four-element quartets. -/
noncomputable def Sfin {n : ℕ} (x c : Fin n → ℝ) (Z : Finset ℂ) : ℂ :=
  ∑ ρ ∈ Z, Fhat x c ρ * Fhat x c (1 - ρ)

/-- For a conjugation-closed finite set of zeros, the partial spectral sum
`Sfin x c Z` is real: conjugation permutes the summands (PROVED). -/
theorem conj_Sfin {n : ℕ} (x c : Fin n → ℝ) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, conj ρ ∈ Z) : conj (Sfin x c Z) = Sfin x c Z := by
  have hinj : Set.InjOn (conj : ℂ → ℂ) (Z : Set ℂ) :=
    fun a _ b _ h => by
      have h2 := congrArg conj h
      simpa only [Complex.conj_conj] using h2
  have himg : Z.image conj = Z := by
    apply Finset.Subset.antisymm
    · intro σ hσ
      rcases Finset.mem_image.mp hσ with ⟨ρ, hρ, rfl⟩
      exact hZ ρ hρ
    · intro σ hσ
      exact Finset.mem_image.mpr ⟨conj σ, hZ σ hσ, Complex.conj_conj σ⟩
  have hc : ∀ ρ : ℂ, conj (1 - ρ) = 1 - conj ρ := fun ρ => by
    rw [map_sub, map_one]
  have key : ∑ σ ∈ Z.image conj, Fhat x c σ * Fhat x c (1 - σ)
      = ∑ ρ ∈ Z, Fhat x c (conj ρ) * Fhat x c (1 - conj ρ) :=
    Finset.sum_image hinj
  rw [himg] at key
  unfold Sfin
  rw [map_sum, key]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [map_mul, ← Fhat_conj, ← Fhat_conj, hc]

/-- A nontrivial zero of `ζ`: a zero of `riemannZeta` in the open critical
strip. -/
def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- An exhaustion of the nontrivial zeros by finite sets. Members are genuine
nontrivial zeros; each `Z k` is closed under the quartet symmetries
`ρ ↦ conj ρ` and `ρ ↦ 1 - ρ`; the sets are nested; every nontrivial zero is
eventually included. The partial sums over the `Z k` are finite sums over
explicit finite sets — no summability framework is involved in stating
`O2`/`O3`. -/
structure ZeroExhaustion (Z : ℕ → Finset ℂ) : Prop where
  zero_mem : ∀ (k : ℕ) (ρ : ℂ), ρ ∈ Z k → IsNontrivialZero ρ
  quartet_closed : ∀ (k : ℕ) (ρ : ℂ), ρ ∈ Z k → conj ρ ∈ Z k ∧ (1 - ρ) ∈ Z k
  mono : Monotone Z
  exhausts : ∀ ρ : ℂ, IsNontrivialZero ρ → ∃ k : ℕ, ρ ∈ Z k

/-- **(O2) The C1 identity** — OPEN, stated only. On `ker ℓ_c`
(`∑ i, c i * cosh (x i / 2) = 0`), the finite partial spectral sums along any
exhaustion of the nontrivial zeros converge to the defect form
`kform Kpsi x c`. This is the Guinand–Weil explicit formula for the test
function `Fc`, with the pole, prime and archimedean terms of the formula
identified term by term with the three parts of `Kpsi`. -/
def O2 : Prop :=
  ∀ (Z : ℕ → Finset ℂ), ZeroExhaustion Z →
    ∀ (n : ℕ) (x c : Fin n → ℝ), (∑ i, c i * Real.cosh (x i / 2)) = 0 →
      Tendsto (fun k => Sfin x c (Z k)) atTop (𝓝 (kform Kpsi x c : ℂ))

/-- **(O3) Positivity of the total spectral sum** — OPEN, stated only. On
`ker ℓ_c`, the total spectral sum along any exhaustion is a nonnegative
real. By `O2` this is exactly the positivity of `kform Kpsi` on `ker ℓ_c`
(`HPsi` in `KreinHPsi`), transported to the spectral side. -/
def O3 : Prop :=
  ∀ (Z : ℕ → Finset ℂ), ZeroExhaustion Z →
    ∀ (n : ℕ) (x c : Fin n → ℝ), (∑ i, c i * Real.cosh (x i / 2)) = 0 →
      ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun k => Sfin x c (Z k)) atTop (𝓝 (L : ℂ))

end GppQuartetSpectral
