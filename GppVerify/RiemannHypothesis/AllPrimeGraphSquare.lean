import GppVerify.RiemannHypothesis.FirstPrimeNegativeBound

/-!
# The graph-square identity: one completed square per prime translation

For a test function `f` and a shift `ℓ`, `∫ (f x − f (x − ℓ))² = 2 ‖f‖² − 2 A_f(ℓ)`, hence

`−2 v A_f(ℓ) = v ∫ (f x − f (x − ℓ))² − 2 v ‖f‖²`.

Summed over any finite family of weighted translations `(v_i, ℓ_i)` this reads

`Σ −2 v_i A_f(ℓ_i) = Σ v_i ∫ (f x − f (x − ℓ_i))² − 2 (Σ v_i) ‖f‖²`,

and the Dirichlet-type sum `Σ v_i ∫ (f x − f (x − ℓ_i))²` is `≥ 0` for `v_i ≥ 0`
(Turbo relay `b64da14`, GPT all-prime graph identity, §1).

**Scope.** This is the exact algebra of the completed square only — the full-line integral, one square
per translation.

No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection
open scoped ContDiff

noncomputable section

namespace GppGraphSquare

/-- **`∫ (f x − f (x − ℓ))² = 2 A_f(0) − 2 A_f(ℓ)`.** -/
theorem integral_shift_sq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ℓ : ℝ) :
    ∫ x, (f x - f (x - ℓ)) ^ 2 = 2 * autocorr f 0 - 2 * autocorr f ℓ := by
  have h1 := GppRungZeroPositivity.integrable_sq hf hc
  have h2 := GppRungZeroPositivity.integrable_sq_shift hf hc ℓ
  have h3 := GppRungZeroPositivity.integrable_mul_shift hf hc ℓ
  have htr : ∫ y, f (y - ℓ) ^ 2 = ∫ y, f y ^ 2 :=
    integral_sub_right_eq_self (fun y => f y ^ 2) ℓ
  have e : (fun x => (f x - f (x - ℓ)) ^ 2) =
      fun x => (f x ^ 2 + f (x - ℓ) ^ 2) - 2 * (f x * f (x - ℓ)) := by
    funext x; ring
  have h12 : Integrable fun x => f x ^ 2 + f (x - ℓ) ^ 2 := h1.add h2
  rw [e, integral_sub h12 (h3.const_mul 2), integral_add h1 h2, htr,
    integral_const_mul, GppRungZeroPositivity.autocorr_zero_eq]
  unfold autocorr
  ring

/-- **One completed square:** `−2 v A_f(ℓ) = v ∫ (f x − f (x − ℓ))² − 2 v ‖f‖²`. -/
theorem prime_term_square {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v ℓ : ℝ) :
    -2 * v * autocorr f ℓ = v * (∫ x, (f x - f (x - ℓ)) ^ 2) - 2 * v * autocorr f 0 := by
  have h := integral_shift_sq hf hc ℓ
  rw [h]; ring

/-- **Finite family of translations.** -/
theorem sum_prime_terms_square {ι : Type*} (s : Finset ι) (v ℓ : ι → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∑ i ∈ s, (-2 * v i * autocorr f (ℓ i)) =
      (∑ i ∈ s, v i * (∫ x, (f x - f (x - ℓ i)) ^ 2)) - 2 * (∑ i ∈ s, v i) * autocorr f 0 := by
  have : ∀ i ∈ s, -2 * v i * autocorr f (ℓ i) =
      v i * (∫ x, (f x - f (x - ℓ i)) ^ 2) - 2 * v i * autocorr f 0 :=
    fun i _ => prime_term_square hf hc (v i) (ℓ i)
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

/-- **The Dirichlet-type sum is nonnegative for nonnegative weights.** -/
theorem sum_dirichlet_nonneg {ι : Type*} (s : Finset ι) {v : ι → ℝ} (hv : ∀ i ∈ s, 0 ≤ v i)
    (ℓ : ι → ℝ) (f : ℝ → ℝ) :
    0 ≤ ∑ i ∈ s, v i * (∫ x, (f x - f (x - ℓ i)) ^ 2) :=
  Finset.sum_nonneg fun i hi =>
    mul_nonneg (hv i hi) (integral_nonneg fun _ => sq_nonneg _)

end GppGraphSquare

#print axioms GppGraphSquare.sum_prime_terms_square
#print axioms GppGraphSquare.sum_dirichlet_nonneg
