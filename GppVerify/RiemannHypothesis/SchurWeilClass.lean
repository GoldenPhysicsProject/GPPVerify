import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import GppVerify.RiemannHypothesis.CauchyKernelPositive

/-!
# Schur product for the Weil class: positive-type times convolution square

Thread S2 (the composition step of the S-truncated transport programme). The classical
Schur product theorem says the pointwise product of two positive-type functions is
positive-type; its general proof needs a Gram/square-root factorization of an abstract
PSD matrix. **For the Weil test class that generality is never needed**: the second
factor is always a convolution square `Q(x) = INT f(y) f(y-x) dy`, which carries an
explicit Gram representation — its Gram vectors are the translates `f(. + x_i)` — so the
product theorem follows from the same sum-integral interchange as
`convolution_square_positive_type` (Thread B), with the abstract positive-type factor
`P` riding along as a weight. No spectral theorem, no matrix square roots, no new
axioms.

* `positiveType_weighted_gram` — the weighting lemma: a positive-type `P` stays
  nonnegative against Gram weights `d_i d_j` (absorb the real weights into the complex
  test vector);
* **`positiveType_mul_convSquare`** — Schur for the Weil class: `P` positive-type and
  `f` integrable and bounded imply `x |-> P x * INT f(y) f(y-x) dy` is positive-type;
* `cauchyKernel_mul_convSquare_positive_type` — the epsilon-regularized Weil-class
  datum: the Cauchy kernel (Thread K) times any convolution square is positive-type —
  the composed on-line object of Yakaboylu eq. (75) in kernel-checked form.

**Why this matters for transport (memo section 6.1).** Composing positivity data is the
product step of the S-truncated class-group transport: adjoining a factor to
`R x (product over p in S)` multiplies the corresponding positive-type data. With the
hom-pullback seed (`positiveType_comp_addMonoidHom`, Thread Q) this gives the two
closure operations — pull back, multiply — needed to assemble rung-N positivity
structures from factor data, with no idele-class-group formalization required.

**Honest boundary**: nothing here is uniform in the support/rung parameter; by
`rh_iff_weil_pairedForm_nonneg` the uniform statement is equivalent to RH and stays
open and named. This file only builds composition machinery, unconditionally.
-/

namespace GppHaarPositivityWeil

open MeasureTheory Finset

/-- **Positive-type survives Gram weighting**: for positive-type `P`, real weights
    `d_i d_j` on the Gram matrix keep the form nonnegative — absorb the weights into
    the complex test vector `c_i * d_i` and expand. -/
theorem positiveType_weighted_gram {P : ℝ → ℝ} (hP : PositiveType P)
    {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (d : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((starRingEnd ℂ) (c i) * c j).re * P (x i - x j) * (d i * d j) := by
  -- `PositiveType` now asserts nonnegativity in `ℂ`; take its real component,
  -- which is exactly the quantity this Gram-weighting statement is about.
  have h : (0 : ℝ) ≤ (∑ i : Fin n, ∑ j : Fin n,
      (starRingEnd ℂ) (c i * ((d i : ℝ) : ℂ)) * (c j * ((d j : ℝ) : ℂ)) *
        ((P (x i - x j) : ℝ) : ℂ)).re := by
    have := (RCLike.nonneg_iff.mp (hP n x (fun i => c i * ((d i : ℝ) : ℂ)))).1
    simpa using this
  refine h.trans_eq ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((starRingEnd ℂ) (c i * ((d i : ℝ) : ℂ)) * (c j * ((d j : ℝ) : ℂ)) *
      ((P (x i - x j) : ℝ) : ℂ)).re =
    ((starRingEnd ℂ) (c i) * c j).re * P (x i - x j) * (d i * d j)
  have hexpand : (starRingEnd ℂ) (c i * ((d i : ℝ) : ℂ)) * (c j * ((d j : ℝ) : ℂ)) *
      ((P (x i - x j) : ℝ) : ℂ) =
      ((starRingEnd ℂ) (c i) * c j) * ((P (x i - x j) * (d i * d j) : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [hexpand, mul_ofReal_re, ← mul_assoc]

/-- **Schur product for the Weil class**: the pointwise product of a positive-type
    function with a convolution square is positive-type, for integrable bounded `f`.
    The convolution square supplies its own Gram vectors (the translates `f(. + x_i)`),
    so the proof is the Thread B sum-integral interchange with `P` riding along as a
    Gram weight — no abstract PSD factorization needed. -/
theorem positiveType_mul_convSquare {P f : ℝ → ℝ} (hP : PositiveType P)
    (hf : Integrable f (volume : Measure ℝ)) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    PositiveType (fun x => P x * ∫ y, f y * f (y - x)) := by
  -- Evenness of the product now comes for free: `hP.even` gives it for `P` — a
  -- consequence the old `.re`-taking definition could not supply — and the
  -- convolution square is even by translation invariance.
  refine positiveType_of_even_of_re (fun t => ?_) (fun n x c => ?_)
  · have hc₁ := convolution_shift (f := f) (0 : ℝ) t
    have hc₂ := convolution_shift (f := f) t (0 : ℝ)
    simp only [zero_sub, sub_zero, add_zero] at hc₁ hc₂
    rw [hP.even t, hc₁, hc₂]
    exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall (fun y => mul_comm _ _)))
  -- Step 1: rewrite each matrix entry through the translation identity.
  have hentry : ∀ i j : Fin n,
      (((fun x => P x * ∫ y, f y * f (y - x)) (x i - x j) : ℝ) : ℂ) =
        ((P (x i - x j) * ∫ y, f (y + x i) * f (y + x j) : ℝ) : ℂ) := by
    intro i j
    norm_cast
    show P (x i - x j) * (∫ y, f y * f (y - (x i - x j))) =
      P (x i - x j) * ∫ y, f (y + x i) * f (y + x j)
    rw [convolution_shift]
  simp only [hentry]
  -- Step 2: push `.re` through the double sum and strip the real coercion.
  rw [Complex.re_sum]
  have hterm : ∀ i : Fin n,
      (∑ j : Fin n, (starRingEnd ℂ) (c i) * c j *
        ((P (x i - x j) * ∫ y, f (y + x i) * f (y + x j) : ℝ) : ℂ)).re =
      ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re * P (x i - x j) *
        ∫ y, f (y + x i) * f (y + x j) := by
    intro i
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_ofReal_re, ← mul_assoc]
  simp only [hterm]
  -- Step 3: interchange the finite double sum with the integral.
  have hint : ∀ i j : Fin n,
      Integrable (fun y => ((starRingEnd ℂ) (c i) * c j).re * P (x i - x j) *
        (f (y + x i) * f (y + x j))) (volume : Measure ℝ) :=
    fun i j => (integrable_shift_mul_shift hf hbdd (x i) (x j)).const_mul _
  have hswap : ∑ i : Fin n, ∑ j : Fin n, ((starRingEnd ℂ) (c i) * c j).re *
      P (x i - x j) * ∫ y, f (y + x i) * f (y + x j) =
      ∫ y, ∑ i : Fin n, ∑ j : Fin n,
        ((starRingEnd ℂ) (c i) * c j).re * P (x i - x j) *
          (f (y + x i) * f (y + x j)) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
      · exact fun j _ => hint i j
    · exact fun i _ => integrable_finset_sum _ fun j _ => hint i j
  rw [hswap]
  -- Step 4: pointwise, the integrand is a P-weighted Gram form, nonnegative by
  -- `positiveType_weighted_gram` with Gram vectors the translates of `f`.
  apply integral_nonneg
  intro y
  exact positiveType_weighted_gram hP x c (fun i => f (y + x i))

/-- **The epsilon-regularized Weil-class datum is positive-type**: the Cauchy kernel
    (positive-type by Thread K) times any convolution square (Thread B) — the composed
    on-line object of the Yakaboylu regularization, now closed under the product. -/
theorem cauchyKernel_mul_convSquare_positive_type {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f (volume : Measure ℝ)) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) :
    PositiveType (fun x => ε^2 / (ε^2 + x^2) * ∫ y, f y * f (y - x)) :=
  positiveType_mul_convSquare (GppCauchyKernel.cauchy_kernel_positive_type hε) hf hbdd

end GppHaarPositivityWeil

-- Summary checks
#check @GppHaarPositivityWeil.positiveType_weighted_gram
#check @GppHaarPositivityWeil.positiveType_mul_convSquare
#check @GppHaarPositivityWeil.cauchyKernel_mul_convSquare_positive_type
