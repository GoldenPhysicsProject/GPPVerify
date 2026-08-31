import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The golden ratio as the minimal hyperbolic sector of `PSL₂(ℤ)`, and its finite-place echo

From a research-front update (2026-08-22) to "Local-field shadow kernels, celestial
unitarity, and the adelic principal series" (Toupin, 2026): the inversion `J : x ↦ x⁻¹`
composed with primitive unit translation `T : x ↦ x+1` gives `F = T∘J : x ↦ 1+1/x`, whose
unique positive fixed point is the golden ratio `φ`. Represented projectively by
`M = !![1,1;1,0] ∈ GL₂(ℤ)` (`det M = -1`), the square `A := M² = !![2,1;1,1] ∈ SL₂(ℤ)` is the
**minimal-trace hyperbolic element** of `SL₂(ℤ)` (`|tr A| ≥ 3` is forced by integrality once
`|tr A| > 2`, and `A` attains `|tr A| = 3`). Its discriminant is `5`, its eigenvalues are
`φ^{±2}`, and its Möbius fixed points are `φ` and `-φ⁻¹`. Independently, the finite-place
shadow kernel `K_{q,1}(s) = (1-q⁻¹)/[(1-q^{-s})(1-q^{-(1-s)})]` — already in this project's
scope, see `discovery/local_field_shadow/` — evaluated at the principal-series center
`s=1/2` and the discriminant `q=5` selected by the *independent* matrix computation above,
equals exactly `φ²`. This file formalizes the mathematical content of both routes and the
theorem connecting them.

**Semantic boundary, deliberately not formalized or claimed**: that this "minimal modular
hyperbolic sector" is the *physical* fundamental sector of anything in the surrounding
research program. That identification is open and physical, not mathematical, and no
theorem below asserts it. Likewise, no theorem claims inversion *alone* forces `φ` — the
precise, and only, claim is that inversion together with primitive translation, restricted
to its minimal orientation-preserving hyperbolic completion in `SL₂(ℤ)`, selects `φ^{±2}`
and discriminant `5`; and that the *independently defined* finite-place kernel at `q=5`,
`s=1/2` happens to equal the same real number `φ²`. Golden ratio infrastructure is reused
from Mathlib's `Data.Real.GoldenRatio` throughout (`Real.goldenRatio`, `Real.goldenRatio_sq`, `Real.goldenRatio_ne_zero`,
`Real.goldenConj_neg`, `Real.goldenRatio_add_goldenConj`, `Real.goldenRatio_mul_goldenConj`) rather than redefined.

**Missing-interface note**: the "characteristic polynomial" and "eigenvalue" statements
below (`A_charpoly_root_*`) are stated as direct root-of-`X²-tr·X+det` facts, not connected
to Mathlib's `Matrix.charpoly` / `Module.End.HasEigenvalue` API — no `charpoly_fin_two`-style
closed form for `2×2` matrices was found in the pinned Mathlib, and building that bridge is a
real but separate piece of work, not attempted here.
-/

namespace GppGoldenHyperbolic

open Real

/-! ## 1. The fixed point of inversion-then-translation is the golden ratio -/

/-- **The fixed-point characterization of `φ`**: for positive real `x`, `x = 1 + 1/x` iff
    `x = φ`. (`F = T∘J`, `F(x) = 1+1/x`; the unique positive fixed point is the golden
    ratio, the negative root `ψ` being excluded by positivity.) -/
theorem fixedPoint_iff_gold {x : ℝ} (hx : 0 < x) : x = 1 + 1 / x ↔ x = Real.goldenRatio := by
  constructor
  · intro h
    have hx' : x ≠ 0 := hx.ne'
    have heq : x ^ 2 - x - 1 = 0 := by
      have h' := h
      field_simp at h'
      nlinarith [h']
    have hfactor : (x - Real.goldenRatio) * (x - goldenConj) = 0 := by
      nlinarith [heq, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
    rcases mul_eq_zero.mp hfactor with h1 | h1
    · linarith [sub_eq_zero.mp h1]
    · exact absurd (sub_eq_zero.mp h1 ▸ hx) (not_lt.mpr Real.goldenConj_neg.le)
  · intro h
    rw [h]
    have h1 : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
    field_simp
    nlinarith [Real.goldenRatio_sq, Real.sq_sqrt (show (0:ℝ) ≤ 5 from by norm_num)]

/-! ## 2–3. The matrix identities -/

/-- The inversion/translation composite `F(x)=1+1/x`, represented projectively. -/
def M : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- `M² = A`, the minimal-trace hyperbolic element. -/
def A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

theorem M_sq_eq_A : M * M = A := by
  unfold M A
  rw [Matrix.mul_fin_two]
  norm_num

theorem det_M : M.det = -1 := by unfold M; rw [Matrix.det_fin_two_of]; norm_num

theorem det_A : A.det = 1 := by unfold A; rw [Matrix.det_fin_two_of]; norm_num

theorem trace_A : A.trace = 3 := by unfold A; rw [Matrix.trace_fin_two_of]; norm_num

/-! ## 4–5. The minimal-trace hyperbolic bound -/

/-- **Integrality forces the hyperbolic trace bound `|tr| ≥ 3`**: for any integer strictly
    greater than `2` in absolute value, that absolute value is at least `3`. Applied to a
    hyperbolic `SL₂(ℤ)` element (`|tr| > 2` is the hyperbolicity criterion), integrality of
    the trace forces `|tr| ≥ 3`. -/
theorem hyperbolic_trace_ge_three {n : ℤ} (h : 2 < |n|) : 3 ≤ |n| := by
  rcases le_or_gt 0 n with hn | hn
  · rw [abs_of_nonneg hn] at h ⊢; omega
  · rw [abs_of_neg hn] at h ⊢; omega

/-- **`A` attains the minimal hyperbolic trace**: `|tr A| = 3`, the lower bound from
    `hyperbolic_trace_ge_three`. -/
theorem A_trace_attains_min : |A.trace| = 3 := by rw [trace_A]; decide

/-! ## 6. The characteristic-polynomial roots `φ^{±2}` -/

/-- `φ²` is a root of `A`'s characteristic polynomial `X² - (tr A)·X + det A`. -/
theorem A_charpoly_root_goldSq :
    ((Real.goldenRatio : ℝ) ^ 2) ^ 2 - (A.trace : ℝ) * (Real.goldenRatio : ℝ) ^ 2 + (A.det : ℝ) = 0 := by
  rw [trace_A, det_A]
  push_cast
  nlinarith [Real.goldenRatio_sq]

/-- `φ⁻²` is the other root of `A`'s characteristic polynomial. -/
theorem A_charpoly_root_goldInvSq :
    ((Real.goldenRatio : ℝ)⁻¹ ^ 2) ^ 2 - (A.trace : ℝ) * (Real.goldenRatio : ℝ)⁻¹ ^ 2 + (A.det : ℝ) = 0 := by
  rw [trace_A, det_A]
  push_cast
  have hφ : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hinv : (Real.goldenRatio : ℝ)⁻¹ = Real.goldenRatio - 1 := by
    have h := Real.goldenRatio_sq
    field_simp
    nlinarith [h, Real.sq_sqrt (show (0:ℝ) ≤ 5 from by norm_num)]
  rw [hinv]
  nlinarith [Real.goldenRatio_sq]

/-! ## 7. The discriminant -/

/-- `A`'s discriminant `(tr A)² - 4·det A`. -/
def discrA : ℤ := A.trace ^ 2 - 4 * A.det

theorem discrA_eq_five : discrA = 5 := by unfold discrA; rw [trace_A, det_A]; decide

/-! ## 8. The projective (Möbius) fixed points of `A` -/

/-- **`A`'s Möbius fixed points are `φ` and `-φ⁻¹`**: for `x ≠ -1`, `(2x+1)/(x+1) = x` iff
    `x = φ` or `x = -φ⁻¹`. -/
theorem A_mobius_fixedPoints {x : ℝ} (hx : x + 1 ≠ 0) :
    (2 * x + 1) / (x + 1) = x ↔ x = Real.goldenRatio ∨ x = -Real.goldenRatio⁻¹ := by
  have hiff : (2 * x + 1) / (x + 1) = x ↔ x ^ 2 - x - 1 = 0 := by
    rw [div_eq_iff hx]
    constructor <;> intro h <;> nlinarith [h]
  rw [hiff]
  have hinv : -Real.goldenRatio⁻¹ = goldenConj := by
    rw [Real.inv_goldenRatio]; ring
  rw [hinv]
  constructor
  · intro heq
    have hfactor : (x - Real.goldenRatio) * (x - goldenConj) = 0 := by
      nlinarith [heq, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
    rcases mul_eq_zero.mp hfactor with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl)
    · nlinarith [Real.goldenRatio_sq]
    · nlinarith [Real.goldenRatio_sq, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]

/-! ## 9–10. The finite-place shadow kernel at the selected discriminant -/

/-- The finite-place shadow kernel `K_{q,1}(s) = (1-q⁻¹)/[(1-q^{-s})(1-q^{-(1-s)})]`
    (`discovery/local_field_shadow/`, §5), as a function of real `q > 1` and real `s`. No
    occurrence of `φ` appears in this definition, and `q` is a free parameter here — it is
    *not* selected to be `5` anywhere in this section. -/
noncomputable def finitePlaceKernel (q s : ℝ) : ℝ :=
  (1 - q⁻¹) / ((1 - q ^ (-s)) * (1 - q ^ (-(1 - s))))

/-- **The kernel at the principal-series center**: `K_{q,1}(1/2) = (√q+1)/(√q-1)`, for
    `q > 1`. -/
theorem finitePlaceKernel_half {q : ℝ} (hq : 1 < q) :
    finitePlaceKernel q (1 / 2) = (Real.sqrt q + 1) / (Real.sqrt q - 1) := by
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq
  set r := Real.sqrt q with hr_def
  have hr_sq : r ^ 2 = q := Real.sq_sqrt hq0.le
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hq0
  have hr_gt1 : 1 < r := by
    have h1 : Real.sqrt 1 < Real.sqrt q := Real.sqrt_lt_sqrt (by norm_num) hq
    simpa using h1
  have hrpow : q ^ (-(1 : ℝ) / 2) = r⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) from by ring, Real.rpow_neg hq0.le, hr_def,
      Real.sqrt_eq_rpow]
  unfold finitePlaceKernel
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, show -((1:ℝ)/2) = -(1:ℝ)/2 from by ring,
    hrpow]
  rw [← hr_sq]
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hr1_ne : r - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **The exact specialization at the independently-selected discriminant `q=5`**:
    `K_{5,1}(1/2) = φ²`. -/
theorem finitePlaceKernel_five_half : finitePlaceKernel 5 (1 / 2) = (Real.goldenRatio : ℝ) ^ 2 := by
  rw [finitePlaceKernel_half (by norm_num : (1:ℝ) < 5)]
  have h5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5gt1 : (1:ℝ) < Real.sqrt 5 := by
    have h1 : Real.sqrt 1 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h1
  have hden : Real.sqrt 5 - 1 ≠ 0 := by linarith
  unfold Real.goldenRatio
  field_simp
  nlinarith [h5sq]

/-! ## 11. The convergence theorem -/

/-- **The two independent routes converge**: the expanding eigenvalue of the minimal-trace
    hyperbolic element `A` (a root of `A`'s characteristic polynomial, `φ²`, from the matrix
    computation of §§2–7) and the finite-place shadow kernel at the discriminant `A` selects,
    evaluated at the principal-series center (`K_{discrA,1}(1/2)`, from the independent
    definition of §§9–10) are the same real number, `φ²`. -/
theorem golden_convergence :
    (Real.goldenRatio : ℝ) ^ 2 = finitePlaceKernel (discrA : ℝ) (1 / 2) := by
  rw [discrA_eq_five]
  norm_cast
  rw [finitePlaceKernel_five_half]

end GppGoldenHyperbolic
