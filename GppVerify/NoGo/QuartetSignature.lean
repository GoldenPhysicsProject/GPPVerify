import GppVerify.NoGo.QuartetThreeNodeUniversal

/-!
# Exact signature of a quartet's Pick kernel: two negative squares off the line, none on it

For the folded quartet of `GppNoGo.QuartetThreeNode` (`K(x,y) = 4 N(x,y)/(D(x)D(y))`), the numerator
`N` is a polynomial of degree ≤ 3 in each variable, so for real nodes `xᵢ` and weights `cᵢ`

  `∑ᵢⱼ cᵢcⱼ N(xᵢ,xⱼ) = Q(E₀,E₁,E₂,E₃)`,  `E_k = ∑ᵢ cᵢ xᵢᵏ`   (`sum_N_eq_Q`),

with the explicit quadratic form `Q = (h³+hw)E₀² + 2(h²+w)E₀E₂ + hE₂² + (h²−w)E₁² + 2hE₁E₃ + E₃²`.
`Q` splits into an even block (E₀,E₂) and an odd block (E₁,E₃).

* `Q_neg_plane`: if `h > 0`, `w > 0`, `Q` is **negative definite on a 2-plane**.
* `Q_pos_plane`: `Q` is **positive definite on a complementary 2-plane**.
  Hence `Q` has signature exactly `(2,2)` on `ℝ⁴` (Sylvester): an off-axis quartet contributes
  **exactly two** negative squares — one per off-line zero in the right (equivalently left) half of
  the critical strip, consistent with the Krein–Langer count.
* `onAxis_psd`: on the line (`δ = 0`, so `w = 0`, `f = 4x/(x²+h)`), the Pick form is
  `4[(∑ cᵢxᵢ/(xᵢ²+h))² + h(∑ cᵢ/(xᵢ²+h))²] ≥ 0` at every size: on-line zeros only add positivity.

**Correction recorded.** Earlier notes (CONVERSATION 2026-10-11, PR #283 text) said "each off-axis
quartet contributes exactly one negative square". That was wrong; it is two. Numerics (14 nodes,
three off-axis quartets) gave 2 negative / 2 positive eigenvalues; this file proves it.

**Hint (unchanged in substance).** RH ⇔ the total Pick kernel `∑_quartets K_q` has no negative
squares; on-line terms are PSD and off-line terms carry exactly two negative squares each, which on-line
mass might mask in finite tests. Showing it cannot is Weil positivity.
-/

namespace GppNoGo.QuartetSignature

open GppNoGo.QuartetThreeNode

/-- The quadratic form in the moment coordinates `E = (E₀,E₁,E₂,E₃)`. -/
def Q (h w E₀ E₁ E₂ E₃ : ℝ) : ℝ :=
  (h ^ 3 + h * w) * E₀ ^ 2 + 2 * (h ^ 2 + w) * E₀ * E₂ + h * E₂ ^ 2
    + (h ^ 2 - w) * E₁ ^ 2 + 2 * h * E₁ * E₃ + E₃ ^ 2

theorem prod_sums {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i) * (∑ j ∈ s, g j) = ∑ i ∈ s, ∑ j ∈ s, f i * g j := Finset.sum_mul_sum _ _ _ _

/-- `∑ᵢⱼ cᵢcⱼ N(xᵢ,xⱼ) = Q(E₀,…,E₃)` with `E_k = ∑ cᵢ xᵢᵏ`. -/
theorem sum_N_eq_Q {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (h w : ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * N h w (x i) (x j)
      = Q h w (∑ i ∈ s, c i) (∑ i ∈ s, c i * x i) (∑ i ∈ s, c i * x i ^ 2)
          (∑ i ∈ s, c i * x i ^ 3) := by
  set E₀ := ∑ i ∈ s, c i
  set E₁ := ∑ i ∈ s, c i * x i
  set E₂ := ∑ i ∈ s, c i * x i ^ 2
  set E₃ := ∑ i ∈ s, c i * x i ^ 3
  have hQ : Q h w E₀ E₁ E₂ E₃
      = (h ^ 3 + h * w) * (E₀ * E₀) + (h ^ 2 + w) * (E₀ * E₂ + E₂ * E₀) + h * (E₂ * E₂)
        + (h ^ 2 - w) * (E₁ * E₁) + h * (E₁ * E₃ + E₃ * E₁) + E₃ * E₃ := by
    unfold Q; ring
  rw [hQ]
  simp only [E₀, E₁, E₂, E₃]
  rw [prod_sums, prod_sums, prod_sums, prod_sums, prod_sums, prod_sums, prod_sums, prod_sums]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  unfold N
  ring

/-- Negative definite on the plane spanned by `e = (1, 0, −(h²+w)/h, 0)` and `o = (0, 1, 0, −h)`. -/
theorem Q_neg_plane {h w : ℝ} (hh : 0 < h) (hw : 0 < w) (α β : ℝ) (hαβ : α ≠ 0 ∨ β ≠ 0) :
    Q h w α β (-(h ^ 2 + w) / h * α) (-h * β) < 0 := by
  have he : Q h w α β (-(h ^ 2 + w) / h * α) (-h * β)
      = -((h ^ 2 * w + w ^ 2) / h * α ^ 2) - w * β ^ 2 := by
    unfold Q; field_simp; ring
  rw [he]
  have h1 : 0 < (h ^ 2 * w + w ^ 2) / h := by positivity
  rcases hαβ with hα | hβ
  · have h2 : 0 < (h ^ 2 * w + w ^ 2) / h * α ^ 2 := by positivity
    have : 0 ≤ w * β ^ 2 := by positivity
    linarith
  · have h2 : 0 < w * β ^ 2 := by positivity
    have : 0 ≤ (h ^ 2 * w + w ^ 2) / h * α ^ 2 := by positivity
    linarith

/-- Positive definite on the plane spanned by `(0,0,1,0)` and `(0,0,0,1)`. -/
theorem Q_pos_plane {h w : ℝ} (hh : 0 < h) (α β : ℝ) (hαβ : α ≠ 0 ∨ β ≠ 0) :
    0 < Q h w 0 0 α β := by
  unfold Q
  rcases hαβ with hα | hβ
  · have : 0 < α ^ 2 := by positivity
    nlinarith [sq_nonneg β]
  · have : 0 < β ^ 2 := by positivity
    nlinarith [sq_nonneg α]

/-- On the line (`w = 0`): the Pick form of `f = 4x/(x²+h)` is a sum of two squares. -/
theorem onAxis_psd {ι : Type*} (s : Finset ι) (c x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hx : ∀ i ∈ s, 0 < x i) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j *
      ((4 * x i / (x i ^ 2 + h) + 4 * x j / (x j ^ 2 + h)) / (x i + x j)) := by
  have key : ∀ i ∈ s, ∀ j ∈ s,
      (4 * x i / (x i ^ 2 + h) + 4 * x j / (x j ^ 2 + h)) / (x i + x j)
        = 4 * (x i / (x i ^ 2 + h) * (x j / (x j ^ 2 + h)) + h * (1 / (x i ^ 2 + h) * (1 / (x j ^ 2 + h)))) := by
    intro i hi j hj
    have h1 : x i ^ 2 + h ≠ 0 := by have := hx i hi; positivity
    have h2 : x j ^ 2 + h ≠ 0 := by have := hx j hj; positivity
    have h3 : x i + x j ≠ 0 := by have := hx i hi; have := hx j hj; positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => by rw [key i hi j hj]))]
  have : ∑ i ∈ s, ∑ j ∈ s, c i * c j * (4 * (x i / (x i ^ 2 + h) * (x j / (x j ^ 2 + h))
        + h * (1 / (x i ^ 2 + h) * (1 / (x j ^ 2 + h)))))
      = 4 * ((∑ i ∈ s, c i * (x i / (x i ^ 2 + h))) ^ 2 + h * (∑ i ∈ s, c i * (1 / (x i ^ 2 + h))) ^ 2) := by
    rw [pow_two, pow_two, prod_sums, prod_sums]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [this]
  positivity

end GppNoGo.QuartetSignature
