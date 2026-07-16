import GppVerify.RiemannHypothesis.ConvolutionSquarePositive
import GppVerify.RiemannHypothesis.AbelCesaroRegularization
import Mathlib.Data.Complex.Trigonometric

/-!
# The off-line quartet: exact contribution, sign mechanism, and positivity transport

Thread Q of `docs/FORMALIZATION_PLAN.md`, from the entanglement/shadow-positivity memo
(§4.3, §3, and the transport question of §6.1). Three of the memo's checkable claims,
kernel-checked:

* **The quartet closed form** (`quartet_contribution`): for a Gaussian test pairing
  `h(r) = e^{−Cr²}`, a hypothetical off-line zero `ρ = 1/2 + δ + iγ` enters the explicit
  formula through its functional-equation quartet `{ρ, ρ̄, 1−ρ, 1−ρ̄}`, whose `r`-values
  are `{±γ ± iδ}`; the total contribution is **exactly**
  `4·e^{−C(γ²−δ²)}·cos(2Cγδ)` — a real number, computed here as an identity in `ℂ`
  (so the vanishing of the imaginary part is part of the theorem, not an assumption).
  On the line (`δ = 0`) the pair contributes `2·e^{−Cγ²}` (`pair_contribution`).
* **The sign mechanism** (`quartet_neg_of_cos_neg`, `cos_neg_of_quartet_neg`,
  `quartet_amplification`): the off-line contribution goes negative exactly when the
  oscillatory factor `cos(2Cγδ)` does — the sign flip lives in the cross-term, not in
  any diagonal shrinkage — and its magnitude carries the amplification factor
  `e^{+Cδ²} ≥ 1` over the on-line value. This is the memo's §4.3 mechanism
  ("the diagonal-entry Weil argument doesn't constrain cross-terms") as exact algebra.
* **Positivity transport, ℝ-factor seed** (`positiveType_comp_addMonoidHom`): a
  positive-type function pulled back along ANY additive group homomorphism is
  positive-type. This is the kernel-checked seed of the memo's §6.1 transport question:
  in log coordinates, positivity transports along the group homs of the factor
  decomposition. The idèle-class-group-level transport (between the Weil datum on
  `𝔸×/ℚ×` and the Cesàro datum on its `ℝ⁺` factor) remains open for the honest reason
  recorded since PR #45: idèle class groups are not in Mathlib.
* **The Cesàro datum is shadow-positive, Gram form** (`cesaro_gram_sq_nonneg`): the
  memo's §3 finding in the repo's finite-Gram idiom — the Abel-regularized Cesàro state
  is nonnegative on the square of any finite real linear combination, directly from the
  proved `abel_state_sq_nonneg` (PR #61).

What is NOT claimed: anything about `arithmetic_admissibility` (the AAC axiom of
`RHSpectralMultiplicity.lean`). The memo is explicit that none of its findings close it,
and neither does this file — these are the memo's checkable fragments, checked.
-/

namespace GppQuartet

open Complex

/-! ## Q1: the quartet closed form -/

/-- The square `(γ + δi)² = (γ² − δ²) + (2γδ)i`, in coordinates. -/
theorem sq_coords (γ δ : ℝ) :
    ((γ:ℂ) + (δ:ℂ)*Complex.I)^2 =
      ((γ^2 - δ^2 : ℝ) : ℂ) + ((2*γ*δ : ℝ) : ℂ)*Complex.I := by
  have h : ((γ:ℂ) + (δ:ℂ)*Complex.I)^2 =
      (γ:ℂ)^2 + 2*(γ:ℂ)*(δ:ℂ)*Complex.I + (δ:ℂ)^2*Complex.I^2 := by ring
  rw [h, Complex.I_sq]
  push_cast
  ring

/-- **The off-line quartet contribution, exactly** (memo §4.3): for the Gaussian pairing
    `h(r) = e^{−Cr²}`, the functional-equation quartet of `ρ = 1/2 + δ + iγ` — with
    `r`-values `{γ+iδ, γ−iδ, −γ+iδ, −γ−iδ}` — contributes
    `4·e^{−C(γ²−δ²)}·cos(2Cγδ)`, as an identity in `ℂ` (imaginary part zero included). -/
theorem quartet_contribution (C γ δ : ℝ) :
    Complex.exp (-(C:ℂ) * ((γ:ℂ) + (δ:ℂ)*Complex.I)^2) +
    Complex.exp (-(C:ℂ) * ((γ:ℂ) - (δ:ℂ)*Complex.I)^2) +
    Complex.exp (-(C:ℂ) * (-(γ:ℂ) + (δ:ℂ)*Complex.I)^2) +
    Complex.exp (-(C:ℂ) * (-(γ:ℂ) - (δ:ℂ)*Complex.I)^2) =
    ((4 * Real.exp (-C * (γ^2 - δ^2)) * Real.cos (2*C*γ*δ) : ℝ) : ℂ) := by
  -- the two "negative-γ" squares coincide with the two "positive-γ" squares
  have hsq1 : (-(γ:ℂ) - (δ:ℂ)*Complex.I)^2 = ((γ:ℂ) + (δ:ℂ)*Complex.I)^2 := by ring
  have hsq2 : (-(γ:ℂ) + (δ:ℂ)*Complex.I)^2 = ((γ:ℂ) - (δ:ℂ)*Complex.I)^2 := by ring
  rw [hsq1, hsq2]
  -- the remaining two terms are complex conjugates of one another
  set z : ℂ := Complex.exp (-(C:ℂ) * ((γ:ℂ) + (δ:ℂ)*Complex.I)^2) with hz
  have hconj_arg : (starRingEnd ℂ) (-(C:ℂ) * ((γ:ℂ) + (δ:ℂ)*Complex.I)^2) =
      -(C:ℂ) * ((γ:ℂ) - (δ:ℂ)*Complex.I)^2 := by
    rw [map_mul, map_neg, Complex.conj_ofReal, map_pow, map_add, Complex.conj_ofReal,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hconj : Complex.exp (-(C:ℂ) * ((γ:ℂ) - (δ:ℂ)*Complex.I)^2) = (starRingEnd ℂ) z := by
    rw [hz, ← Complex.exp_conj, hconj_arg]
  -- the real part of z, via exp_re and the coordinates of the square
  have harg : -(C:ℂ) * ((γ:ℂ) + (δ:ℂ)*Complex.I)^2 =
      ((-C * (γ^2 - δ^2) : ℝ) : ℂ) + ((-C * (2*γ*δ) : ℝ) : ℂ)*Complex.I := by
    rw [sq_coords]
    push_cast
    ring
  have hre : ((-C * (γ^2 - δ^2) : ℝ) : ℂ).re + (((-C * (2*γ*δ) : ℝ) : ℂ)*Complex.I).re
      = -C * (γ^2 - δ^2) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ((-C * (γ^2 - δ^2) : ℝ) : ℂ).im + (((-C * (2*γ*δ) : ℝ) : ℂ)*Complex.I).im
      = -C * (2*γ*δ) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hzre : z.re = Real.exp (-C * (γ^2 - δ^2)) * Real.cos (-C * (2*γ*δ)) := by
    rw [hz, Complex.exp_re, harg, Complex.add_re, Complex.add_im, hre, him]
  rw [hconj]
  calc z + (starRingEnd ℂ) z + (starRingEnd ℂ) z + z
      = 2 * (z + (starRingEnd ℂ) z) := by ring
    _ = 2 * ((2 * z.re : ℝ) : ℂ) := by rw [Complex.add_conj]
    _ = ((4 * z.re : ℝ) : ℂ) := by push_cast; ring
    _ = ((4 * Real.exp (-C * (γ^2 - δ^2)) * Real.cos (2*C*γ*δ) : ℝ) : ℂ) := by
        rw [hzre, show -C * (2*γ*δ) = -(2*C*γ*δ) by ring, Real.cos_neg]
        push_cast
        ring

/-- On the critical line (`δ = 0`) the pair `{±γ}` contributes `2·e^{−Cγ²}`, exactly. -/
theorem pair_contribution (C γ : ℝ) :
    Complex.exp (-(C:ℂ) * (γ:ℂ)^2) + Complex.exp (-(C:ℂ) * (-(γ:ℂ))^2) =
    ((2 * Real.exp (-C * γ^2) : ℝ) : ℂ) := by
  have h : (-(γ:ℂ))^2 = (γ:ℂ)^2 := by ring
  rw [h]
  have harg : -(C:ℂ) * (γ:ℂ)^2 = ((-C * γ^2 : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

/-! ## Q2: the sign mechanism -/

/-- The quartet contribution is negative whenever the oscillatory cross-term factor
    `cos(2Cγδ)` is — the sign flip is in the cross-term. -/
theorem quartet_neg_of_cos_neg {C γ δ : ℝ} (h : Real.cos (2*C*γ*δ) < 0) :
    4 * Real.exp (-C * (γ^2 - δ^2)) * Real.cos (2*C*γ*δ) < 0 := by
  have hpos : (0:ℝ) < 4 * Real.exp (-C * (γ^2 - δ^2)) := by positivity
  nlinarith [mul_pos hpos (neg_pos.mpr h)]

/-- Conversely: a negative quartet contribution forces `cos(2Cγδ) < 0` — no other part
    of the closed form can produce the sign. -/
theorem cos_neg_of_quartet_neg {C γ δ : ℝ}
    (h : 4 * Real.exp (-C * (γ^2 - δ^2)) * Real.cos (2*C*γ*δ) < 0) :
    Real.cos (2*C*γ*δ) < 0 := by
  by_contra hc
  push_neg at hc
  have hpos : (0:ℝ) < 4 * Real.exp (-C * (γ^2 - δ^2)) := by positivity
  nlinarith [mul_nonneg hpos.le hc]

/-- **Amplification**: the off-line magnitude factor splits as
    `e^{−C(γ²−δ²)} = e^{−Cγ²}·e^{Cδ²}` with `e^{Cδ²} ≥ 1` for `C ≥ 0` — moving off the
    line can only amplify the envelope relative to the on-line value. -/
theorem quartet_amplification {C : ℝ} (hC : 0 ≤ C) (γ δ : ℝ) :
    Real.exp (-C * (γ^2 - δ^2)) = Real.exp (-C * γ^2) * Real.exp (C * δ^2) ∧
    1 ≤ Real.exp (C * δ^2) := by
  constructor
  · rw [← Real.exp_add]
    congr 1
    ring
  · have h0 : (0:ℝ) ≤ C * δ^2 := by positivity
    linarith [Real.add_one_le_exp (C * δ^2)]

/-! ## Q3: positivity transport along group homomorphisms (the ℝ-factor seed) -/

/-- **Positivity transports along additive homomorphisms**: if `P` is positive-type,
    so is `P ∘ φ` for every additive group homomorphism `φ : ℝ →+ ℝ`. In log
    coordinates this is the `ℝ⁺`-factor seed of the memo's §6.1 transport question;
    the idèle-class-group-level statement stays open (idèle class groups are not in
    Mathlib — the honest gap recorded since PR #45). -/
theorem positiveType_comp_addMonoidHom {P : ℝ → ℝ}
    (hP : GppHaarPositivityWeil.PositiveType P) (φ : ℝ →+ ℝ) :
    GppHaarPositivityWeil.PositiveType (fun x => P (φ x)) := by
  intro n x c
  have h := hP n (fun i => φ (x i)) c
  simp only [← map_sub] at h
  exact h

/-! ## Q4: the Cesàro datum is shadow-positive, in Gram form -/

/-- **The Cesàro/Abel state is nonnegative on squares of finite linear combinations** —
    the memo's §3 "the Cesàro mechanism is a shadow-positive datum," in the repo's
    finite-Gram idiom, directly from the proved positivity of `ω_ε` (PR #61). -/
theorem cesaro_gram_sq_nonneg {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ}
    (c : Fin n → ℝ) (f : Fin n → ℝ → ℝ) :
    0 ≤ ε / 2 * ((∫ u in Set.Iic (0 : ℝ),
        Real.exp (-ε * |u|) * (∑ i : Fin n, c i * f i u) ^ 2) +
      ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-ε * |u|) * (∑ i : Fin n, c i * f i u) ^ 2) :=
  GppAbelCesaro.abel_state_sq_nonneg hε (fun u => ∑ i : Fin n, c i * f i u)

end GppQuartet
