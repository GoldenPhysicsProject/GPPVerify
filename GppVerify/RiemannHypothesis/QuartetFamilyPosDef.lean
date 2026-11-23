import GppVerify.RiemannHypothesis.QuartetTwoRate
import GppVerify.RiemannHypothesis.XiHeightBound

/-!
# Two-rate positive definiteness for a function with a paired Hadamard expansion

A *quartet family* records the zeros of an even entire function of order one in centred
coordinates: for each index `k` a height `γ k`, a real displacement `δ k` from the symmetry
line and a weight `w k > 0`, with `|δ k| ≤ 3/4` and `3 < |γ k|`. A quartet of multiplicity `m`
has weight `m`; an on-line pair `±iγ` of multiplicity `m` has weight `m/2`, because its
contribution `m · 2b/(b² + γ²)` is half of `m · resp (γ²) b`. The response at rate `b > 0` is

  `M b = ∑' k, w k * resp (λ k) b`,   `λ k = (γ k + i δ k)^2`,

with `resp` the single-quartet response of `GppQuartetTwoRate`.

* `QuartetFamily.two_rate_posdef`: when the response series is summable at every rate, the
  two-rate interpolation form
  `(M b / b) d₁² + 2 ((M b + M c)/(b + c)) d₁ d₂ + (M c / c) d₂²`
  is strictly positive on every nonzero real `(d₁, d₂)`, for rates `0 < c < b`.
  The admissibility `|Im λ| < Re λ` of every quartet is `GppXiHeight.lam_admissible`.
* `HasQuartetPairing F`: the named hypothesis that the real part of the logarithmic derivative
  `F'/F` of `F` at positive real rates is the response of a nonempty quartet family with
  summable series. This is the paired form of the Hadamard product of an even entire function
  of order one (the pairing `1/(b - ρ) + 1/(b + ρ) = 2b/(b² - ρ²)` of a zero with its mirror,
  collected into quartets with their conjugates, multiplicities counted).
* `two_rate_posdef_of_pairing`: if `F` has a quartet pairing, then its two-rate interpolation
  form built from `Re (F'/F)` is strictly positive on nonzero vectors.
* `xiCentred`, `xiShiftedProduct`: the centred completed zeta `z ↦ ξ(1/2 + z)` and the
  quarter-shifted product `z ↦ ξ(3/4 + z) ξ(1/4 + z)`; `XiHadamardPairing` and
  `XiShiftedHadamardPairing` are their pairing hypotheses, and `xi_two_rate_posdef`,
  `xiShifted_two_rate_posdef` are the corresponding conclusions.
-/

open Complex GppQuartetTwoRate

namespace GppQuartetFamily

/-- Zeros of an even entire function in centred coordinates, with weights. -/
structure QuartetFamily (ι : Type) where
  γ : ι → ℝ
  δ : ι → ℝ
  w : ι → ℝ
  w_pos : ∀ k, 0 < w k
  hδ : ∀ k, |δ k| ≤ 3 / 4
  hγ : ∀ k, 3 < |γ k|

namespace QuartetFamily

variable {ι : Type}

/-- The quartet parameter `λ k = (γ k + i δ k)^2`. -/
noncomputable def lam (Q : QuartetFamily ι) (k : ι) : ℂ :=
  ((Q.γ k : ℂ) + (Q.δ k : ℂ) * Complex.I) ^ 2

/-- The response of the family at rate `b`. -/
noncomputable def M (Q : QuartetFamily ι) (b : ℝ) : ℝ :=
  ∑' k, Q.w k * resp (Q.lam k) b

/-- The response series converges at every positive rate. -/
def SummableAt (Q : QuartetFamily ι) : Prop :=
  ∀ b : ℝ, 0 < b → Summable fun k => Q.w k * resp (Q.lam k) b

theorem admissible (Q : QuartetFamily ι) (k : ι) : |(Q.lam k).im| < (Q.lam k).re :=
  GppXiHeight.lam_admissible (Q.hδ k) (Q.hγ k)

/-- **Two-rate positive definiteness of a quartet family.** -/
theorem two_rate_posdef [Nonempty ι] (Q : QuartetFamily ι) (hs : Q.SummableAt) {b c : ℝ}
    (hc : 0 < c) (hcb : c < b) {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < (Q.M b / b) * d1 ^ 2 + 2 * ((Q.M b + Q.M c) / (b + c)) * d1 * d2 +
      (Q.M c / c) * d2 ^ 2 := by
  have hb0 : 0 < b := lt_trans hc hcb
  have sb := hs b hb0
  have sc := hs c hc
  have hbb : Summable fun k => Q.w k * (resp (Q.lam k) b / b) :=
    (sb.mul_right b⁻¹).congr fun k => by field_simp
  have hcc : Summable fun k => Q.w k * (resp (Q.lam k) c / c) :=
    (sc.mul_right c⁻¹).congr fun k => by field_simp
  have hbc : Summable fun k => Q.w k * pairKernel (Q.lam k) b c :=
    ((sb.add sc).mul_right (b + c)⁻¹).congr fun k => by
      unfold pairKernel; field_simp
  have hterm : Summable fun k => Q.w k * pairForm (Q.lam k) b c d1 d2 := by
    have := ((hbb.mul_right (d1 ^ 2)).add ((hbc.mul_right (2 * d1 * d2)).add
      (hcc.mul_right (d2 ^ 2))))
    refine this.congr fun k => ?_
    unfold pairForm
    ring
  have hpos : ∀ k, 0 < Q.w k * pairForm (Q.lam k) b c d1 d2 := fun k =>
    mul_pos (Q.w_pos k) (quartet_pairForm_pos (Q.admissible k) hc hcb hd)
  have hsum : 0 < ∑' k, Q.w k * pairForm (Q.lam k) b c d1 d2 :=
    hterm.tsum_pos (fun k => (hpos k).le) (Classical.arbitrary ι) (hpos _)
  have e1 : ∑' k, Q.w k * (resp (Q.lam k) b / b) = Q.M b / b := by
    have : (fun k => Q.w k * (resp (Q.lam k) b / b)) =
        fun k => Q.w k * resp (Q.lam k) b * b⁻¹ := by
      funext k; ring
    rw [this, tsum_mul_right]; unfold M; ring
  have e2 : ∑' k, Q.w k * (resp (Q.lam k) c / c) = Q.M c / c := by
    have : (fun k => Q.w k * (resp (Q.lam k) c / c)) =
        fun k => Q.w k * resp (Q.lam k) c * c⁻¹ := by
      funext k; ring
    rw [this, tsum_mul_right]; unfold M; ring
  have e3 : ∑' k, Q.w k * pairKernel (Q.lam k) b c = (Q.M b + Q.M c) / (b + c) := by
    have : (fun k => Q.w k * pairKernel (Q.lam k) b c) =
        fun k => (Q.w k * resp (Q.lam k) b + Q.w k * resp (Q.lam k) c) * (b + c)⁻¹ := by
      funext k; unfold pairKernel; ring
    rw [this, tsum_mul_right, sb.tsum_add sc]; unfold M; ring
  have heq : ∑' k, Q.w k * pairForm (Q.lam k) b c d1 d2 =
      (Q.M b / b) * d1 ^ 2 + 2 * ((Q.M b + Q.M c) / (b + c)) * d1 * d2 +
        (Q.M c / c) * d2 ^ 2 := by
    have ef : (fun k => Q.w k * pairForm (Q.lam k) b c d1 d2) =
        fun k => Q.w k * (resp (Q.lam k) b / b) * d1 ^ 2 +
          (Q.w k * pairKernel (Q.lam k) b c * (2 * d1 * d2) +
            Q.w k * (resp (Q.lam k) c / c) * d2 ^ 2) := by
      funext k; unfold pairForm; ring
    rw [ef, (hbb.mul_right _).tsum_add ((hbc.mul_right _).add (hcc.mul_right _)),
      (hbc.mul_right _).tsum_add (hcc.mul_right _), tsum_mul_right, tsum_mul_right,
      tsum_mul_right, e1, e2, e3]
    ring
  rw [← heq]
  exact hsum

end QuartetFamily

/-- **Named hypothesis (paired Hadamard expansion).** The real part of the logarithmic derivative
`F'/F` at positive real rates is the response of a nonempty quartet family with summable series. -/
def HasQuartetPairing (F : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Nonempty ι) (Q : QuartetFamily ι), Q.SummableAt ∧
    ∀ b : ℝ, 0 < b → (logDeriv F (b : ℂ)).re = Q.M b

/-- **Two-rate positive definiteness from the paired Hadamard expansion.** -/
theorem two_rate_posdef_of_pairing {F : ℂ → ℂ} (h : HasQuartetPairing F) {b c : ℝ} (hc : 0 < c)
    (hcb : c < b) {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < ((logDeriv F (b : ℂ)).re / b) * d1 ^ 2 +
        2 * (((logDeriv F (b : ℂ)).re + (logDeriv F (c : ℂ)).re) / (b + c)) * d1 * d2 +
        ((logDeriv F (c : ℂ)).re / c) * d2 ^ 2 := by
  obtain ⟨ι, hne, Q, hs, hM⟩ := h
  have hb0 : 0 < b := lt_trans hc hcb
  rw [hM b hb0, hM c hc]
  exact Q.two_rate_posdef hs hc hcb hd

/-- The centred completed zeta function `z ↦ ξ(1/2 + z)`. -/
noncomputable def xiCentred (z : ℂ) : ℂ := GppLogDerivZeroFree.xi (1 / 2 + z)

/-- The quarter-shifted product `z ↦ ξ(3/4 + z) ξ(1/4 + z)`, centred. -/
noncomputable def xiShiftedProduct (z : ℂ) : ℂ :=
  GppLogDerivZeroFree.xi (3 / 4 + z) * GppLogDerivZeroFree.xi (1 / 4 + z)

/-- Named hypothesis: the paired Hadamard expansion of `ξ` (centred). -/
def XiHadamardPairing : Prop := HasQuartetPairing xiCentred

/-- Named hypothesis: the paired Hadamard expansion of the quarter-shifted product. -/
def XiShiftedHadamardPairing : Prop := HasQuartetPairing xiShiftedProduct

/-- Two-rate positive definiteness for `ξ`, from its paired Hadamard expansion. -/
theorem xi_two_rate_posdef (h : XiHadamardPairing) {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < ((logDeriv xiCentred (b : ℂ)).re / b) * d1 ^ 2 +
        2 * (((logDeriv xiCentred (b : ℂ)).re + (logDeriv xiCentred (c : ℂ)).re) / (b + c)) *
          d1 * d2 + ((logDeriv xiCentred (c : ℂ)).re / c) * d2 ^ 2 :=
  two_rate_posdef_of_pairing h hc hcb hd

/-- Two-rate positive definiteness for the quarter-shifted product, from its paired Hadamard
expansion. -/
theorem xiShifted_two_rate_posdef (h : XiShiftedHadamardPairing) {b c : ℝ} (hc : 0 < c)
    (hcb : c < b) {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < ((logDeriv xiShiftedProduct (b : ℂ)).re / b) * d1 ^ 2 +
        2 * (((logDeriv xiShiftedProduct (b : ℂ)).re + (logDeriv xiShiftedProduct (c : ℂ)).re) /
          (b + c)) * d1 * d2 + ((logDeriv xiShiftedProduct (c : ℂ)).re / c) * d2 ^ 2 :=
  two_rate_posdef_of_pairing h hc hcb hd

#print axioms QuartetFamily.two_rate_posdef
#print axioms two_rate_posdef_of_pairing
#print axioms xi_two_rate_posdef
#print axioms xiShifted_two_rate_posdef

end GppQuartetFamily
