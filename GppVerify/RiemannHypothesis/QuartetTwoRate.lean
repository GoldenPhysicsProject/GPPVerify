import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Two-rate positivity for a single zero quartet

For a complex number `lam` with `|Im lam| < Re lam` (that is, `|arg lam| < π/4`) the quartet
response

  `resp lam b = 4 * Re (b / (b^2 + lam))`,   `b > 0`,

has the following properties, all proved here with no analytic input.

* `resp lam b > 0`.
* `b ↦ resp lam b / b` is strictly decreasing on `b > 0`.
* `b ↦ b * resp lam b` is strictly increasing on `b > 0`.
* For two distinct rates `b ≠ c` (both `> 0`) the real symmetric `2 × 2` interpolation matrix
  `[[K b b, K b c], [K b c, K c c]]` with `K b c = (resp lam b + resp lam c) / (b + c)` is
  positive definite: the quadratic form is strictly positive on every nonzero real vector.

The hypothesis `|Im lam| < Re lam` holds for every quartet of `ξ` (real displacement at most `1/2`,
height above `3`) and of the quarter-shifted product `ξ(s + 1/4) ξ(s - 1/4)` (displacement at most
`3/4`, height above `3`), so these statements are shift-invariant: the same positivity holds for
both functions at any two distinct unmodulated rates.

The sandwich `c / b < resp lam b / resp lam c < b / c` (for `b > c`) is the content of the first
three items, and positive definiteness of the matrix is the abstract
`pairForm_pos` below (determinant `= (b v - c u)(b u - c v) / (b c (b + c)^2)`).

* `sum_pairForm_pos`: for any nonempty family of admissible quartets with multiplicities `n k ≥ 1`
  whose weighted diagonal and off-diagonal kernels are summable, the summed two-rate form is
  strictly positive on nonzero vectors. This is the step that turns per-quartet positive
  definiteness into positive definiteness of the interpolation matrix of the full function once
  its zeros are paired into quartets.

Names in this file: `GppQuartetTwoRate.resp`, `GppQuartetTwoRate.pairKernel`,
`GppQuartetTwoRate.pairForm_pos`, `GppQuartetTwoRate.quartet_pairForm_pos`,
`GppQuartetTwoRate.sum_pairForm_pos`.
-/

namespace GppQuartetTwoRate

/-- Quartet response at rate `b`: `4 Re (b / (b^2 + lam))`. -/
noncomputable def resp (lam : ℂ) (b : ℝ) : ℝ := 4 * ((b : ℂ) / ((b : ℂ) ^ 2 + lam)).re

/-- Pair kernel `K(b,c) = (resp b + resp c) / (b + c)`. -/
noncomputable def pairKernel (lam : ℂ) (b c : ℝ) : ℝ := (resp lam b + resp lam c) / (b + c)

/-- Closed real form of the response, in terms of `p = Re lam` and `q = Im lam`. -/
theorem resp_eq (lam : ℂ) (b : ℝ) :
    resp lam b = 4 * b * (b ^ 2 + lam.re) / ((b ^ 2 + lam.re) ^ 2 + lam.im ^ 2) := by
  unfold resp
  have h : ((b : ℂ) / ((b : ℂ) ^ 2 + lam)).re =
      b * (b ^ 2 + lam.re) / ((b ^ 2 + lam.re) * (b ^ 2 + lam.re) + lam.im * lam.im) := by
    rw [Complex.div_re]
    simp [Complex.normSq_apply, pow_two]
  rw [h]
  ring

/-- Real helper: `F s = 4 s / (s^2 + q^2)` is strictly decreasing when `q^2 < s t`. -/
theorem F_lt {q s t : ℝ} (hs : 0 < s) (hst : s < t) (hq : q ^ 2 < s * t) :
    4 * t / (t ^ 2 + q ^ 2) < 4 * s / (s ^ 2 + q ^ 2) := by
  have ht : 0 < t := lt_trans hs hst
  rw [div_lt_div_iff₀ (by nlinarith [sq_nonneg q, mul_pos ht ht]) (by nlinarith [sq_nonneg q, mul_pos hs hs])]
  nlinarith [mul_pos (sub_pos.2 hst) (sub_pos.2 hq)]

/-- Real helper: `G s = 4 (s - p) s / (s^2 + q^2)` is strictly increasing for `p < s < t`
when `0 < p`. -/
theorem G_lt {p q s t : ℝ} (hp : 0 < p) (hps : p < s) (hst : s < t) :
    4 * (s - p) * s / (s ^ 2 + q ^ 2) < 4 * (t - p) * t / (t ^ 2 + q ^ 2) := by
  have ht : p < t := lt_trans hps hst
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [div_lt_div_iff₀ (by nlinarith [sq_nonneg q, mul_pos hs0 hs0]) (by nlinarith [sq_nonneg q, mul_pos ht0 ht0])]
  have hpos : 0 < (t - s) * (q ^ 2 * (t + s - p) + p * s * t) := by
    apply mul_pos (sub_pos.2 hst)
    have h1 : 0 ≤ q ^ 2 * (t + s - p) := mul_nonneg (sq_nonneg q) (by linarith)
    have h2 : 0 < p * s * t := by
      have : 0 < s := by linarith
      have : 0 < t := by linarith
      positivity
    linarith
  have hid : 4 * (t - p) * t * (s ^ 2 + q ^ 2) - 4 * (s - p) * s * (t ^ 2 + q ^ 2) =
      4 * ((t - s) * (q ^ 2 * (t + s - p) + p * s * t)) := by ring
  nlinarith [hid, hpos]

/-- Abstract positivity of the `2 × 2` pair form: for positive `b c u v` with
`c u < b v` and `c v < b u` the form
`(u/b) d1^2 + 2 ((u+v)/(b+c)) d1 d2 + (v/c) d2^2` is strictly positive on nonzero vectors. -/
theorem pairForm_pos {b c u v : ℝ} (hb : 0 < b) (hc : 0 < c) (hu : 0 < u) (_hv : 0 < v)
    (h1 : c * u < b * v) (h2 : c * v < b * u) {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < (u / b) * d1 ^ 2 + 2 * ((u + v) / (b + c)) * d1 * d2 + (v / c) * d2 ^ 2 := by
  have hK : 0 < u / b := div_pos hu hb
  have hbc : 0 < b + c := by linarith
  have hdet : 0 < u / b * (v / c) - ((u + v) / (b + c)) ^ 2 := by
    have : u / b * (v / c) - ((u + v) / (b + c)) ^ 2 =
        (b * v - c * u) * (b * u - c * v) / (b * c * (b + c) ^ 2) := by
      field_simp
      ring
    rw [this]
    exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  set Q := (u / b) * d1 ^ 2 + 2 * ((u + v) / (b + c)) * d1 * d2 + (v / c) * d2 ^ 2 with hQ
  have key : (u / b) * Q = ((u / b) * d1 + ((u + v) / (b + c)) * d2) ^ 2 +
      (u / b * (v / c) - ((u + v) / (b + c)) ^ 2) * d2 ^ 2 := by
    rw [hQ]; ring
  have hpos : 0 < (u / b) * Q := by
    rw [key]
    by_cases h : d2 = 0
    · have hd1 : d1 ≠ 0 := by
        rcases hd with hd | hd
        · exact hd
        · exact absurd h hd
      subst h
      have : 0 < ((u / b) * d1 + ((u + v) / (b + c)) * 0) ^ 2 := by
        have : (u / b) * d1 + ((u + v) / (b + c)) * 0 ≠ 0 := by
          simpa using mul_ne_zero hK.ne' hd1
        positivity
      nlinarith [sq_nonneg (0 : ℝ)]
    · have : 0 < (u / b * (v / c) - ((u + v) / (b + c)) ^ 2) * d2 ^ 2 := by
        have : 0 < d2 ^ 2 := by positivity
        exact mul_pos hdet this
      nlinarith [sq_nonneg ((u / b) * d1 + ((u + v) / (b + c)) * d2)]
  exact (mul_pos_iff_of_pos_left hK).mp hpos

/-- Positivity of the response when `0 < Re lam`. -/
theorem resp_pos {lam : ℂ} (hlam : 0 < lam.re) {b : ℝ} (hb : 0 < b) : 0 < resp lam b := by
  rw [resp_eq]
  have : 0 < b ^ 2 + lam.re := by positivity
  positivity

/-- `resp lam b / b` is strictly decreasing on `b > 0` when `|Im lam| < Re lam`. -/
theorem resp_div_lt {lam : ℂ} (hlam : |lam.im| < lam.re) {b c : ℝ} (hc : 0 < c) (hcb : c < b) :
    resp lam b / b < resp lam c / c := by
  have hb : 0 < b := lt_trans hc hcb
  have hp : 0 < lam.re := lt_of_le_of_lt (abs_nonneg _) hlam
  have hq : lam.im ^ 2 < lam.re ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_lt.mp hlam]) (abs_lt.mp hlam).2
    simpa using this
  have e : ∀ x : ℝ, 0 < x → resp lam x / x =
      4 * (x ^ 2 + lam.re) / ((x ^ 2 + lam.re) ^ 2 + lam.im ^ 2) := by
    intro x hx
    rw [resp_eq]
    field_simp
  rw [e b hb, e c hc]
  apply F_lt (by positivity)
  · nlinarith
  · have : lam.re ^ 2 < (c ^ 2 + lam.re) * (b ^ 2 + lam.re) := by
      nlinarith [sq_nonneg b, sq_nonneg c, mul_pos hb hc]
    linarith

/-- `b * resp lam b` is strictly increasing on `b > 0` when `|Im lam| < Re lam`. -/
theorem mul_resp_lt {lam : ℂ} (hlam : |lam.im| < lam.re) {b c : ℝ} (hc : 0 < c) (hcb : c < b) :
    c * resp lam c < b * resp lam b := by
  have hb : 0 < b := lt_trans hc hcb
  have hp : 0 < lam.re := lt_of_le_of_lt (abs_nonneg _) hlam
  have e : ∀ x : ℝ, x * resp lam x =
      4 * ((x ^ 2 + lam.re) - lam.re) * (x ^ 2 + lam.re) /
        ((x ^ 2 + lam.re) ^ 2 + lam.im ^ 2) := by
    intro x
    rw [resp_eq]
    ring
  rw [e b, e c]
  apply G_lt hp
  · nlinarith [sq_nonneg c]
  · nlinarith

/-- Strict positive definiteness of the two-rate quartet matrix: for `|Im lam| < Re lam`, rates
`0 < c < b` and every nonzero real `(d1, d2)`, the form
`K(b,b) d1^2 + 2 K(b,c) d1 d2 + K(c,c) d2^2` is strictly positive, where
`K(b,b) = resp lam b / b`. -/
theorem quartet_pairForm_pos {lam : ℂ} (hlam : |lam.im| < lam.re) {b c : ℝ} (hc : 0 < c)
    (hcb : c < b) {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < (resp lam b / b) * d1 ^ 2 + 2 * pairKernel lam b c * d1 * d2 +
      (resp lam c / c) * d2 ^ 2 := by
  have hb : 0 < b := lt_trans hc hcb
  have hp : 0 < lam.re := lt_of_le_of_lt (abs_nonneg _) hlam
  have h1 : c * resp lam b < b * resp lam c := by
    have := resp_div_lt hlam hc hcb
    rw [div_lt_div_iff₀ hb hc] at this
    linarith
  have h2 : c * resp lam c < b * resp lam b := by
    have := mul_resp_lt hlam hc hcb
    nlinarith
  have := pairForm_pos hb hc (resp_pos hp hb) (resp_pos hp hc) h1 (by linarith) hd
  simpa [pairKernel] using this

/-- Sandwich form: for `0 < c < b`, `(c / b) * resp c < resp b < (b / c) * resp c`. -/
theorem resp_sandwich {lam : ℂ} (hlam : |lam.im| < lam.re) {b c : ℝ} (hc : 0 < c) (hcb : c < b) :
    c / b * resp lam c < resp lam b ∧ resp lam b < b / c * resp lam c := by
  have hb : 0 < b := lt_trans hc hcb
  have h1 := resp_div_lt hlam hc hcb
  have h2 := mul_resp_lt hlam hc hcb
  rw [div_lt_div_iff₀ hb hc] at h1
  constructor
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hb]
    linarith
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hc]
    linarith

#print axioms resp_eq
#print axioms pairForm_pos
#print axioms resp_div_lt
#print axioms mul_resp_lt
#print axioms quartet_pairForm_pos
#print axioms resp_sandwich

/-! ### Summation over quartets -/

/-- Quadratic form of the two-rate matrix of one quartet. -/
noncomputable def pairForm (lam : ℂ) (b c d1 d2 : ℝ) : ℝ :=
  (resp lam b / b) * d1 ^ 2 + 2 * pairKernel lam b c * d1 * d2 + (resp lam c / c) * d2 ^ 2

/-- A weighted, summable family of admissible quartets gives a positive definite two-rate form.
Here `n k` is the multiplicity of the `k`-th quartet and the three summability hypotheses say
that the diagonal and off-diagonal kernels converge when summed with multiplicities. -/
theorem sum_pairForm_pos {ι : Type*} [Nonempty ι] (lam : ι → ℂ) (n : ι → ℕ)
    (hn : ∀ k, 1 ≤ n k) (hlam : ∀ k, |(lam k).im| < (lam k).re) {b c : ℝ} (hc : 0 < c)
    (hcb : c < b)
    (hb : Summable fun k => (n k : ℝ) * (resp (lam k) b / b))
    (hcc : Summable fun k => (n k : ℝ) * (resp (lam k) c / c))
    (hbc : Summable fun k => (n k : ℝ) * pairKernel (lam k) b c)
    {d1 d2 : ℝ} (hd : d1 ≠ 0 ∨ d2 ≠ 0) :
    0 < (∑' k, (n k : ℝ) * (resp (lam k) b / b)) * d1 ^ 2 +
        2 * (∑' k, (n k : ℝ) * pairKernel (lam k) b c) * d1 * d2 +
        (∑' k, (n k : ℝ) * (resp (lam k) c / c)) * d2 ^ 2 := by
  have hterm : Summable fun k => (n k : ℝ) * pairForm (lam k) b c d1 d2 := by
    have := ((hb.mul_right (d1 ^ 2)).add ((hbc.mul_right (2 * d1 * d2)).add
      (hcc.mul_right (d2 ^ 2))))
    refine this.congr fun k => ?_
    unfold pairForm
    ring
  have hpos : ∀ k, 0 < (n k : ℝ) * pairForm (lam k) b c d1 d2 := fun k => by
    have h1 : (0 : ℝ) < n k := by exact_mod_cast lt_of_lt_of_le one_pos (hn k)
    exact mul_pos h1 (quartet_pairForm_pos (hlam k) hc hcb hd)
  have hsum : 0 < ∑' k, (n k : ℝ) * pairForm (lam k) b c d1 d2 :=
    hterm.tsum_pos (fun k => (hpos k).le) (Classical.arbitrary ι) (hpos _)
  have heq : ∑' k, (n k : ℝ) * pairForm (lam k) b c d1 d2 =
      (∑' k, (n k : ℝ) * (resp (lam k) b / b)) * d1 ^ 2 +
        2 * (∑' k, (n k : ℝ) * pairKernel (lam k) b c) * d1 * d2 +
        (∑' k, (n k : ℝ) * (resp (lam k) c / c)) * d2 ^ 2 := by
    have e : (fun k => (n k : ℝ) * pairForm (lam k) b c d1 d2) =
        fun k => (n k : ℝ) * (resp (lam k) b / b) * d1 ^ 2 +
          ((n k : ℝ) * pairKernel (lam k) b c * (2 * d1 * d2) +
            (n k : ℝ) * (resp (lam k) c / c) * d2 ^ 2) := by
      funext k
      unfold pairForm
      ring
    rw [e, (hb.mul_right _).tsum_add ((hbc.mul_right _).add (hcc.mul_right _)),
      (hbc.mul_right _).tsum_add (hcc.mul_right _), tsum_mul_right, tsum_mul_right,
      tsum_mul_right]
    ring
  rw [← heq]
  exact hsum

#print axioms sum_pairForm_pos

end GppQuartetTwoRate
