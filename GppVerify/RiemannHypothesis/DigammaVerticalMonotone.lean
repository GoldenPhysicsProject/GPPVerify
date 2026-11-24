import GppVerify.RiemannHypothesis.PlasticConstant
import GppVerify.RiemannHypothesis.DigammaGaussSeries

/-!
# `Re ψ(a + iy)` is strictly increasing in `y ≥ 0`, and the digamma shift

From the in-tree Gauss series `ψ(s) = −γ − 1/s + Σ_n [1/(n+1) − 1/(n+1+s)]`
(`GppDigammaGaussSeries.digammaSeries_eq_digamma`), for real `a > 0`:

`Re ψ(a + iy) = −γ − a/(a² + y²) + Σ_n [1/(n+1) − (n+1+a)/((n+1+a)² + y²)]`   (`re_digamma_series`).

Every term is a nondecreasing function of `y²`, and the first is strictly increasing, so
**`Re ψ(a + iy) < Re ψ(a + iy')` for `0 ≤ y < y'`** (`re_digamma_strictMonoOn`). Also the shift
`ψ(s + 1) = ψ(s) + 1/s` gives
**`Re ψ(a + 1 + iy) = Re ψ(a + iy) + a/(a² + y²)`** (`re_digamma_add_one`) — the `1/4 → 5/4` shift in GPT's
reference multiplier `m_ref(λ) = Re ψ(5/4 + iλ/2) − log π` (Turbo relays `fe9d9b5`/`f7f6242`: cleared
candidate (2)).

**Scope.** Real-part formula, monotonicity, and the shift. The existence and uniqueness of the zero `λ*` of
`m_ref` (needs `ψ(1/4)` and a rigorous large-`λ` lower bound) and the identification of `m_ref` with the
reference multiplier of the Weil form are **not** here. Nothing about positivity of the Weil form.

No `sorry`, no axiom.
-/

open Complex

noncomputable section

namespace GppDigammaVertical

/-- The point `a + i y`. -/
def pt (a y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * Complex.I

theorem pt_re (a y : ℝ) : (pt a y).re = a := by simp [pt]
theorem pt_im (a y : ℝ) : (pt a y).im = y := by simp [pt]

theorem offPoles_pt {a : ℝ} (ha : 0 < a) (y : ℝ) : GppDigammaSeries.OffPoles (pt a y) := by
  intro n h
  have := congrArg Complex.re h
  simp [pt] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem normSq_pt (a y : ℝ) : Complex.normSq (pt a y) = a ^ 2 + y ^ 2 := by
  simp [Complex.normSq_apply, pt]; ring

/-- Real part of the `n`-th series term: `1/(n+1) − (n+1+a)/((n+1+a)² + y²)`. -/
def Tn (a y : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + y ^ 2)

theorem re_term {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    (GppDigammaSeries.digammaSeriesTerm (pt a y) n).re = Tn a y n := by
  unfold GppDigammaSeries.digammaSeriesTerm Tn
  have hn : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
  rw [Complex.sub_re]
  have h1 : (((n : ℂ) + 1)⁻¹).re = 1 / ((n : ℝ) + 1) := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have h2 : (((n : ℂ) + 1 + pt a y)⁻¹).re =
      ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + y ^ 2) := by
    have : ((n : ℂ) + 1 + pt a y) = ((((n : ℝ) + 1 + a : ℝ) : ℂ)) + (y : ℂ) * Complex.I := by
      simp [pt]; ring
    rw [Complex.inv_re, this]
    have : Complex.normSq ((((n : ℝ) + 1 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        ((n : ℝ) + 1 + a) ^ 2 + y ^ 2 := by
      simp [Complex.normSq_apply]; ring
    rw [this]; simp
  rw [h1, h2]

theorem summable_Tn {a : ℝ} (ha : 0 < a) (y : ℝ) : Summable (Tn a y) := by
  have hs := GppDigammaSeries.summable_digammaSeriesTerm (offPoles_pt ha y)
  have := (Complex.reCLM.summable hs)
  refine this.congr fun n => ?_
  simpa using re_term ha y n

/-- **Real part of the Gauss series.** -/
theorem re_digamma_series {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (Complex.digamma (pt a y)).re =
      -Real.eulerMascheroniConstant - a / (a ^ 2 + y ^ 2) + ∑' n : ℕ, Tn a y n := by
  have hpoles : ∀ m : ℕ, pt a y ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [pt] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [← GppDigammaGaussSeries.digammaSeries_eq_digamma hpoles]
  unfold GppDigammaSeries.digammaSeries
  have hs := GppDigammaSeries.summable_digammaSeriesTerm (offPoles_pt ha y)
  have htsum : (∑' n : ℕ, GppDigammaSeries.digammaSeriesTerm (pt a y) n).re = ∑' n : ℕ, Tn a y n := by
    have := Complex.reCLM.map_tsum hs
    simp only [Complex.reCLM_apply] at this
    rw [this]
    exact tsum_congr fun n => re_term ha y n
  have hinv : ((pt a y)⁻¹).re = a / (a ^ 2 + y ^ 2) := by
    rw [Complex.inv_re, normSq_pt, pt_re]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, hinv, htsum]

/-- Each term is nondecreasing in `y²`. -/
theorem Tn_mono {a : ℝ} (ha : 0 < a) {y y' : ℝ} (h : y ^ 2 ≤ y' ^ 2) (n : ℕ) :
    Tn a y n ≤ Tn a y' n := by
  unfold Tn
  have hn : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
  have h1 : 0 < ((n : ℝ) + 1 + a) ^ 2 + y ^ 2 := by positivity
  have h2 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + y' ^ 2) ≤
      ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + y ^ 2) :=
    div_le_div_of_nonneg_left hn.le h1 (by linarith)
  linarith

/-- **`Re ψ(a + iy)` is strictly increasing in `y ≥ 0`.** -/
theorem re_digamma_strictMonoOn {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun y : ℝ => (Complex.digamma (pt a y)).re) (Set.Ici 0) := by
  intro y hy y' hy' hlt
  have hy0 : (0 : ℝ) ≤ y := hy
  have hsq : y ^ 2 < y' ^ 2 := by nlinarith
  simp only
  rw [re_digamma_series ha y, re_digamma_series ha y']
  have hT : ∑' n : ℕ, Tn a y n ≤ ∑' n : ℕ, Tn a y' n :=
    (summable_Tn ha y).tsum_le_tsum (fun n => Tn_mono ha hsq.le n) (summable_Tn ha y')
  have hfrac : -(a / (a ^ 2 + y ^ 2)) < -(a / (a ^ 2 + y' ^ 2)) := by
    rw [neg_lt_neg_iff]
    exact div_lt_div_of_pos_left ha (by positivity) (by linarith)
  linarith

/-- **The shift:** `Re ψ(a + 1 + iy) = Re ψ(a + iy) + a/(a² + y²)`. -/
theorem re_digamma_add_one {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (Complex.digamma (pt (a + 1) y)).re = (Complex.digamma (pt a y)).re + a / (a ^ 2 + y ^ 2) := by
  have hs : ∀ m : ℕ, pt a y ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [pt] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := Complex.digamma_apply_add_one (pt a y) hs
  have e : pt (a + 1) y = pt a y + 1 := by simp [pt]; ring
  rw [e, h, Complex.add_re, Complex.inv_re, normSq_pt, pt_re]

end GppDigammaVertical

#print axioms GppDigammaVertical.re_digamma_strictMonoOn
#print axioms GppDigammaVertical.re_digamma_add_one
