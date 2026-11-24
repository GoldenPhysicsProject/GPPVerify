/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.DigammaGaussSeries

/-!
# Two-sided bounds for `Re ψ` on vertical lines

For `s = a + b i` with `a > 0`, Gauss's series (`Complex.hasSum_digamma`) gives

  `Re ψ(s) = -γ - a / (a² + b²) + ∑_{n ≥ 0} t_n(a, b)`,
  `t_n(a, b) = 1 / (n + 1) - (n + 1 + a) / ((n + 1 + a)² + b²) ≥ 0`.

## Main results

* `Complex.monotoneOn_re_digamma`: for `a > 0`, `b ↦ Re ψ(a + b i)` is monotone on `[0, ∞)`.
  Every `t_n(a, ·)` and `-a/(a² + ·²)` is increasing in `b ≥ 0`.
* `Complex.re_digamma_ge_sum`: dropping the tail of the series gives a lower bound,
  `-γ - a/(a²+b²) + ∑_{n<N} t_n(a, b) ≤ Re ψ(a + b i)`.
* `Complex.re_digamma_le_asymp` and `Complex.re_digamma_ge_asymp`: for `a > 0`,

    `L(a,b) - 1/(4((a+½)² + b²)) ≤ Re ψ(a + b i) ≤ L(a,b) + 1/(2a²)`,
    `L(a,b) = ½ log((a + ½)² + b²) - a/(a² + b²)`.

* `Complex.re_digamma_mem_Icc`: shifting by `M` with `ψ(s + 1) = ψ(s) + 1/s` gives an
  enclosure of width `3/(4(a + M)²)`:

    `G - 1/(4(a+M)²) ≤ Re ψ(a + b i) ≤ G + 1/(2(a+M)²)`,
    `G = ½ log((a + M + ½)² + b²) - (a+M)/((a+M)² + b²) - ∑_{k<M} (a+k)/((a+k)² + b²)`.

  At `a = 1/4` and `M = 1000` the width is `7.5 · 10⁻⁷`, uniformly in `b`.

## Proof

The two asymptotic bounds compare `∑ (n + 1 + a)/((n + 1 + a)² + b²)` with
`½ log((x + ½)² + b²)` term by term. The lower bound uses
`2(x-y)/(x+y) ≤ log x - log y` (`Real.two_mul_sub_div_add_le_log_sub_log`). The upper bound
uses `log x - log y ≤ (x-y)(1/x + 1/y)/2`, the series `Real.hasSum_log_one_add_inv` against a
geometric majorant. The per-term error `1/(x-½)³` telescopes against
`½(1/(x-1)² - 1/x²)`.
-/

open Filter Topology Set Finset

namespace Real

/-- **Upper Padé bound for a logarithm difference.** For `0 < y < x`,
`log x - log y ≤ (x - y) (1/x + 1/y) / 2`. -/
theorem log_sub_log_le_mul_inv_add_inv {x y : ℝ} (hy : 0 < y) (hxy : y < x) :
    log x - log y ≤ (x - y) * (1 / x + 1 / y) / 2 := by
  have hxy' : 0 < x - y := sub_pos.mpr hxy
  set c : ℝ := y / (x - y) with hc
  have hc0 : 0 < c := div_pos hy hxy'
  set q : ℝ := 1 / (2 * c + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by linarith)]; linarith
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hgeo : HasSum (fun k : ℕ => 2 * q * (q ^ 2) ^ k) (2 * q * (1 - q ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hq2).mul_left (2 * q)
  have hle : log (1 + c⁻¹) ≤ 2 * q * (1 - q ^ 2)⁻¹ := by
    refine hasSum_le (fun k => ?_) (hasSum_log_one_add_inv hc0) hgeo
    have hk : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have hp : (1 / (2 * c + 1)) ^ (2 * k + 1) = q * (q ^ 2) ^ k := by
      rw [← hq, pow_succ, pow_mul]; ring
    rw [hp]
    have : 0 ≤ q * (q ^ 2) ^ k := by positivity
    nlinarith
  have h1 : 1 + c⁻¹ = x / y := by rw [hc, inv_div]; field_simp; ring
  rw [h1, log_div (by linarith) hy.ne'] at hle
  have hx0 : 0 < x := by linarith
  have hqv : q = (x - y) / (x + y) := by
    rw [hq, hc]; field_simp; ring
  have h2 : 2 * q * (1 - q ^ 2)⁻¹ = (x - y) * (1 / x + 1 / y) / 2 := by
    rw [hqv]
    have hxy0 : 0 < x + y := by linarith
    have hden : 1 - ((x - y) / (x + y)) ^ 2 = 4 * x * y / (x + y) ^ 2 := by
      field_simp; ring
    rw [hden]
    field_simp
    ring
  linarith

end Real

namespace Complex

namespace DigammaVertical

open DigammaGauss

/-- The real part of the `n`-th Gauss-series term at `a + b i`. -/
noncomputable def reTerm (a b : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + b ^ 2)

lemma offPoles {a b : ℝ} (ha : 0 < a) : ∀ m : ℕ, (⟨a, b⟩ : ℂ) ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp only [neg_re, natCast_re] at this
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma re_inv (a b : ℝ) : ((⟨a, b⟩ : ℂ)⁻¹).re = a / (a ^ 2 + b ^ 2) := by
  rw [inv_re, normSq_apply]; simp; ring

/-- The real parts of Gauss's series. -/
lemma hasSum_reTerm {a b : ℝ} (ha : 0 < a) :
    HasSum (reTerm a b)
      ((digamma ⟨a, b⟩).re + Real.eulerMascheroniConstant + a / (a ^ 2 + b ^ 2)) := by
  have h := Complex.hasSum_re (hasSum_digamma (offPoles (b := b) ha))
  have hterm : ∀ n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 1 + ⟨a, b⟩)).re = reTerm a b n := by
    intro n
    have e := re_term a b n
    simp only [term, one_div] at e ⊢
    rw [e]; simp [reTerm, phi]
  have hval : (digamma ⟨a, b⟩ + (Real.eulerMascheroniConstant : ℂ) + 1 / ⟨a, b⟩).re
      = (digamma ⟨a, b⟩).re + Real.eulerMascheroniConstant + a / (a ^ 2 + b ^ 2) := by
    rw [add_re, add_re, ofReal_re, one_div, re_inv]
  rw [hval] at h
  exact h.congr_fun (fun n => (hterm n).symm)

lemma reTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (n : ℕ) : 0 ≤ reTerm a b n := by
  unfold reTerm
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : (n : ℝ) + 1 ≤ (n : ℝ) + 1 + a := by linarith
  have hcpos : 0 < (n : ℝ) + 1 + a := by linarith
  have h1 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + b ^ 2) ≤ 1 / ((n : ℝ) + 1 + a) := by
    rw [div_le_div_iff₀ (by positivity) hcpos]; nlinarith [sq_nonneg b]
  have h2 : 1 / ((n : ℝ) + 1 + a) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le hn hc
  linarith

lemma reTerm_mono {a : ℝ} (ha : 0 ≤ a) {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb : b₁ ≤ b₂) (n : ℕ) :
    reTerm a b₁ n ≤ reTerm a b₂ n := by
  unfold reTerm
  have hcpos : 0 < (n : ℝ) + 1 + a := by positivity
  have hsq : b₁ ^ 2 ≤ b₂ ^ 2 := by nlinarith
  have : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + b₂ ^ 2) ≤
      ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + b₁ ^ 2) :=
    div_le_div_of_nonneg_left hcpos.le (by positivity) (by linarith)
  linarith

/-- Partial sums of the real parts: harmonic number minus the `φ`-sum. -/
lemma sum_reTerm (a b : ℝ) (N : ℕ) :
    ∑ n ∈ range N, reTerm a b n
      = ((harmonic N : ℚ) : ℝ) - ∑ n ∈ range N, phi b ((n : ℝ) + 1 + a) := by
  have hharm : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
    rw [harmonic]; push_cast; simp
  rw [hharm, ← Finset.sum_sub_distrib]
  rfl

/-- `harmonic N - ½ log((N + c)² + b²) → γ`. -/
lemma tendsto_harmonic_sub_logPot (b c : ℝ) :
    Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + c)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have := Real.tendsto_harmonic_sub_log.sub (tendsto_logPot_sub_log b c)
  rw [sub_zero] at this
  refine this.congr (fun N => ?_)
  ring

/-- Per-term lower comparison, for `x ≥ 1`. -/
lemma phi_le_of_one_le (b x : ℝ) (hx1 : 1 ≤ x) :
    phi b x ≤ (logPot b (x + 1 / 2) - logPot b (x - 1 / 2))
      + (invQuad b (x - 1 / 2) - invQuad b (x + 1 / 2)) / 4 := by
  have hx : 0 < x := by linarith
  unfold phi logPot invQuad
  set A : ℝ := (x + 1 / 2) ^ 2 + b ^ 2 with hA
  set B : ℝ := (x - 1 / 2) ^ 2 + b ^ 2 with hB
  set P : ℝ := x ^ 2 + b ^ 2 with hP
  have hP0 : 1 / 4 ≤ P := by rw [hP]; nlinarith [sq_nonneg b]
  have hB0 : 0 < B := by rw [hB]; nlinarith [sq_nonneg b]
  have hA0 : 0 < A := by rw [hA]; nlinarith [sq_nonneg b]
  have hBA : B < A := by rw [hA, hB]; nlinarith
  have hlog := Real.two_mul_sub_div_add_le_log_sub_log hB0 hBA
  have hsumAB : A + B = 2 * (P + 1 / 4) := by rw [hA, hB, hP]; ring
  have hdiffAB : A - B = 2 * x := by rw [hA, hB]; ring
  have hlog' : x / (P + 1 / 4) ≤ (Real.log A - Real.log B) / 2 := by
    have : 2 * (A - B) / (A + B) = 2 * (x / (P + 1 / 4)) := by
      rw [hsumAB, hdiffAB]; field_simp
    linarith
  have halg : x / P ≤ x / (P + 1 / 4) + (1 / B - 1 / A) / 4 := by
    have hPpos : 0 < P := by linarith
    have hP4 : 0 < P + 1 / 4 := by linarith
    have e1 : x / P - x / (P + 1 / 4) = x / (4 * P * (P + 1 / 4)) := by
      field_simp; ring
    have e2 : (1 / B - 1 / A) / 4 = x / (2 * (A * B)) := by
      field_simp; rw [hA, hB]; ring
    have hABpos : 0 < A * B := mul_pos hA0 hB0
    have hle : 2 * (A * B) ≤ 4 * P * (P + 1 / 4) := by nlinarith
    have : x / (4 * P * (P + 1 / 4)) ≤ x / (2 * (A * B)) :=
      div_le_div_of_nonneg_left hx.le (by positivity) hle
    linarith
  linarith

/-- Per-term upper comparison, for `x > 1/2`:
`φ(x) ≥ ½(log A - log B) - 1/(x - ½)³`. -/
lemma phi_ge (b x : ℝ) (hx : 1 / 2 < x) :
    (logPot b (x + 1 / 2) - logPot b (x - 1 / 2)) - 1 / (x - 1 / 2) ^ 3 ≤ phi b x := by
  unfold logPot phi
  set A : ℝ := (x + 1 / 2) ^ 2 + b ^ 2 with hA
  set B : ℝ := (x - 1 / 2) ^ 2 + b ^ 2 with hB
  set P : ℝ := x ^ 2 + b ^ 2 with hP
  have hx0 : 0 < x := by linarith
  have hy : 0 < x - 1 / 2 := by linarith
  have hB0 : 0 < B := by positivity
  have hBA : B < A := by rw [hA, hB]; nlinarith
  have hA0 : 0 < A := by linarith
  have hP0 : 0 < P := by positivity
  have hlog := Real.log_sub_log_le_mul_inv_add_inv hB0 hBA
  have hdiff : A - B = 2 * x := by rw [hA, hB]; ring
  have hAB : A * B = (P + 1 / 4) ^ 2 - x ^ 2 := by rw [hA, hB, hP]; ring
  have hsum : A + B = 2 * (P + 1 / 4) := by rw [hA, hB, hP]; ring
  -- ½(log A - log B) ≤ x (1/A + 1/B)/2 = x (P + 1/4)/(A B)
  have h1 : (Real.log A - Real.log B) / 2 ≤ x * (P + 1 / 4) / (A * B) := by
    have e : (A - B) * (1 / A + 1 / B) / 2 / 2 = x * (P + 1 / 4) / (A * B) := by
      field_simp; rw [hdiff]; nlinarith [hsum]
    linarith
  -- x (P + 1/4)/(A B) - x/P = x (x² - P/4 - 1/16)/(A B P) ≤ 1/(x - 1/2)³
  have hABpos : 0 < A * B := mul_pos hA0 hB0
  have h2 : x * (P + 1 / 4) / (A * B) - x / P ≤ 1 / (x - 1 / 2) ^ 3 := by
    have e : x * (P + 1 / 4) / (A * B) - x / P = x * (x ^ 2 - P / 4 - 1 / 16) / (A * B * P) := by
      rw [div_sub_div _ _ hABpos.ne' hP0.ne', hAB]
      congr 1; ring
    rw [e]
    have hnum : x * (x ^ 2 - P / 4 - 1 / 16) ≤ x ^ 3 := by
      have e2 : x * (x ^ 2 - P / 4 - 1 / 16) = x ^ 3 - x * (P / 4 + 1 / 16) := by ring
      have : 0 ≤ x * (P / 4 + 1 / 16) := by positivity
      rw [e2]; linarith
    have hden : x ^ 4 * (x - 1 / 2) ^ 2 ≤ A * B * P := by
      have hAx : x ^ 2 ≤ A := by rw [hA]; nlinarith [sq_nonneg b]
      have hBy : (x - 1 / 2) ^ 2 ≤ B := by rw [hB]; nlinarith [sq_nonneg b]
      have hPx : x ^ 2 ≤ P := by rw [hP]; nlinarith [sq_nonneg b]
      have h1' : x ^ 2 * (x - 1 / 2) ^ 2 ≤ A * B := mul_le_mul hAx hBy (by positivity) hA0.le
      have h2' : x ^ 2 * (x - 1 / 2) ^ 2 * x ^ 2 ≤ A * B * P :=
        mul_le_mul h1' hPx (by positivity) hABpos.le
      calc x ^ 4 * (x - 1 / 2) ^ 2 = x ^ 2 * (x - 1 / 2) ^ 2 * x ^ 2 := by ring
        _ ≤ A * B * P := h2'
    calc x * (x ^ 2 - P / 4 - 1 / 16) / (A * B * P)
        ≤ x ^ 3 / (A * B * P) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ x ^ 3 / (x ^ 4 * (x - 1 / 2) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 1 / (x * (x - 1 / 2) ^ 2) := by field_simp
      _ ≤ 1 / (x - 1 / 2) ^ 3 := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (x - 1 / 2) ^ 3 = (x - 1 / 2) * (x - 1 / 2) ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hlogeq : Real.log A / 2 - Real.log B / 2 = (Real.log A - Real.log B) / 2 := by ring
  linarith

/-- `1/y³ ≤ ½ (1/(y - ½)² - 1/(y + ½)²)` for `y > 1/2`. -/
lemma inv_cube_le (y : ℝ) (hy : 1 / 2 < y) :
    1 / y ^ 3 ≤ (1 / (y - 1 / 2) ^ 2 - 1 / (y + 1 / 2) ^ 2) / 2 := by
  have h1 : 0 < y - 1 / 2 := by linarith
  have h2 : 0 < y + 1 / 2 := by linarith
  have hy0 : 0 < y := by linarith
  have key : 1 / (y - 1 / 2) ^ 2 - 1 / (y + 1 / 2) ^ 2
      = 2 * y / ((y - 1 / 2) ^ 2 * (y + 1 / 2) ^ 2) := by
    rw [div_sub_div _ _ (pow_ne_zero 2 h1.ne') (pow_ne_zero 2 h2.ne')]
    congr 1; ring
  have hD : (y - 1 / 2) ^ 2 * (y + 1 / 2) ^ 2 = (y ^ 2 - 1 / 4) ^ 2 := by ring
  have hq : 0 < y ^ 2 - 1 / 4 := by nlinarith
  have hle : (y ^ 2 - 1 / 4) ^ 2 ≤ y ^ 4 := by nlinarith
  rw [key, hD, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hy0 3]

end DigammaVertical

open DigammaGauss DigammaVertical

/-- **Monotonicity on vertical lines.** For `a > 0`, `b ↦ Re ψ(a + b i)` is monotone on `[0, ∞)`. -/
theorem monotoneOn_re_digamma {a : ℝ} (ha : 0 < a) :
    MonotoneOn (fun b : ℝ => (digamma ⟨a, b⟩).re) (Ici 0) := by
  intro b₁ hb₁ b₂ _ hb
  have hb₁' : (0 : ℝ) ≤ b₁ := hb₁
  have hle := hasSum_le (reTerm_mono ha.le hb₁' hb) (hasSum_reTerm (b := b₁) ha)
    (hasSum_reTerm (b := b₂) ha)
  have hq : a / (a ^ 2 + b₂ ^ 2) ≤ a / (a ^ 2 + b₁ ^ 2) :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by nlinarith)
  simp only
  linarith

/-- **Truncation lower bound.** For `a > 0` and every `N`,
`-γ - a/(a²+b²) + ∑_{n<N} t_n(a, b) ≤ Re ψ(a + b i)`. -/
theorem re_digamma_ge_sum {a : ℝ} (ha : 0 < a) (b : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant - a / (a ^ 2 + b ^ 2) + ∑ n ∈ range N, reTerm a b n
      ≤ (digamma ⟨a, b⟩).re := by
  have h := sum_le_hasSum (range N) (fun n _ => reTerm_nonneg ha.le b n) (hasSum_reTerm (b := b) ha)
  linarith

/-- **Asymptotic upper bound.** For `a > 0`,
`Re ψ(a + b i) ≤ ½ log((a + ½)² + b²) - a/(a² + b²) + 1/(2a²)`. -/
theorem re_digamma_le_asymp {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (digamma ⟨a, b⟩).re ≤ logPot b (a + 1 / 2) - a / (a ^ 2 + b ^ 2) + 1 / (2 * a ^ 2) := by
  have hlim := (hasSum_reTerm (b := b) ha).tendsto_sum_nat
  -- partial sums are bounded above
  have hup : ∀ N : ℕ, ∑ n ∈ range N, reTerm a b n ≤
      ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2)) + logPot b (a + 1 / 2)
        + 1 / (2 * a ^ 2) := by
    intro N
    rw [sum_reTerm]
    set g : ℕ → ℝ := fun k => logPot b ((k : ℝ) + a + 1 / 2) + 1 / (2 * ((k : ℝ) + a) ^ 2)
      with hg
    have hstep : ∀ k ∈ range N, g (k + 1) - g k ≤ phi b ((k : ℝ) + 1 + a) := by
      intro k _
      have hx : 1 / 2 < (k : ℝ) + 1 + a := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
      have hφ := phi_ge b ((k : ℝ) + 1 + a) hx
      have hy : 1 / 2 < (k : ℝ) + 1 + a - 1 / 2 := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
      have hc := inv_cube_le ((k : ℝ) + 1 + a - 1 / 2) hy
      have e1 : (k : ℝ) + 1 + a - 1 / 2 - 1 / 2 = (k : ℝ) + a := by ring
      have e2 : (k : ℝ) + 1 + a - 1 / 2 + 1 / 2 = ((k + 1 : ℕ) : ℝ) + a := by push_cast; ring
      have e3 : (k : ℝ) + 1 + a + 1 / 2 = ((k + 1 : ℕ) : ℝ) + a + 1 / 2 := by push_cast; ring
      have e4 : (k : ℝ) + 1 + a - 1 / 2 = (k : ℝ) + a + 1 / 2 := by ring
      rw [e1, e2] at hc
      rw [e3, e4] at hφ
      rw [e4] at hc
      simp only [hg]
      have : 1 / (2 * (((k + 1 : ℕ) : ℝ) + a) ^ 2) - 1 / (2 * ((k : ℝ) + a) ^ 2)
          = -((1 / ((k : ℝ) + a) ^ 2 - 1 / (((k + 1 : ℕ) : ℝ) + a) ^ 2) / 2) := by
        have h1 : 0 < (k : ℝ) + a := by positivity
        have h2 : 0 < ((k + 1 : ℕ) : ℝ) + a := by positivity
        field_simp; ring
      linarith
    have htel := Finset.sum_le_sum hstep
    rw [Finset.sum_range_sub] at htel
    simp only [hg, Nat.cast_zero, zero_add] at htel
    have hnn : 0 ≤ 1 / (2 * ((N : ℝ) + a) ^ 2) := by positivity
    have e : (N : ℝ) + (a + 1 / 2) = (N : ℝ) + a + 1 / 2 := by ring
    rw [e]
    have e' : (0 : ℝ) + a + 1 / 2 = a + 1 / 2 := by ring
    linarith
  have hlimU : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2))
      + logPot b (a + 1 / 2) + 1 / (2 * a ^ 2)) atTop
      (𝓝 (Real.eulerMascheroniConstant + logPot b (a + 1 / 2) + 1 / (2 * a ^ 2))) :=
    ((tendsto_harmonic_sub_logPot b (a + 1 / 2)).add_const _).add_const _
  have := le_of_tendsto_of_tendsto' hlim hlimU hup
  linarith

/-- **Asymptotic lower bound.** For `a > 0`,
`½ log((a + ½)² + b²) - a/(a² + b²) - 1/(4((a + ½)² + b²)) ≤ Re ψ(a + b i)`. -/
theorem re_digamma_ge_asymp {a : ℝ} (ha : 0 < a) (b : ℝ) :
    logPot b (a + 1 / 2) - a / (a ^ 2 + b ^ 2) - invQuad b (a + 1 / 2) / 4
      ≤ (digamma ⟨a, b⟩).re := by
  have hlim := (hasSum_reTerm (b := b) ha).tendsto_sum_nat
  have hlow : ∀ N : ℕ, ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2))
      + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4 ≤ ∑ n ∈ range N, reTerm a b n := by
    intro N
    rw [sum_reTerm]
    set g : ℕ → ℝ := fun k => logPot b ((k : ℝ) + a + 1 / 2) - invQuad b ((k : ℝ) + a + 1 / 2) / 4
      with hg
    have hstep : ∀ k ∈ range N, phi b ((k : ℝ) + 1 + a) ≤ g (k + 1) - g k := by
      intro k _
      have hx : 1 ≤ (k : ℝ) + 1 + a := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
      have hφ := phi_le_of_one_le b ((k : ℝ) + 1 + a) hx
      have e3 : (k : ℝ) + 1 + a + 1 / 2 = ((k + 1 : ℕ) : ℝ) + a + 1 / 2 := by push_cast; ring
      have e4 : (k : ℝ) + 1 + a - 1 / 2 = (k : ℝ) + a + 1 / 2 := by ring
      rw [e3, e4] at hφ
      simp only [hg]
      linarith
    have htel := Finset.sum_le_sum hstep
    rw [Finset.sum_range_sub] at htel
    simp only [hg, Nat.cast_zero, zero_add] at htel
    have hnn : 0 ≤ invQuad b ((N : ℝ) + a + 1 / 2) := by unfold invQuad; positivity
    have e : (N : ℝ) + (a + 1 / 2) = (N : ℝ) + a + 1 / 2 := by ring
    rw [e]
    linarith
  have hlimL : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - logPot b ((N : ℝ) + (a + 1 / 2))
      + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4) atTop
      (𝓝 (Real.eulerMascheroniConstant + logPot b (a + 1 / 2) - invQuad b (a + 1 / 2) / 4)) :=
    ((tendsto_harmonic_sub_logPot b (a + 1 / 2)).add_const _).sub_const _
  have := le_of_tendsto_of_tendsto' hlimL hlim hlow
  linarith

/-- **Shift by `M`.** `Re ψ(a + b i) = Re ψ(a + M + b i) - ∑_{k<M} (a+k)/((a+k)² + b²)`
for `a > 0`. -/
theorem re_digamma_shift {a : ℝ} (ha : 0 < a) (b : ℝ) (M : ℕ) :
    (digamma ⟨a, b⟩).re = (digamma ⟨a + M, b⟩).re
      - ∑ k ∈ range M, (a + k) / ((a + k) ^ 2 + b ^ 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hpos : 0 < a + M := by positivity
    have hstep := digamma_apply_add_one (⟨a + M, b⟩ : ℂ) (offPoles hpos)
    have e : (⟨a + M, b⟩ : ℂ) + 1 = ⟨a + ((M + 1 : ℕ) : ℝ), b⟩ := by
      apply Complex.ext <;> simp
      ring
    rw [e] at hstep
    have hre := congrArg Complex.re hstep
    rw [add_re, re_inv] at hre
    rw [ih, Finset.sum_range_succ, hre]
    ring

/-- **Two-sided enclosure of `Re ψ` on a vertical line.** For `a > 0`, `b` real and `M : ℕ`,
put `a' = a + M` and
`G = ½ log((a' + ½)² + b²) - a'/(a'² + b²) - ∑_{k<M} (a+k)/((a+k)² + b²)`. Then
`G - 1/(4a'²) ≤ Re ψ(a + b i) ≤ G + 1/(2a'²)`. -/
theorem re_digamma_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) (M : ℕ) :
    (digamma ⟨a, b⟩).re ∈ Set.Icc
      (Real.log ((a + M + 1 / 2) ^ 2 + b ^ 2) / 2 - (a + M) / ((a + M) ^ 2 + b ^ 2)
        - ∑ k ∈ range M, (a + k) / ((a + k) ^ 2 + b ^ 2) - 1 / (4 * (a + M) ^ 2))
      (Real.log ((a + M + 1 / 2) ^ 2 + b ^ 2) / 2 - (a + M) / ((a + M) ^ 2 + b ^ 2)
        - ∑ k ∈ range M, (a + k) / ((a + k) ^ 2 + b ^ 2) + 1 / (2 * (a + M) ^ 2)) := by
  have hpos : 0 < a + M := by positivity
  rw [re_digamma_shift ha b M]
  have hU := re_digamma_le_asymp hpos b
  have hL := re_digamma_ge_asymp hpos b
  have hq : invQuad b (a + M + 1 / 2) / 4 ≤ 1 / (4 * (a + M) ^ 2) := by
    unfold invQuad
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg b]
  unfold logPot at hU hL
  constructor <;> linarith

end Complex
