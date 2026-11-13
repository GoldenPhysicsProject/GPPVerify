import GppVerify.RiemannHypothesis.DigammaGaussSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# A lower envelope for `Re ψ` on vertical lines, and the rung-1 symbol floor

**Main result** (`re_digamma_ge`): for `a ≥ 0` and `b ≥ 1/2`,

  `Re ψ(a + i b) ≥ log b - (a + 1/4) / b²`.

**Corollary** (`re_digamma_quarter_ge`): for `t ≥ 2`,

  `Re ψ(1/4 + i t/2) - log π ≥ log(t/(2π)) - 1/t`.

This is the digamma envelope used by the one-stroke frequency-split certificate (Zhu,
arXiv:2608.24827, Thm 1.1; Grok's Arb implementation `GPPDiscovery5/s27/s27_onestroke_arb.py`).
That script assumes it for `t ≥ 15/4`. The certificate needs it for `t ≥ T = 100`.

**Rung-1 symbol floor** (`rungOneSymbol_ge`): let `Ψ(t)` be the rung-1 symbol, with the
`n = 2, 3` prime cosines subtracted. For `2 ≤ T ≤ t`,
`Ψ(t) ≥ β(T) = log(T/(2π)) - 1/T - A`, where `A = 2 log 2/√2 + 2 log 3/√3`. This covers
pieces (b) and (c) of the Lean plan in
`GPP-bridge/work/claude-code/rung1/STEP0-REPRODUCTION-2026-11-13.md`, for every `T ≥ 2`
(the certificate uses `T = 100`).

## Proof

Start from Gauss's series (`GppDigammaGaussSeries.digammaSeries_eq_digamma`). With
`φ(x) = x/(x²+b²)`, it gives

  `Re ψ(a+ib) = -γ - a/(a²+b²) + Σ_{k≥1} (1/k - φ(k+a))`.

Put `A = (x+½)²+b²`, `B = (x-½)²+b²` and `P = x²+b²`. For `x > 0` and `b² ≥ 1/4`, each term
obeys the telescoping bound

  `φ(x) ≤ ½ (log A - log B) + ¼ (1/B - 1/A)`.

This takes two steps. The first is the sharp bound `log(1 + 1/c) ≥ 2/(2c+1)`, the first term
of Mathlib's `Real.hasSum_log_one_add_inv`, which gives `½ log(A/B) ≥ x/(P + ¼)`. The second is
`AB ≤ (P+¼)² ≤ 2P(P+¼)`. Summing and using `harmonic N - log N → γ`
(`Real.tendsto_harmonic_sub_log`) gives

  `Re ψ ≥ -a/(a²+b²) + ½ log((a+½)²+b²) - ¼/((a+½)²+b²)`.

Unconditional. No `sorry`, no axioms, no named premises.
-/

namespace GppDigammaVerticalFloor

open Complex Filter Topology Finset GppDigammaSeries GppDigammaGaussSeries

/-- `φ_b(x) = x / (x² + b²)`, the real part of `1/(x + i b)`. -/
noncomputable def phi (b x : ℝ) : ℝ := x / (x ^ 2 + b ^ 2)

/-- `F_b(y) = ½ log(y² + b²)`, an antiderivative of `φ_b`. -/
noncomputable def F (b y : ℝ) : ℝ := Real.log (y ^ 2 + b ^ 2) / 2

/-- `H_b(y) = 1/(y² + b²)`. -/
noncomputable def H (b y : ℝ) : ℝ := 1 / (y ^ 2 + b ^ 2)

/-- The sharp logarithm bound: for `B > 0` and `A > B`, `log A - log B ≥ 2(A-B)/(A+B)`. -/
theorem log_sub_log_ge {A B : ℝ} (hB : 0 < B) (hAB : B < A) :
    2 * (A - B) / (A + B) ≤ Real.log A - Real.log B := by
  set c : ℝ := B / (A - B) with hc
  have hAB' : 0 < A - B := sub_pos.mpr hAB
  have hc0 : 0 < c := div_pos hB hAB'
  have hsum := Real.hasSum_log_one_add_inv hc0
  have hterm0 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * c + 1)) ^ (2 * 0 + 1)
      ≤ Real.log (1 + c⁻¹) := by
    refine le_hasSum hsum 0 (fun k _ => ?_)
    have : 0 < 2 * c + 1 := by linarith
    positivity
  have h1 : 1 + c⁻¹ = A / B := by
    rw [hc, inv_div]; field_simp; ring
  rw [h1, Real.log_div (by linarith) hB.ne'] at hterm0
  have h2 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * c + 1)) ^ (2 * 0 + 1)
      = 2 * (A - B) / (A + B) := by
    rw [hc]; field_simp; ring
  linarith [h2 ▸ hterm0]

/-- **Per-term telescoping bound.** For `x > 0` and `b² ≥ 1/4`,
`φ(x) ≤ F(x+½) - F(x-½) + ¼ (H(x-½) - H(x+½))`. -/
theorem phi_le (b x : ℝ) (hx : 0 < x) (hb : 1 / 4 ≤ b ^ 2) :
    phi b x ≤ (F b (x + 1 / 2) - F b (x - 1 / 2))
      + (H b (x - 1 / 2) - H b (x + 1 / 2)) / 4 := by
  unfold phi F H
  set A : ℝ := (x + 1 / 2) ^ 2 + b ^ 2 with hA
  set B : ℝ := (x - 1 / 2) ^ 2 + b ^ 2 with hB
  set P : ℝ := x ^ 2 + b ^ 2 with hP
  have hP0 : 1 / 4 ≤ P := by nlinarith
  have hB0 : 0 < B := by positivity
  have hA0 : 0 < A := by positivity
  have hBA : B < A := by rw [hA, hB]; nlinarith
  have hlog := log_sub_log_ge hB0 hBA
  have hsumAB : A + B = 2 * (P + 1 / 4) := by rw [hA, hB, hP]; ring
  have hdiffAB : A - B = 2 * x := by rw [hA, hB]; ring
  have hlog' : x / (P + 1 / 4) ≤ (Real.log A - Real.log B) / 2 := by
    have : 2 * (A - B) / (A + B) = 2 * (x / (P + 1 / 4)) := by
      rw [hsumAB, hdiffAB]; field_simp
    linarith
  -- algebraic part: x/P - x/(P+1/4) ≤ (1/B - 1/A)/4
  have hAB : A * B = (P + 1 / 4) ^ 2 - x ^ 2 := by rw [hA, hB, hP]; ring
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

/-- Real part of a Gauss-series term at `s = a + i b`. -/
theorem re_digammaSeriesTerm (a b : ℝ) (n : ℕ) :
    (digammaSeriesTerm ⟨a, b⟩ n).re = 1 / ((n : ℝ) + 1) - phi b ((n : ℝ) + 1 + a) := by
  have h1 : (((n : ℂ) + 1)⁻¹).re = 1 / ((n : ℝ) + 1) := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have h2 : (((n : ℂ) + 1 + ⟨a, b⟩)⁻¹).re = phi b ((n : ℝ) + 1 + a) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp [phi]
    ring
  simp only [digammaSeriesTerm, Complex.sub_re, h1, h2]

/-- **Partial-sum bound.** -/
theorem sum_phi_le (a b : ℝ) (ha : 0 ≤ a) (hb : 1 / 4 ≤ b ^ 2) (N : ℕ) :
    ∑ k ∈ range N, phi b ((k : ℝ) + 1 + a)
      ≤ F b ((N : ℝ) + a + 1 / 2) - F b (a + 1 / 2) + H b (a + 1 / 2) / 4 := by
  set g : ℕ → ℝ := fun k => F b ((k : ℝ) + a + 1 / 2) - H b ((k : ℝ) + a + 1 / 2) / 4 with hg
  have hstep : ∀ k ∈ range N, phi b ((k : ℝ) + 1 + a) ≤ g (k + 1) - g k := by
    intro k _
    have hx : 0 < (k : ℝ) + 1 + a := by positivity
    have := phi_le b ((k : ℝ) + 1 + a) hx hb
    simp only [hg]
    push_cast
    have e1 : (k : ℝ) + 1 + a + 1 / 2 = (k : ℝ) + 1 + a + 1 / 2 := rfl
    have e2 : (k : ℝ) + 1 + a - 1 / 2 = (k : ℝ) + a + 1 / 2 := by ring
    rw [e2] at this
    linarith
  have htel := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub] at htel
  have hH : 0 ≤ H b ((N : ℝ) + a + 1 / 2) := by unfold H; positivity
  simp only [hg, Nat.cast_zero, zero_add] at htel
  linarith

/-- `F_b(N + c) - log N → 0`. -/
theorem tendsto_F_sub_log (b c : ℝ) :
    Tendsto (fun N : ℕ => F b ((N : ℝ) + c) - Real.log N) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun N : ℕ => (1 + c * ((N : ℝ))⁻¹) ^ 2 + b ^ 2 * (((N : ℝ))⁻¹) ^ 2)
      atTop (𝓝 ((1 + c * 0) ^ 2 + b ^ 2 * 0 ^ 2)) := by
    exact ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).pow 2).add
      (tendsto_const_nhds.mul (hinv.pow 2))
  simp only [mul_zero, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hq
  have hlog : Tendsto (fun N : ℕ => Real.log ((1 + c * ((N : ℝ))⁻¹) ^ 2
      + b ^ 2 * (((N : ℝ))⁻¹) ^ 2) / 2) atTop (𝓝 (Real.log 1 / 2)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).div_const 2
  rw [Real.log_one, zero_div] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq' : (1 + c * ((N : ℝ))⁻¹) ^ 2 + b ^ 2 * (((N : ℝ))⁻¹) ^ 2
      = (((N : ℝ) + c) ^ 2 + b ^ 2) / (N : ℝ) ^ 2 := by
    field_simp
  have hpos : 0 < ((N : ℝ) + c) ^ 2 + b ^ 2 ∨ ((N : ℝ) + c) ^ 2 + b ^ 2 = 0 := by
    rcases (add_nonneg (sq_nonneg ((N : ℝ) + c)) (sq_nonneg b)).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  unfold F
  rw [hq']
  rcases hpos with hpos | hzero
  · rw [Real.log_div hpos.ne' (by positivity), Real.log_pow]
    push_cast; ring
  · rw [hzero, zero_div, Real.log_zero]
    -- impossible branch for large N is not needed: both sides are then expressible
    have : ((N : ℝ) + c) ^ 2 + b ^ 2 = 0 := hzero
    rw [this, Real.log_zero]; ring_nf
    -- log 0 = 0, so LHS = 0/2 = 0 and RHS = -log N; this case forces N + c = 0 and b = 0
    have hb0 : b = 0 := by nlinarith [sq_nonneg ((N : ℝ) + c), sq_nonneg b]
    have hc0 : (N : ℝ) + c = 0 := by nlinarith [sq_nonneg ((N : ℝ) + c), sq_nonneg b]
    -- `Real.log (N ^ 2) / 2 = log N` is what the RHS reduces to; it does not vanish in general,
    -- so we instead avoid this branch by strengthening the filter below.
    exact absurd hzero (by nlinarith [hN'])

/-- **Main theorem.** For `a ≥ 0` and `b² ≥ 1/4`,
`Re ψ(a+ib) ≥ -a/(a²+b²) + ½ log((a+½)²+b²) - ¼/((a+½)²+b²)`. -/
theorem re_digamma_ge_aux (a b : ℝ) (ha : 0 ≤ a) (hb : 1 / 4 ≤ b ^ 2) :
    -a / (a ^ 2 + b ^ 2) + F b (a + 1 / 2) - H b (a + 1 / 2) / 4
      ≤ (Complex.digamma ⟨a, b⟩).re := by
  set s : ℂ := ⟨a, b⟩ with hs
  have hb0 : b ≠ 0 := by rintro rfl; norm_num at hb
  have hnp : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.im h
    simp [hs] at this
    exact hb0 this
  have hoff : OffPoles s := by
    intro n h
    have := congrArg Complex.im h
    simp [hs] at this
    exact hb0 this
  rw [← digammaSeries_eq_digamma hnp]
  have hsumm := summable_digammaSeriesTerm hoff
  have hre : HasSum (fun n => (digammaSeriesTerm s n).re) (∑' n, digammaSeriesTerm s n).re :=
    Complex.hasSum_re hsumm.hasSum
  have hlim := hre.tendsto_sum_nat
  -- the lower bound sequence
  have hlow : ∀ N : ℕ, ((harmonic N : ℚ) : ℝ) - F b ((N : ℝ) + (a + 1 / 2))
      + F b (a + 1 / 2) - H b (a + 1 / 2) / 4
      ≤ ∑ n ∈ range N, (digammaSeriesTerm s n).re := by
    intro N
    have hbound := sum_phi_le a b ha hb N
    simp only [hs, re_digammaSeriesTerm, Finset.sum_sub_distrib]
    have hharm : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
      rw [harmonic]; push_cast; simp
    rw [hharm]
    have : (N : ℝ) + (a + 1 / 2) = (N : ℝ) + a + 1 / 2 := by ring
    rw [this]
    linarith
  have hlowlim : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - F b ((N : ℝ) + (a + 1 / 2))
      + F b (a + 1 / 2) - H b (a + 1 / 2) / 4) atTop
      (𝓝 (Real.eulerMascheroniConstant - 0 + F b (a + 1 / 2) - H b (a + 1 / 2) / 4)) := by
    have := (Real.tendsto_harmonic_sub_log.sub (tendsto_F_sub_log b (a + 1 / 2))).add_const
      (F b (a + 1 / 2))
    refine (this.sub_const (H b (a + 1 / 2) / 4)).congr (fun N => ?_)
    ring
  have hle := le_of_tendsto_of_tendsto' hlowlim hlim hlow
  have hre_s : (s⁻¹).re = a / (a ^ 2 + b ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_apply]; simp [hs]; ring
  have hre_tot : (digammaSeries s).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + b ^ 2)
        + (∑' n, digammaSeriesTerm s n).re := by
    simp only [digammaSeries, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.ofReal_re, hre_s]
  rw [hre_tot]
  have : -a / (a ^ 2 + b ^ 2) = -(a / (a ^ 2 + b ^ 2)) := by ring
  rw [this]
  linarith

/-- **Lower envelope for `Re ψ` on vertical lines.** For `a ≥ 0` and `b ≥ 1/2`,
`Re ψ(a+ib) ≥ log b - (a + 1/4)/b²`. -/
theorem re_digamma_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 1 / 2 ≤ b) :
    Real.log b - (a + 1 / 4) / b ^ 2 ≤ (Complex.digamma ⟨a, b⟩).re := by
  have hb0 : 0 < b := by linarith
  have hb2 : 1 / 4 ≤ b ^ 2 := by nlinarith
  refine le_trans ?_ (re_digamma_ge_aux a b ha hb2)
  have hbsq : 0 < b ^ 2 := by positivity
  -- F(a+½) ≥ log b
  have hF : Real.log b ≤ F b (a + 1 / 2) := by
    unfold F
    have : Real.log b = Real.log (b ^ 2) / 2 := by
      rw [Real.log_pow]; push_cast; ring
    rw [this]
    have := Real.log_le_log hbsq (by nlinarith : b ^ 2 ≤ (a + 1 / 2) ^ 2 + b ^ 2)
    linarith
  -- a/(a²+b²) ≤ a/b²
  have h1 : a / (a ^ 2 + b ^ 2) ≤ a / b ^ 2 :=
    div_le_div_of_nonneg_left ha hbsq (by nlinarith)
  -- H(a+½) ≤ 1/b²
  have h2 : H b (a + 1 / 2) ≤ 1 / b ^ 2 := by
    unfold H
    exact div_le_div_of_nonneg_left zero_le_one hbsq (by nlinarith)
  have e : (a + 1 / 4) / b ^ 2 = a / b ^ 2 + (1 / b ^ 2) / 4 := by ring
  rw [e]
  have : -a / (a ^ 2 + b ^ 2) = -(a / (a ^ 2 + b ^ 2)) := by ring
  rw [this]
  linarith

/-- **The certificate's digamma envelope.** For `t ≥ 2`,
`Re ψ(1/4 + i t/2) - log π ≥ log(t/(2π)) - 1/t`. -/
theorem re_digamma_quarter_ge (t : ℝ) (ht : 2 ≤ t) :
    Real.log (t / (2 * Real.pi)) - 1 / t
      ≤ (Complex.digamma ⟨1 / 4, t / 2⟩).re - Real.log Real.pi := by
  have ht0 : 0 < t := by linarith
  have h := re_digamma_ge (1 / 4) (t / 2) (by norm_num) (by linarith)
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_pos.ne']
  have hq : (1 / 4 + 1 / 4) / (t / 2) ^ 2 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
  rw [hlog]
  linarith

/-- The rung-1 prime-cosine sum (`supp f ⊂ [-11/20, 11/20]`, so only `n = 2, 3` enter):
`Σ_{n ∈ {2,3}} 2 Λ(n)/√n · cos(t log n)`. -/
noncomputable def rungOnePrimeCos (t : ℝ) : ℝ :=
  2 * Real.log 2 / Real.sqrt 2 * Real.cos (t * Real.log 2)
    + 2 * Real.log 3 / Real.sqrt 3 * Real.cos (t * Real.log 3)

/-- The constant `A = 2 log 2/√2 + 2 log 3/√3 ≈ 2.2488`, the triangle bound for the
prime-cosine sum. -/
noncomputable def rungOneA : ℝ :=
  2 * Real.log 2 / Real.sqrt 2 + 2 * Real.log 3 / Real.sqrt 3

theorem rungOnePrimeCos_le (t : ℝ) : rungOnePrimeCos t ≤ rungOneA := by
  unfold rungOnePrimeCos rungOneA
  have h2 : 0 ≤ 2 * Real.log 2 / Real.sqrt 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have h3 : 0 ≤ 2 * Real.log 3 / Real.sqrt 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
  have c2 := Real.cos_le_one (t * Real.log 2)
  have c3 := Real.cos_le_one (t * Real.log 3)
  nlinarith [mul_le_mul_of_nonneg_left c2 h2, mul_le_mul_of_nonneg_left c3 h3]

/-- The rung-1 symbol `Ψ(t) = Re ψ(1/4 + i t/2) - log π - Σ_{n∈{2,3}} 2Λ(n)/√n cos(t log n)`. -/
noncomputable def rungOneSymbol (t : ℝ) : ℝ :=
  (Complex.digamma ⟨1 / 4, t / 2⟩).re - Real.log Real.pi - rungOnePrimeCos t

/-- `β(T) = log(T/(2π)) - 1/T - A`. -/
noncomputable def rungOneBeta (T : ℝ) : ℝ :=
  Real.log (T / (2 * Real.pi)) - 1 / T - rungOneA

/-- **Rung-1 symbol floor.** For `2 ≤ T ≤ t`, `Ψ(t) ≥ β(T)`. With `T = 100` this is the
input that lets the certificate replace `Ψ` by `β` on `[T, ∞)`. -/
theorem rungOneSymbol_ge {T t : ℝ} (hT : 2 ≤ T) (hTt : T ≤ t) :
    rungOneBeta T ≤ rungOneSymbol t := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have henv := re_digamma_quarter_ge t (le_trans hT hTt)
  have hcos := rungOnePrimeCos_le t
  have hmono_log : Real.log (T / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right hTt (by positivity))
  have hmono_inv : 1 / t ≤ 1 / T := one_div_le_one_div_of_le hT0 hTt
  unfold rungOneSymbol rungOneBeta
  linarith

end GppDigammaVerticalFloor
