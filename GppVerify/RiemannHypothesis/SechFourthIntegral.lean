import GppVerify.RiemannHypothesis.SechSquaredIntegral

/-!
# The eigenstate norm `N_{1/2} = log 2/6 − 1/24` (rh_cesaro_v2, Proposition 5.2)

Thread A2 of `docs/FORMALIZATION_PLAN.md`: the exact value of the Yakaboylu eigenstate
norm at the critical point,

  `N_{1/2} = (1/16) ∫₀^∞ t/cosh⁴(t/2) dt = log 2/6 − 1/24`,

the closed form asserted (without formal proof) in Proposition 5.2 of Toupin's
Abel-Cesàro paper. As with Thread C2, **no series interchange is used**: the `u`-variable
integral `∫₀^∞ u/cosh⁴u du = (2/3)log 2 − 1/6` is computed from an explicit
antiderivative, and the `t`-variable form follows by differentiating `t ↦ 4·F₄(t/2)`
directly — no change-of-variables lemma needed.

The antiderivative is expressed **polynomially in `tanh`** via `tanh' = 1 − tanh²`
(the Pythagorean identity `1/cosh² = 1 − tanh²` is proved once, in `one_div_cosh_sq`, and
everything downstream is pure `ring`):

  `F₄(u) = (1/3)(u·tanh u·(1−tanh²u) + (1−tanh²u)/2) + (2/3)·F(u)`,

where `F` is the `sech²` antiderivative of `SechSquaredIntegral.lean` — so
`F₄(∞) = (2/3)·log 2` reuses `tendsto_sechSqAntideriv_log_two`, and the two new decay
terms are squeezed against `4u·e^{−2u}` and `4e^{−2u}` via the elementary bound
`cosh u ≥ eᵘ/2`.
-/

namespace GppSechIntegral

open Filter MeasureTheory

/-- The Pythagorean bridge `1/cosh²x = 1 − tanh²x`, proved once so that all later
    derivative algebra is polynomial in `tanh`. -/
theorem one_div_cosh_sq (x : ℝ) : 1 / Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `tanh'(x) = 1 − tanh²(x)`: the `tanh`-polynomial form of the derivative. -/
theorem hasDerivAt_tanh' (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := hasDerivAt_tanh x
  rwa [one_div_cosh_sq] at h

/-- The `sech⁴` antiderivative, in `tanh`-polynomial form:
    `F₄(u) = (1/3)(u·tanh u·(1−tanh²u) + (1−tanh²u)/2) + (2/3)·F(u)`. -/
noncomputable def sechFourthAntideriv (u : ℝ) : ℝ :=
  1/3 * (u * Real.tanh u * (1 - Real.tanh u ^ 2) + (1 - Real.tanh u ^ 2) / 2)
    + 2/3 * sechSqAntideriv u

/-- `F₄'(x) = x/cosh⁴(x)` exactly, everywhere. All the algebra is polynomial in `tanh`
    after the single Pythagorean rewrite. -/
theorem hasDerivAt_sechFourthAntideriv (x : ℝ) :
    HasDerivAt sechFourthAntideriv (x / Real.cosh x ^ 4) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have htanh' := hasDerivAt_tanh' x
  have h1 := ((hasDerivAt_id x).mul htanh').mul
    ((hasDerivAt_const x (1 : ℝ)).sub (htanh'.pow 2))
  have h2 := ((hasDerivAt_const x (1 : ℝ)).sub (htanh'.pow 2)).div_const 2
  have hF := ((h1.add h2).const_mul (1/3 : ℝ)).add
    ((hasDerivAt_sechSqAntideriv x).const_mul (2/3 : ℝ))
  have hc4 : x / Real.cosh x ^ 4 = x * (1 - Real.tanh x ^ 2) ^ 2 := by
    rw [← one_div_cosh_sq]
    ring
  have hc2 : x / Real.cosh x ^ 2 = x * (1 - Real.tanh x ^ 2) := by
    rw [← one_div_cosh_sq]
    ring
  convert hF using 1
  rw [hc4, hc2]
  push_cast
  simp only [id_eq]
  ring

/-- `F₄(0) = 1/6`. -/
theorem sechFourthAntideriv_zero : sechFourthAntideriv 0 = 1/6 := by
  show 1/3 * ((0 : ℝ) * Real.tanh 0 * (1 - Real.tanh 0 ^ 2) + (1 - Real.tanh 0 ^ 2) / 2)
      + 2/3 * sechSqAntideriv 0 = 1/6
  rw [Real.tanh_zero, sechSqAntideriv_zero]
  norm_num

/-- The elementary decay bound: `1/cosh²u ≤ 4·e^{−2u}` (in fact for every `u`), from
    `cosh u ≥ eᵘ/2`. -/
theorem one_div_cosh_sq_le (u : ℝ) :
    1 / Real.cosh u ^ 2 ≤ 4 * Real.exp (-(2 * u)) := by
  have hcosh_ge : Real.exp u / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]
    have := (Real.exp_pos (-u)).le
    linarith
  have hc2 : Real.exp u ^ 2 / 4 ≤ Real.cosh u ^ 2 := by
    calc Real.exp u ^ 2 / 4 = (Real.exp u / 2) ^ 2 := by ring
      _ ≤ Real.cosh u ^ 2 := pow_le_pow_left₀ (by positivity) hcosh_ge 2
  have hpos : (0 : ℝ) < Real.exp u ^ 2 / 4 := by positivity
  have hexp2 : Real.exp u ^ 2 = Real.exp (2 * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc 1 / Real.cosh u ^ 2 ≤ 1 / (Real.exp u ^ 2 / 4) :=
        one_div_le_one_div_of_le hpos hc2
    _ = 4 * Real.exp (-(2 * u)) := by
        rw [hexp2, Real.exp_neg, one_div_div, div_eq_mul_inv]

/-- `F₄(u) → (2/3)·log 2` at infinity: the two new terms are squeezed to `0` against
    `4u·e^{−2u}` and `4e^{−2u}`, and the `(2/3)·F` term reuses the `sech²` limit. -/
theorem tendsto_sechFourthAntideriv :
    Tendsto sechFourthAntideriv atTop (nhds (2/3 * Real.log 2)) := by
  have h2u : Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have hnum : Tendsto (fun u : ℝ => (2 * u) ^ 1 * Real.exp (-(2 * u))) atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h2u
  have h4ue : Tendsto (fun u : ℝ => 4 * u * Real.exp (-(2 * u))) atTop (nhds 0) := by
    have heq : ∀ u : ℝ, 2 * ((2 * u) ^ 1 * Real.exp (-(2 * u))) =
        4 * u * Real.exp (-(2 * u)) := fun u => by rw [pow_one]; ring
    have h := hnum.const_mul (2 : ℝ)
    simpa only [mul_zero] using (tendsto_congr heq).mp h
  have hexp : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2u
  have h4e : Tendsto (fun u : ℝ => 4 * Real.exp (-(2 * u))) atTop (nhds 0) := by
    simpa only [mul_zero] using hexp.const_mul (4 : ℝ)
  have hA : Tendsto (fun u : ℝ => u * Real.tanh u * (1 - Real.tanh u ^ 2)) atTop
      (nhds 0) := by
    apply squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun u hu => ?_)
      ((eventually_ge_atTop (0 : ℝ)).mono fun u hu => ?_) h4ue
    · have hs : 0 ≤ Real.sinh u := by
        rw [Real.sinh_eq]
        have := Real.exp_le_exp.mpr (by linarith : -u ≤ u)
        linarith
      have ht0 : 0 ≤ Real.tanh u := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg hs (Real.cosh_pos u).le
      have ht1 : 0 ≤ 1 - Real.tanh u ^ 2 := by
        rw [← one_div_cosh_sq]
        positivity
      exact mul_nonneg (mul_nonneg hu ht0) ht1
    · have hsc : Real.sinh u ≤ Real.cosh u := by
        rw [Real.sinh_eq, Real.cosh_eq]
        have := (Real.exp_pos (-u)).le
        linarith
      have ht1 : Real.tanh u ≤ 1 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact (div_le_one (Real.cosh_pos u)).mpr hsc
      have h1c : (0 : ℝ) ≤ 1 / Real.cosh u ^ 2 := by positivity
      calc u * Real.tanh u * (1 - Real.tanh u ^ 2)
          = u * Real.tanh u * (1 / Real.cosh u ^ 2) := by rw [one_div_cosh_sq]
        _ ≤ u * 1 * (1 / Real.cosh u ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ h1c
            exact mul_le_mul_of_nonneg_left ht1 hu
        _ = u * (1 / Real.cosh u ^ 2) := by ring
        _ ≤ u * (4 * Real.exp (-(2 * u))) :=
            mul_le_mul_of_nonneg_left (one_div_cosh_sq_le u) hu
        _ = 4 * u * Real.exp (-(2 * u)) := by ring
  have hB : Tendsto (fun u : ℝ => (1 - Real.tanh u ^ 2) / 2) atTop (nhds 0) := by
    apply squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun u hu => ?_)
      ((eventually_ge_atTop (0 : ℝ)).mono fun u hu => ?_) h4e
    · have ht1 : 0 ≤ 1 - Real.tanh u ^ 2 := by
        rw [← one_div_cosh_sq]
        positivity
      linarith
    · have ht1 : 0 ≤ 1 - Real.tanh u ^ 2 := by
        rw [← one_div_cosh_sq]
        positivity
      calc (1 - Real.tanh u ^ 2) / 2 ≤ 1 - Real.tanh u ^ 2 := half_le_self ht1
        _ = 1 / Real.cosh u ^ 2 := (one_div_cosh_sq u).symm
        _ ≤ 4 * Real.exp (-(2 * u)) := one_div_cosh_sq_le u
  have hsum := ((hA.add hB).const_mul (1/3 : ℝ)).add
    (tendsto_sechSqAntideriv_log_two.const_mul (2/3 : ℝ))
  have hval : 1/3 * ((0 : ℝ) + 0) + 2/3 * Real.log 2 = 2/3 * Real.log 2 := by ring
  rw [hval] at hsum
  exact hsum

/-- **`∫₀^∞ u/cosh⁴u du = (2/3)·log 2 − 1/6`** — the `u`-variable form
    (`J(1) = (2/3)(log 2 − 1/4)` in the paper's notation). -/
theorem integral_id_div_cosh_fourth :
    ∫ u in Set.Ioi (0 : ℝ), u / Real.cosh u ^ 4 = 2/3 * Real.log 2 - 1/6 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_sechFourthAntideriv 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_sechFourthAntideriv x)
    (fun x hx => div_nonneg (le_of_lt hx) (by positivity))
    tendsto_sechFourthAntideriv
  rw [sechFourthAntideriv_zero] at h
  exact h

/-- The `t`-variable antiderivative `G(t) = 4·F₄(t/2)`, whose derivative is exactly the
    `N_{1/2}` integrand `t/cosh⁴(t/2)` — no change-of-variables lemma needed. -/
noncomputable def tHalfAntideriv (t : ℝ) : ℝ := 4 * sechFourthAntideriv (t / 2)

theorem hasDerivAt_tHalfAntideriv (t : ℝ) :
    HasDerivAt tHalfAntideriv (t / Real.cosh (t/2) ^ 4) t := by
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1/2) t := (hasDerivAt_id t).div_const 2
  have hcomp : HasDerivAt (fun s : ℝ => sechFourthAntideriv (s / 2))
      ((t/2) / Real.cosh (t/2) ^ 4 * (1/2)) t :=
    HasDerivAt.comp (g := sechFourthAntideriv) t
      (hasDerivAt_sechFourthAntideriv (t/2)) hhalf
  have h : HasDerivAt (fun s : ℝ => 4 * sechFourthAntideriv (s / 2))
      (4 * ((t/2) / Real.cosh (t/2) ^ 4 * (1/2))) t := hcomp.const_mul 4
  have hval : 4 * ((t/2) / Real.cosh (t/2) ^ 4 * (1/2)) = t / Real.cosh (t/2) ^ 4 := by
    ring
  rw [← hval]
  exact h

theorem tendsto_tHalfAntideriv :
    Tendsto tHalfAntideriv atTop (nhds (8/3 * Real.log 2)) := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Tendsto.atTop_div_const two_pos tendsto_id
  have hcomp : Tendsto (fun t : ℝ => sechFourthAntideriv (t / 2)) atTop
      (nhds (2/3 * Real.log 2)) := tendsto_sechFourthAntideriv.comp hhalf
  have h := hcomp.const_mul (4 : ℝ)
  have hval : (4 : ℝ) * (2/3 * Real.log 2) = 8/3 * Real.log 2 := by ring
  rw [hval] at h
  exact h

/-- `∫₀^∞ t/cosh⁴(t/2) dt = (8/3)·log 2 − 2/3`. -/
theorem integral_t_div_cosh_half_fourth :
    ∫ t in Set.Ioi (0 : ℝ), t / Real.cosh (t/2) ^ 4 = 8/3 * Real.log 2 - 2/3 := by
  have h0 : tHalfAntideriv 0 = 2/3 := by
    show (4 : ℝ) * sechFourthAntideriv (0 / 2) = 2/3
    rw [show (0 : ℝ) / 2 = 0 by norm_num, sechFourthAntideriv_zero]
    norm_num
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_tHalfAntideriv 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_tHalfAntideriv x)
    (fun x hx => div_nonneg (le_of_lt hx) (by positivity))
    tendsto_tHalfAntideriv
  rw [h0] at h
  exact h

/-- **`N_{1/2} = log 2/6 − 1/24`** (rh_cesaro_v2, Proposition 5.2): the Yakaboylu
    eigenstate norm at the critical point, exactly. -/
theorem eigenstate_norm_half :
    1/16 * ∫ t in Set.Ioi (0 : ℝ), t / Real.cosh (t/2) ^ 4 =
      Real.log 2 / 6 - 1/24 := by
  rw [integral_t_div_cosh_half_fourth]
  ring

end GppSechIntegral
