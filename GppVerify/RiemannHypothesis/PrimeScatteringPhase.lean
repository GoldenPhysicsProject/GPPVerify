import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Prime and Archimedean factors as unitary scattering phases

Source: Codex, GPPDiscovery2 `research/2026-09-27_completed_phase_as_su11_scattering_balance.md`,
§§1, 3, 4 (exact local identities).

For `0 ≤ a < 1`, `L : ℝ` set `S_p(T) = (1 − a e^{iTL}) / (1 − a e^{−iTL})`. With `a = p^{−1/2}`
and `L = log p` this is the free-delay-subtracted prime Blaschke channel of the note. This file
proves:
* `norm_Sp`: `|S_p(T)| = 1` for real `T` (numerator and denominator are conjugate).
* `Sp_eq_local_ratio`: for a natural `p > 1`,
  `S_p(T) = (1 − p^{−(1/2 − iT)}) / (1 − p^{−(1/2 + iT)}) = ζ_p(½ + iT) / ζ_p(½ − iT)`,
  with `ζ_p(s) = (1 − p^{−s})⁻¹`.
* `Sp_eq_exp_phase`: `S_p(T) = exp(i φ(T))` with the explicit real phase
  `φ(T) = −2 Σ_{m≥1} aᵐ sin(mTL)/m`.
* `hasDerivAt_phase`: the Wigner–Smith delay is `φ'(T) = −2L Σ_{m≥1} aᵐ cos(mTL)`. With
  `a = p^{−1/2}`, `L = log p` this is `−2 Σ_m Λ(pᵐ) p^{−m/2} cos(T log pᵐ)`, the prime term of the
  explicit formula.
* `norm_Sinf`: the Archimedean factor `S_∞(T) = π^{−iT} Γ(¼ + iT/2) / Γ(¼ − iT/2)` is unimodular
  for real `T`.

**Not formalized:** the zeta-regularized determinant reading of `S_∞` (§2), the renormalized
infinite prime product, and the zero-counting phase quantization (§§6–7). The infinite critical
product does not converge as an ordinary Euler product, as the note itself says. **No RH claim.**
-/

namespace GppPrimeScatteringPhase

open Complex

/-- The free-delay-subtracted local prime scattering phase. -/
noncomputable def Sp (a L T : ℝ) : ℂ :=
  (1 - a * exp (I * (T * L))) / (1 - a * exp (-(I * (T * L))))

theorem norm_exp_I_mul_ofReal (x : ℝ) : ‖exp (I * x)‖ = 1 := by
  rw [mul_comm]; exact norm_exp_ofReal_mul_I x

theorem one_sub_ne_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    1 - (a : ℂ) * exp (I * x) ≠ 0 := by
  intro h
  have hz : (a : ℂ) * exp (I * x) = 1 := (sub_eq_zero.mp h).symm
  have h1 : ‖(a : ℂ) * exp (I * x)‖ = 1 := by rw [hz]; simp
  rw [norm_mul, norm_exp_I_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg ha0] at h1
  linarith

theorem conj_numerator (a x : ℝ) :
    (starRingEnd ℂ) (1 - (a : ℂ) * exp (I * x)) = 1 - a * exp (-(I * x)) := by
  rw [map_sub, map_one, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, neg_mul]

/-- **Unitarity of the prime channel** on the real line. -/
theorem norm_Sp {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L T : ℝ) : ‖Sp a L T‖ = 1 := by
  unfold Sp
  have hx : ((T * L : ℝ) : ℂ) = (T : ℂ) * L := by push_cast; ring
  rw [← hx, ← conj_numerator, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (one_sub_ne_zero ha0 ha1 _))

theorem natCast_cpow_eq {p : ℕ} (hp : 0 < p) (T : ℝ) (σ : ℂ) :
    (p : ℂ) ^ (σ + I * T) = (p : ℂ) ^ σ * exp (I * (T * Real.log p)) := by
  rw [cpow_add _ _ (by exact_mod_cast hp.ne'), cpow_def_of_ne_zero (by exact_mod_cast hp.ne')
    (I * T), ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  push_cast; ring_nf

/-- **The prime phase is the local Euler-factor ratio**:
`S_p(T) = (1 − p^{−(½ − iT)}) / (1 − p^{−(½ + iT)})`, i.e. `ζ_p(½ + iT)/ζ_p(½ − iT)`. -/
theorem Sp_eq_local_ratio {p : ℕ} (hp : 0 < p) (T : ℝ) :
    Sp ((p : ℝ) ^ (-(1 / 2 : ℝ))) (Real.log p) T =
      (1 - (p : ℂ) ^ (-(1 / 2 - I * T))) / (1 - (p : ℂ) ^ (-(1 / 2 + I * T))) := by
  have e1 : -(1 / 2 - I * T) = (-(1 / 2) : ℂ) + I * T := by ring
  have e2 : -(1 / 2 + I * T) = (-(1 / 2) : ℂ) + I * ((-T : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, natCast_cpow_eq hp, natCast_cpow_eq hp]
  have ha : (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (p : ℂ) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  unfold Sp
  rw [ha]
  congr 3
  push_cast; ring_nf

/-- The real phase `φ(T) = −2 Σ_{m≥1} aᵐ sin(mTL)/m`. -/
noncomputable def phase (a L T : ℝ) : ℝ :=
  -2 * ∑' m : ℕ, a ^ (m + 1) * Real.sin ((m + 1) * (T * L)) / (m + 1)

theorem summable_geom_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable fun m : ℕ => a ^ (m + 1) := by
  simpa [pow_succ] using (summable_geometric_of_lt_one ha0 ha1).mul_right a

theorem summable_phase_terms {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    Summable fun m : ℕ => a ^ (m + 1) * Real.sin ((m + 1) * x) / (m + 1) := by
  refine Summable.of_norm_bounded (summable_geom_bound ha0 ha1) fun m => ?_
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ha0 _),
    abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
  rw [div_le_iff₀ (by positivity)]
  have hs := Real.abs_sin_le_one ((m + 1) * x)
  have hp := pow_nonneg ha0 (m + 1)
  nlinarith

theorem log_one_sub_hasSum {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (x : ℝ) :
    HasSum (fun m : ℕ => ((a : ℂ) * exp (I * x)) ^ (m + 1) / (m + 1))
      (-log (1 - (a : ℂ) * exp (I * x))) := by
  apply hasSum_taylorSeries_neg_log'
  rw [norm_mul, norm_exp_I_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg ha0]; linarith

theorem term_diff (a x : ℝ) (m : ℕ) :
    ((a : ℂ) * exp (I * ((-x : ℝ) : ℂ))) ^ (m + 1) / (m + 1)
        - ((a : ℂ) * exp (I * x)) ^ (m + 1) / (m + 1)
      = I * ((-2 * (a ^ (m + 1) * Real.sin ((m + 1) * x) / (m + 1)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_neg, mul_neg, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  rw [Complex.sin]
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- **The prime channel is a pure phase**: `S_p(T) = exp(i φ(T))`. -/
theorem Sp_eq_exp_phase {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L T : ℝ) :
    Sp a L T = exp (I * phase a L T) := by
  set x : ℝ := T * L with hx
  have hx' : ((x : ℝ) : ℂ) = (T : ℂ) * L := by rw [hx]; push_cast; ring
  have h1 := log_one_sub_hasSum ha0 ha1 x
  have h2 := log_one_sub_hasSum ha0 ha1 (-x)
  have hdiff := h2.sub h1
  simp_rw [term_diff] at hdiff
  have hreal : HasSum (fun m : ℕ => -2 * (a ^ (m + 1) * Real.sin ((m + 1) * x) / (m + 1)))
      (phase a L T) := by
    unfold phase; rw [← hx]
    exact ((summable_phase_terms ha0 ha1 x).hasSum).mul_left (-2)
  have hc := (hreal.mapL Complex.ofRealCLM).mul_left I
  have heq : -log (1 - (a : ℂ) * exp (I * ((-x : ℝ) : ℂ))) - -log (1 - (a : ℂ) * exp (I * x))
      = I * (phase a L T : ℂ) := hdiff.unique hc
  rw [Complex.ofReal_neg, mul_neg] at heq
  have n1 := one_sub_ne_zero ha0 ha1 x
  have n2 := one_sub_ne_zero ha0 ha1 (-x)
  rw [Complex.ofReal_neg, mul_neg] at n2
  unfold Sp
  rw [← hx', ← heq, exp_sub, Complex.exp_neg (log (1 - (a : ℂ) * exp (-(I * x)))),
    Complex.exp_neg (log (1 - (a : ℂ) * exp (I * x))), exp_log n1, exp_log n2]
  field_simp

/-- **Wigner–Smith delay of the prime channel**: `φ'(T) = −2L Σ_{m≥1} aᵐ cos(mTL)`. -/
theorem hasDerivAt_phase {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L T : ℝ) :
    HasDerivAt (phase a L)
      (-2 * L * ∑' m : ℕ, a ^ (m + 1) * Real.cos ((m + 1) * (T * L))) T := by
  have hd : ∀ (m : ℕ) (y : ℝ), HasDerivAt
      (fun z : ℝ => a ^ (m + 1) * Real.sin ((m + 1) * (z * L)) / (m + 1))
      (L * (a ^ (m + 1) * Real.cos ((m + 1) * (y * L)))) y := by
    intro m y
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    have h := (((hasDerivAt_id y).mul_const L).const_mul ((m : ℝ) + 1)).sin
    have h2 := (h.const_mul (a ^ (m + 1))).div_const ((m : ℝ) + 1)
    refine h2.congr_deriv ?_
    simp only [id]
    field_simp
  have hb : ∀ (m : ℕ) (y : ℝ), ‖L * (a ^ (m + 1) * Real.cos ((m + 1) * (y * L)))‖
      ≤ |L| * a ^ (m + 1) := by
    intro m y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ha0 _)]
    have hc := Real.abs_cos_le_one ((m + 1) * (y * L))
    have hp := pow_nonneg ha0 (m + 1)
    have hL := abs_nonneg L
    calc |L| * (a ^ (m + 1) * |Real.cos ((m + 1) * (y * L))|) ≤ |L| * (a ^ (m + 1) * 1) := by
          gcongr
      _ = |L| * a ^ (m + 1) := by ring
  have hsum := hasDerivAt_tsum ((summable_geom_bound ha0 ha1).mul_left |L|) hd hb
    (summable_phase_terms ha0 ha1 (0 * L)) T
  have := hsum.const_mul (-2)
  unfold phase
  refine this.congr_deriv ?_
  rw [tsum_mul_left]; ring

/-- The Archimedean factor `S_∞(T) = π^{−iT} Γ(¼ + iT/2)/Γ(¼ − iT/2)`. -/
noncomputable def Sinf (T : ℝ) : ℂ :=
  (Real.pi : ℂ) ^ (-(I * T)) * (Gamma (1 / 4 + I * (T / 2)) / Gamma (1 / 4 - I * (T / 2)))

/-- **Unitarity of the Archimedean channel**: `|S_∞(T)| = 1` for real `T`. -/
theorem norm_Sinf (T : ℝ) : ‖Sinf T‖ = 1 := by
  unfold Sinf
  have hconj : (1 / 4 : ℂ) - I * (T / 2) = (starRingEnd ℂ) (1 / 4 + I * (T / 2)) := by
    apply Complex.ext <;> simp [map_ofNat]
  have hne : Gamma (1 / 4 + I * (T / 2)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp)
  rw [hconj, Complex.Gamma_conj, norm_mul, norm_div, Complex.norm_conj, div_self
    (norm_ne_zero_iff.mpr hne), mul_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp

end GppPrimeScatteringPhase
