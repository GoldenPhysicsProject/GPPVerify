import GppVerify.RiemannHypothesis.TwoSpaceForm
import GppVerify.RiemannHypothesis.RungZeroPositivity

/-!
# (O1): `B_N ≥ [θ(N) + κ_L] ‖f‖²`, and `B_N ≥ 0` at admissible cutoffs with `θ(N) + κ_L ≥ 0`

Obligation (O1) of the two-positive-space form of OB-6 (bridge `c11a2d9`; Turbo's sequencing at `b60da44`).
For a test function `f` supported in `[−L/2, L/2]` and `A = f ⋆ f̃`:

* **Pole bound** `poleTerm A ≥ (L − 2 sinh(L/2)) ‖f‖²` (`poleTerm_autocorr_ge_wide`). By the exact identity
  `poleTerm A = 2[(∫ f cosh(u/2))² − (∫ f sinh(u/2))²]` (`poleTerm_autocorr_eq`, from the in-tree transform
  identity `ĝ_A(s) = ĝ(s) ĝ(1−s)` at `s = 1` and `s = 0`) and the *exact* Cauchy–Schwarz constant
  `∫_{−L/2}^{L/2} sinh²(u/2) du = sinh(L/2) − L/2`.
* **Archimedean floor** `archimedeanTerm A ≥ C_∞ ‖f‖²` (`archimedeanTerm_autocorr_floor`): the in-tree
  `archimedean_floor` applied to `r = A/‖f‖²`, with the in-tree integrability
  (`RungZeroPositivity.integrableOn_archimedeanIntegrand`). No support hypothesis.
* **`BNform_ge`**: `(θ(N) + κ_L) ‖f‖² ≤ B_N(f)`, `κ_L = C_∞ + L − 2 sinh(L/2)`; and `κ_L ≤ C_∞ < 0`
  (`kappa_le_floor`, `archimedeanFloor_neg`).
* **`BNform_nonneg`**: `B_N(f) ≥ 0` whenever `θ(N) + κ_L ≥ 0`.
* **`exists_cutoff_nonneg`**: for every width `L` there is `N₀` with, for all `N ≥ N₀`, `L < log(N+1)` *and*
  `θ(N) + κ_L ≥ 0` — per fixed width only.

**Obligations:** the resolvent identification (O2); contractivity (O3 = `OB6At`, OPEN).
No `sorry`, no axiom.
-/

open MeasureTheory Set
open GppArithmeticReflection GppArchimedeanFloor GppRungZeroPositivity GppMeyerSpectralWeil
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

/-! ### The archimedean floor for an autocorrelation -/

/-- **`archimedeanTerm (f ⋆ f̃) ≥ C_∞ ‖f‖²`**, for every test function (no support hypothesis). -/
theorem archimedeanTerm_autocorr_floor {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    archimedeanFloor * autocorr f 0 ≤ archimedeanTerm (autocorr f) := by
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr ⟨hf, hc⟩
  have ha0 := autocorr_zero_nonneg f
  rcases ha0.lt_or_eq with hpos | hzero
  · set r : ℝ → ℝ := fun u => a u / a 0 with hr
    have hr0 : r 0 = 1 := by simp only [hr]; exact div_self hpos.ne'
    have hrle : ∀ u, 0 < u → r u ≤ 1 := by
      intro u _; simp only [hr]
      rw [div_le_one hpos]; exact (le_abs_self _).trans (abs_autocorr_le hf hc u)
    have hscale : ∀ u, archimedeanIntegrand a u = a 0 * archimedeanIntegrand r u := by
      intro u; unfold archimedeanIntegrand; simp only [hr]; field_simp
      rw [mul_div_mul_left _ _ hpos.ne']
    have hintA := integrableOn_archimedeanIntegrand hta.1 hta.2
    have hintR : IntegrableOn (archimedeanIntegrand r) (Ioi 0) := by
      have h' : IntegrableOn (fun u => archimedeanIntegrand a u / a 0) (Ioi 0) :=
        hintA.div_const _
      refine h'.congr_fun (fun u _ => ?_) measurableSet_Ioi
      show archimedeanIntegrand a u / a 0 = archimedeanIntegrand r u
      rw [hscale, mul_div_cancel_left₀ _ hpos.ne']
    have harch : archimedeanTerm a = a 0 * archimedeanTerm r := by
      unfold archimedeanTerm
      simp only [hscale, integral_const_mul, hr0]
      simp only [hr]; field_simp
    have hfl := archimedean_floor r hr0 hrle hintR
    rw [harch]
    calc archimedeanFloor * a 0 ≤ archimedeanTerm r * a 0 := mul_le_mul_of_nonneg_right hfl hpos.le
      _ = a 0 * archimedeanTerm r := mul_comm _ _
  · have hzero' : ∀ u, a u = 0 := fun u => by
      have := abs_autocorr_le hf hc u
      rw [← hzero] at this
      exact abs_nonpos_iff.mp this
    have : archimedeanTerm a = 0 := by
      unfold archimedeanTerm archimedeanIntegrand; simp [hzero']
    have h0 : a 0 = 0 := hzero.symm
    rw [this, h0, mul_zero]

/-! ### The pole term -/

/-- **The pole identity.** `poleTerm (f ⋆ f̃) = 2[(∫ f cosh(u/2))² − (∫ f sinh(u/2))²]`. -/
theorem poleTerm_autocorr_eq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    poleTerm (autocorr f) =
      2 * ((∫ y, f y * Real.cosh (y / 2)) ^ 2 - (∫ y, f y * Real.sinh (y / 2)) ^ 2) := by
  have htf : IsTestFunction f := ⟨hf, hc⟩
  set a := autocorr f with ha_def
  have hta : IsTestFunction a := GppAutocorrTransport.isTestFunction_autocorr htf
  have hfc : Continuous f := hf.continuous
  have hac : Continuous a := hta.1.continuous
  -- integrability of the weighted functions
  have hI1 : ∀ w : ℝ → ℝ, Continuous w → Integrable (fun y => f y * w y) := fun w hw =>
    (hfc.mul hw).integrable_of_hasCompactSupport hc.mul_right
  have hIa : ∀ w : ℝ → ℝ, Continuous w → Integrable (fun y => a y * w y) := fun w hw =>
    (hac.mul hw).integrable_of_hasCompactSupport hta.2.mul_right
  have hex : Continuous fun y : ℝ => Real.exp (y / 2) := by fun_prop
  have hen : Continuous fun y : ℝ => Real.exp (-y / 2) := by fun_prop
  -- the four real integrals
  set Pp := ∫ y, f y * Real.exp (y / 2) with hPp
  set Pm := ∫ y, f y * Real.exp (-y / 2) with hPm
  set Qp := ∫ y, a y * Real.exp (y / 2) with hQp
  set Qm := ∫ y, a y * Real.exp (-y / 2) with hQm
  have hST : ∀ (g : ℝ → ℝ) (σ : ℝ), spectralTransform g ((σ : ℂ) + 1 / 2) =
      ((∫ y, g y * Real.exp (σ * y) : ℝ) : ℂ) := by
    intro g σ
    unfold spectralTransform
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [add_sub_cancel_right]
    push_cast
    rfl
  have hQ : Qp = Pp * Pm := by
    have h := GppAutocorrTransport.spectralTransform_autocorr htf ((1 / 2 : ℝ) + 1 / 2 : ℂ)
    have e1 : (((1 / 2 : ℝ) : ℂ) + 1 / 2) = ((1 / 2 : ℝ) : ℂ) + 1 / 2 := rfl
    have e2 : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + 1 / 2) = (((-1 / 2 : ℝ) : ℂ) + 1 / 2) := by
      push_cast; ring
    rw [e2, hST a (1 / 2), hST f (1 / 2), hST f (-1 / 2)] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at h'
    have e3 : ∀ y : ℝ, (1 / 2 : ℝ) * y = y / 2 := fun y => by ring
    have e4 : ∀ y : ℝ, (-1 / 2 : ℝ) * y = -y / 2 := fun y => by ring
    simp only [e3, e4] at h'
    exact h'
  have hQ' : Qm = Pp * Pm := by
    have h := GppAutocorrTransport.spectralTransform_autocorr htf (((-1 / 2 : ℝ) : ℂ) + 1 / 2)
    have e2 : (1 : ℂ) - (((-1 / 2 : ℝ) : ℂ) + 1 / 2) = (((1 / 2 : ℝ) : ℂ) + 1 / 2) := by
      push_cast; ring
    rw [e2, hST a (-1 / 2), hST f (1 / 2), hST f (-1 / 2)] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at h'
    have e3 : ∀ y : ℝ, (1 / 2 : ℝ) * y = y / 2 := fun y => by ring
    have e4 : ∀ y : ℝ, (-1 / 2 : ℝ) * y = -y / 2 := fun y => by ring
    simp only [e3, e4] at h'
    have h'' : Qm = Pm * Pp := h'
    rw [h'']; ring
  -- poleTerm = Qp + Qm
  have hpole : poleTerm a = Qp + Qm := by
    unfold poleTerm
    rw [hQp, hQm, ← integral_add (hIa _ hex) (hIa _ hen)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Real.cosh_eq]
    have : Real.exp (-u / 2) = Real.exp (-(u / 2)) := by rw [neg_div]
    rw [this]; ring
  -- Pp = C + S, Pm = C - S
  have hcosh : Continuous fun y : ℝ => Real.cosh (y / 2) := by fun_prop
  have hsinh : Continuous fun y : ℝ => Real.sinh (y / 2) := by fun_prop
  have hPp' : Pp = (∫ y, f y * Real.cosh (y / 2)) + ∫ y, f y * Real.sinh (y / 2) := by
    rw [hPp, ← integral_add (hI1 _ hcosh) (hI1 _ hsinh)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.cosh_eq, Real.sinh_eq]
    have : Real.exp (-(y / 2)) = Real.exp (-(y / 2)) := rfl
    ring
  have hPm' : Pm = (∫ y, f y * Real.cosh (y / 2)) - ∫ y, f y * Real.sinh (y / 2) := by
    rw [hPm, ← integral_sub (hI1 _ hcosh) (hI1 _ hsinh)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Real.cosh_eq, Real.sinh_eq]
    have : Real.exp (-y / 2) = Real.exp (-(y / 2)) := by rw [neg_div]
    rw [this]; ring
  rw [hpole, hQ, hQ', hPp', hPm']
  ring

/-! ### The exact Cauchy–Schwarz constant -/

/-- `∫_{−L/2}^{L/2} sinh²(u/2) du = sinh(L/2) − L/2`. -/
theorem integral_sinh_sq (L : ℝ) :
    ∫ y in (-(L / 2))..(L / 2), Real.sinh (y / 2) ^ 2 = Real.sinh (L / 2) - L / 2 := by
  have h1 : ∀ y : ℝ, Real.sinh (y / 2) ^ 2 = (Real.cosh y - 1) / 2 := by
    intro y
    have h2 := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring] at h2
    nlinarith [Real.cosh_sq (y / 2)]
  simp_rw [h1]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Real.continuous_cosh.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Real.hasDerivAt_sinh x)
      (Real.continuous_cosh.intervalIntegrable _ _)]
  simp [Real.sinh_neg]
  ring

/-- A function vanishing for `|y| > a` integrates over `ℝ` as over `[−a, a]`. -/
theorem integral_eq_interval {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ y : ℝ, a < |y| → φ y = 0) :
    ∫ y, φ y = ∫ y in (-a)..a, φ y := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => h y ?_)
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact hy

/-- **Cauchy–Schwarz with the exact constant.** For continuous `f` vanishing for `|y| > L/2`:
`(∫ f sinh(y/2))² ≤ (∫ f²) · (sinh(L/2) − L/2)`. -/
theorem sinh_cauchy_schwarz {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ y : ℝ, L / 2 < |y| → f y = 0) :
    (∫ y, f y * Real.sinh (y / 2)) ^ 2 ≤ (∫ y, f y ^ 2) * (Real.sinh (L / 2) - L / 2) := by
  have ha : 0 ≤ L / 2 := by linarith
  have hS : ∫ y, f y * Real.sinh (y / 2) = ∫ y in (-(L / 2))..(L / 2), f y * Real.sinh (y / 2) :=
    integral_eq_interval ha (fun y hy => by rw [hs y hy, zero_mul])
  have hA : ∫ y, f y ^ 2 = ∫ y in (-(L / 2))..(L / 2), f y ^ 2 :=
    integral_eq_interval ha (fun y hy => by rw [hs y hy]; ring)
  rw [hS, hA, ← integral_sinh_sq L]
  have hc1 : Continuous fun y : ℝ => f y ^ 2 := hf.pow 2
  have hc2 : Continuous fun y : ℝ => f y * Real.sinh (y / 2) := hf.mul (by fun_prop)
  have hc3 : Continuous fun y : ℝ => Real.sinh (y / 2) ^ 2 := by fun_prop
  have hdisc : discrim (∫ y in (-(L / 2))..(L / 2), f y ^ 2)
      (-2 * ∫ y in (-(L / 2))..(L / 2), f y * Real.sinh (y / 2))
      (∫ y in (-(L / 2))..(L / 2), Real.sinh (y / 2) ^ 2) ≤ 0 := by
    refine discrim_le_zero fun t => ?_
    have hnn : 0 ≤ ∫ y in (-(L / 2))..(L / 2), (t * f y - Real.sinh (y / 2)) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => sq_nonneg _)
    have hexp : ∫ y in (-(L / 2))..(L / 2), (t * f y - Real.sinh (y / 2)) ^ 2 =
        t * t * (∫ y in (-(L / 2))..(L / 2), f y ^ 2)
          + (-2 * (∫ y in (-(L / 2))..(L / 2), f y * Real.sinh (y / 2))) * t
          + ∫ y in (-(L / 2))..(L / 2), Real.sinh (y / 2) ^ 2 := by
      have e : ∀ y : ℝ, (t * f y - Real.sinh (y / 2)) ^ 2 =
          t * t * f y ^ 2 + (-2 * t) * (f y * Real.sinh (y / 2)) + Real.sinh (y / 2) ^ 2 := by
        intro y; ring
      simp_rw [e]
      rw [intervalIntegral.integral_add
        (((hc1.const_mul (t * t)).intervalIntegrable _ _).add
          ((hc2.const_mul (-2 * t)).intervalIntegrable _ _)) (hc3.intervalIntegrable _ _),
        intervalIntegral.integral_add ((hc1.const_mul (t * t)).intervalIntegrable _ _)
          ((hc2.const_mul (-2 * t)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    linarith
  unfold discrim at hdisc
  nlinarith [hdisc]

/-- **The pole bound.** For a test `f` supported in `[−L/2, L/2]`:
`poleTerm (f ⋆ f̃) ≥ (L − 2 sinh(L/2)) ‖f‖²`. -/
theorem poleTerm_autocorr_ge_wide {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {L : ℝ} (hL : 0 ≤ L) (hs : ∀ y : ℝ, L / 2 < |y| → f y = 0) :
    (L - 2 * Real.sinh (L / 2)) * autocorr f 0 ≤ poleTerm (autocorr f) := by
  rw [poleTerm_autocorr_eq hf hc, autocorr_zero_eq]
  have h := sinh_cauchy_schwarz hf.continuous hL hs
  nlinarith [sq_nonneg (∫ y, f y * Real.cosh (y / 2))]

/-- `κ_L = C_∞ + L − 2 sinh(L/2)`. -/
def kappa (L : ℝ) : ℝ := archimedeanFloor + L - 2 * Real.sinh (L / 2)

theorem archimedeanFloor_neg : archimedeanFloor < 0 := by
  unfold archimedeanFloor
  have h1 : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have h2 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have h3 : 0 < Real.pi / 2 := by positivity
  have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem kappa_le_floor {L : ℝ} (hL : 0 ≤ L) : kappa L ≤ archimedeanFloor := by
  unfold kappa
  have : L / 2 ≤ Real.sinh (L / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  linarith

theorem kappa_neg {L : ℝ} (hL : 0 ≤ L) : kappa L < 0 :=
  (kappa_le_floor hL).trans_lt archimedeanFloor_neg

/-- **(O1): `B_N(f) ≥ (θ(N) + κ_L) ‖f‖²`.** -/
theorem BNform_ge {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ y : ℝ, L / 2 < |y| → f y = 0) (N : ℕ) :
    ((∑ p ∈ primesUpTo N, Real.log p) + kappa L) * autocorr f 0 ≤ BNform N f := by
  have h1 := poleTerm_autocorr_ge_wide hf hc hL hs
  have h2 := archimedeanTerm_autocorr_floor hf hc
  unfold BNform massDefectSum kappa
  nlinarith

/-- **`B_N ≥ 0`** at any cutoff with `θ(N) + κ_L ≥ 0`. -/
theorem BNform_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {L : ℝ}
    (hL : 0 ≤ L) (hs : ∀ y : ℝ, L / 2 < |y| → f y = 0) (N : ℕ)
    (hθ : 0 ≤ (∑ p ∈ primesUpTo N, Real.log p) + kappa L) : 0 ≤ BNform N f :=
  (mul_nonneg hθ (autocorr_zero_nonneg f)).trans (BNform_ge hf hc hL hs N)

theorem primesUpTo_mono {N N' : ℕ} (h : N ≤ N') : primesUpTo N ⊆ primesUpTo N' := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- There are arbitrarily many primes `≤ N`, for `N` large. -/
theorem card_primesUpTo_unbounded (k : ℕ) : ∃ N₀ : ℕ, k ≤ (primesUpTo N₀).card := by
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨N₀, hN₀⟩ := ih
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (N₀ + 1)
    refine ⟨p, ?_⟩
    have hsub : insert p (primesUpTo N₀) ⊆ primesUpTo p := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hp⟩
      · exact primesUpTo_mono (by omega) hq
    have hnot : p ∉ primesUpTo N₀ := by
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    omega

/-- `θ(N) = Σ_{p ≤ N} log p` is unbounded. -/
theorem theta_unbounded (M : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, M ≤ ∑ p ∈ primesUpTo N, Real.log p := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_ge (M / Real.log 2)
  obtain ⟨N₀, hN₀⟩ := card_primesUpTo_unbounded k
  refine ⟨N₀, fun N hN => ?_⟩
  have hcard : k ≤ (primesUpTo N).card :=
    hN₀.trans (Finset.card_le_card (primesUpTo_mono hN))
  have hsum : (primesUpTo N).card • Real.log 2 ≤ ∑ p ∈ primesUpTo N, Real.log p := by
    refine Finset.card_nsmul_le_sum _ _ _ (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    exact Real.log_le_log (by norm_num) hp2
  have hk' : (k : ℝ) ≤ ((primesUpTo N).card : ℝ) := by exact_mod_cast hcard
  rw [nsmul_eq_mul] at hsum
  have hM : M ≤ k * Real.log 2 := by
    rw [div_le_iff₀ hl2] at hk; exact hk
  nlinarith

/-- **Admissible cutoffs with `B_N ≥ 0` exist at every width** (per fixed `L`; **no uniformity in `L`**):
for `N ≥ N₀`, `L < log(N+1)` and `θ(N) + κ_L ≥ 0`. -/
theorem exists_cutoff_nonneg (L : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, L < Real.log (N + 1) ∧ 0 ≤ (∑ p ∈ primesUpTo N, Real.log p) + kappa L := by
  obtain ⟨N₁, h₁⟩ := theta_unbounded (-kappa L)
  refine ⟨max N₁ ⌈Real.exp L⌉₊, fun N hN => ⟨?_, ?_⟩⟩
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h1 : Real.exp L ≤ ⌈Real.exp L⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp L⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (le_of_max_le_right hN)
    linarith
  · have := h₁ N (le_of_max_le_left hN)
    linarith

/-- **The operator form of OB-6, with (O1) discharged.** At any admissible `N` with `θ(N) + κ_L ≥ 0`
(these exist at every width, `exists_cutoff_nonneg`), `OB6At L` is exactly the operator inequality
`‖C_N g‖ ≤ √(B_N g)` for the width-`L` tests — contractivity of `C_N` from the `B_N`-seminorm.
Still `OB6At L`: **OPEN**. -/
theorem ob6At_iff_operator_form {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : L < Real.log (N + 1))
    (hθ : 0 ≤ (∑ p ∈ primesUpTo N, Real.log p) + kappa L) :
    OB6At L ↔ ∀ g : ℝ → ℝ, ∀ hg : ContDiff ℝ ∞ g, ∀ hc : HasCompactSupport g,
      (∀ y : ℝ, L / 2 < |y| → g y = 0) →
        ‖CN N hg.continuous hc‖ ≤ Real.sqrt (BNform N g) := by
  rw [ob6At_iff_single_cutoff L N hN]
  refine forall_congr' fun g => forall_congr' fun hg => forall_congr' fun hc =>
    imp_congr_right fun hs => ?_
  exact contraction_iff_norm_le hg.continuous hc (BNform_nonneg hg hc hL hs N hθ)

end GppShiftPresentation

#print axioms GppShiftPresentation.archimedeanTerm_autocorr_floor
#print axioms GppShiftPresentation.BNform_ge
#print axioms GppShiftPresentation.BNform_nonneg
#print axioms GppShiftPresentation.exists_cutoff_nonneg
#print axioms GppShiftPresentation.ob6At_iff_operator_form
