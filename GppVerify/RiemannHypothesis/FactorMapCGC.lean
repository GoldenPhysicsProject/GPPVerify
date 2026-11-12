import GppVerify.RiemannHypothesis.ZetaFactorMap
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# FactorMapCGC: the one-prime obstruction and the controls (Astra Theorems 3/5, §7)

Turbo, GPP-bridge PR #11 issuecomment-6807334824, item 2 (c) and (e). Source: Astra,
`work/2026-11-11_astra_completed_kernel_local_factor_obstruction.md`, audited by Flint
(GPPDiscovery3 `research/flint_astra_factor_map_audit_2026_11_11.md`). Items (a), (b) and the
proved part of (d) are in `ZetaFactorMap` (typed class (9), signed assembly, CGC as named Props,
(5), (7)/Prop 2, (14), `cgc_iff_arp`, `cgc_iff_obligation`, `obligation_of_positiveFactor`).

**(c) The one-prime obstruction.**
* `prime2_witness_pointwise`, `prime2_witness_signed`, `prime2_witness_negative` (Theorem 5,
  first window): with `f_b = b + b(· - log 2)`, `2R < log 3`, `supp b ⊂ (-R, R - log 2)`, the
  prime-2 channel (7) gives `∫_I (P f_b)² - ∫_I (C f_b)² = -2 w_{2,1} ∫_I b²`, strictly negative
  when `∫_I b² > 0`: the prime sector alone carries a negative direction. `fb_mem_window`:
  `f_b` is a window-`R` test. PROVED.
* `no_class9_of_negativeFamilies` (Theorem 3, the finite-repair step): if the local form at a
  place is negative definite on linear families of every finite dimension in `𝒟_R`, then no
  class-(9) factor exists there (kernel of the `m + n` constraint/finite-rank coordinates on an
  `(m+n+1)`-dimensional family is nonzero). PROVED.
* `Eq10NegativeIndex p R`: Astra's (10) in the form Theorem 3 uses, as a named obligation with
  its exact content (negative families of every dimension for `Q_p = W_fin p ∘ autocorr`).
  GAP in Lean (paper level: `Q_p(f_b) = -2 (log p) p^{-1/2} ‖b‖²`).
  `OnePrimeObstruction` (exact statement of Theorem 3 on windows with `log p < 2R`) and
  `onePrimeObstruction_of_eq10`, `not_placewise_of_eq10`: PROVED from (10).

**(e) The controls.**
* F_θ fails at local unitarity: `ftheta_trace_gt_two` (`p^θ + p^{-θ} > 2` for `p > 1`, `θ ≠ 0`),
  `unitary2_trace_norm_le` (`|tr U| ≤ 2` for `U ∈ U(2)`), `ftheta_not_unitary`. PROVED.
* Davenport–Heilbronn fails at Euler locality: `dhCoeff κ` with `χ mod 5`, `χ(2) = i`;
  `dhCoeff_two/three/six` (`κ, -κ, 1`), `dh_not_multiplicative` (`a₆ ≠ a₂a₃`, every real `κ`),
  `dh_logDeriv_six` (any `c` satisfying the Dirichlet-convolution relation
  `a(n) log n = Σ_{d∣n} c(d) a(n/d)` at `n = 2, 3, 6` with `c 1 = 0` has
  `c 6 = (1 + κ²) log 6 ≠ 0`), `six_not_primePow`, `vonMangoldt_six` (`Λ 6 = 0`: no Euler-local
  channel at `n = 6`). PROVED. (κ is left a real parameter; its functional-equation value is not
  used.)

Labels: everything above PROVED except `Eq10NegativeIndex` (GAP, named, real content) and the
existence of a bump `b` with `∫_I b² > 0` (standard, not formalized here; the negativity theorem
takes it as a hypothesis). The converse CGC ⇒ positive factor (Astra Theorem 4 1⇒2⇒3,
with dilation and shadow compatibility): paper level. **CGC OPEN; ARP OPEN; RH OPEN.** No `sorry`, no
axiom declarations.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok,
GPPDiscovery5 seat, typed and proved; Astra's note supplies the statements; Flint audited them;
Turbo specified the task and audits).
-/

open MeasureTheory Complex
open scoped ContDiff
open GppZetaFactorMap GlobalTate.Weil

namespace GppFactorMapCGC

/-! ### (c) Theorem 5, first window: the prime sector alone has a negative direction -/

theorem wpk21_pos : 0 < wpk 2 1 := by
  unfold wpk
  exact mul_pos (Real.log_pos (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)

/-- `f_b = b + b(· - log 2)` is a window-`R` test when `b` is smooth with
`supp b ⊂ (-R, R - log 2)`. PROVED. -/
theorem fb_mem_window {R : ℝ} {b : ℝ → ℝ} (hbs : ContDiff ℝ ∞ b)
    (hb : Function.support b ⊆ Set.Ioo (-R) (R - Real.log 2)) :
    (fun x => b x + b (x - Real.log 2)) ∈ windowTests R := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsh : ContDiff ℝ ∞ (fun x => b (x - Real.log 2)) :=
    hbs.comp (contDiff_id.sub contDiff_const)
  refine ⟨hbs.add hsh, fun x hx => ?_⟩
  by_cases h : b x = 0
  · have h2 : b (x - Real.log 2) ≠ 0 := by
      intro h'; exact hx (by simp [h, h'])
    have := hb h2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have := hb h
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Pointwise signed identity for the witness (from (14)). PROVED. -/
theorem prime2_witness_pointwise {R : ℝ} (hR : 2 * R < Real.log 3) {b : ℝ → ℝ}
    (hb : Function.support b ⊆ Set.Ioo (-R) (R - Real.log 2)) {u : ℝ}
    (hu : u ∈ channelWindow R (apk 2 1)) :
    (primeP (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2 -
      (primeC (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2 =
        -(2 * wpk 2 1) * b u ^ 2 := by
  obtain ⟨h1, h2⟩ := first_window_eq14 hR hb hu
  rw [h1, h2, mul_pow, Real.sq_sqrt (by linarith [wpk21_pos])]
  ring

/-- **Theorem 5, signed form**: `∫_I (P f_b)² - ∫_I (C f_b)² = -2 w_{2,1} ∫_I b²`
(the difference integrated). PROVED. -/
theorem prime2_witness_signed {R : ℝ} (hR : 2 * R < Real.log 3) {b : ℝ → ℝ}
    (hb : Function.support b ⊆ Set.Ioo (-R) (R - Real.log 2)) :
    ∫ u in channelWindow R (apk 2 1),
        ((primeP (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2 -
          (primeC (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2) =
      -(2 * wpk 2 1) * ∫ u in channelWindow R (apk 2 1), b u ^ 2 := by
  rw [← integral_const_mul]
  exact setIntegral_congr_fun (by unfold channelWindow; exact measurableSet_Icc)
    (fun u hu => prime2_witness_pointwise hR hb hu)

/-- **The prime sector alone carries a negative direction.** PROVED. -/
theorem prime2_witness_negative {R : ℝ} (hR : 2 * R < Real.log 3) {b : ℝ → ℝ}
    (hb : Function.support b ⊆ Set.Ioo (-R) (R - Real.log 2))
    (hpos : 0 < ∫ u in channelWindow R (apk 2 1), b u ^ 2) :
    ∫ u in channelWindow R (apk 2 1),
        ((primeP (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2 -
          (primeC (wpk 2 1) (apk 2 1) (fun x => b x + b (x - Real.log 2)) u) ^ 2) < 0 := by
  rw [prime2_witness_signed hR hb]
  have := wpk21_pos
  nlinarith

/-! ### (c) Theorem 3: no class-(9) factor at one prime -/

/-- A linear family of dimension `N` in `𝒟_R` on which the local form at `v` is negative
definite. -/
def NegativeFamily (v : Place) (R : ℝ) (N : ℕ) : Prop :=
  ∃ ι : (Fin N → ℝ) →ₗ[ℝ] windowTests R, ∀ x, x ≠ 0 → localForm v (ι x) < 0

/-- **Theorem 3, finite-repair step.** Negative families of every finite dimension exclude a
class-(9) factor: finitely many constraints and a finite-rank repair cannot remove an
infinite negative index. PROVED. -/
theorem no_class9_of_negativeFamilies {v : Place} {R : ℝ} (h : ∀ N, NegativeFamily v R N) :
    IsEmpty (LocalClass9Factor v R) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨ι, hι⟩ := h (F.m + F.n + 1)
  let g : (Fin (F.m + F.n + 1) → ℝ) →ₗ[ℝ] (Fin F.m → ℝ) × (Fin F.n → ℝ) :=
    (F.κ.comp ι).prod (F.lam.comp ι)
  have hk : LinearMap.ker g ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hg : F.κ (ι x) = 0 ∧ F.lam (ι x) = 0 := by
    have := LinearMap.mem_ker.1 hx
    simpa [g, Prod.ext_iff] using this
  have hgram := F.gram (ι x) hg.1
  rw [hg.2] at hgram
  simp only [map_zero, add_zero] at hgram
  have hneg := hι x hx0
  nlinarith [sq_nonneg (@norm F.H F.instN.toNorm (F.A (ι x)))]

/-- **Astra (10), as Theorem 3 uses it** (named obligation, real content): at the prime `p` on
the window `R`, the local form `Q_p = W_fin p ∘ autocorr` is negative definite on linear families
of every finite dimension. Paper level (Astra §4: `f_b = b + b(· - log p)`, `b ∈ C_c^∞(I)`,
`|I| < log p`, `Q_p(f_b, f_c) = -2 (log p) p^{-1/2} ⟨b, c⟩`); Lean: GAP. -/
def Eq10NegativeIndex (p : Nat.Primes) (R : ℝ) : Prop := ∀ N, NegativeFamily (some p) R N

/-- **Theorem 3, exact statement** on windows containing two intervals separated by `log p`:
no class-(9) local factor at any finite place. -/
def OnePrimeObstruction : Prop :=
  ∀ (p : Nat.Primes) (R : ℝ), Real.log p < 2 * R → IsEmpty (LocalClass9Factor (some p) R)

/-- Theorem 3 from (10). PROVED. -/
theorem onePrimeObstruction_of_eq10
    (h : ∀ (p : Nat.Primes) (R : ℝ), Real.log p < 2 * R → Eq10NegativeIndex p R) :
    OnePrimeObstruction :=
  fun p R hR => no_class9_of_negativeFamilies (h p R hR)

/-- No positive direct-sum factor map in class (9), given (10) at one prime and window. PROVED. -/
theorem not_placewise_of_eq10 {p : Nat.Primes} {R : ℝ} (h : Eq10NegativeIndex p R) :
    ¬ PlacewiseClass9Factor := fun hP =>
  (no_class9_of_negativeFamilies h).false (hP (some p) R).some

/-! ### (e) Control 1: F_θ fails at the local unitary parameter -/

/-- `p^θ + p^{-θ} > 2` for `p > 1`, `θ ≠ 0`. PROVED. -/
theorem ftheta_trace_gt_two {p θ : ℝ} (hp : 1 < p) (hθ : θ ≠ 0) :
    2 < p ^ θ + p ^ (-θ) := by
  have hp0 : 0 < p := by linarith
  have h1 : 0 < p ^ θ := Real.rpow_pos_of_pos hp0 θ
  have h2 : p ^ (-θ) = (p ^ θ)⁻¹ := Real.rpow_neg hp0.le θ
  have h3 : p ^ θ ≠ 1 := by
    intro h
    have hl := Real.log_rpow hp0 θ
    rw [h, Real.log_one] at hl
    have : 0 < Real.log p := Real.log_pos hp
    exact hθ (by nlinarith [mul_eq_zero.1 hl.symm |>.resolve_right this.ne'])
  have hx : p ^ θ * (p ^ θ)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  have hsq : 0 < (p ^ θ - 1) ^ 2 := by
    have := sub_ne_zero.2 h3
    positivity
  rw [h2]
  nlinarith [inv_pos.2 h1]

/-- Every `2 × 2` unitary has `|tr U| ≤ 2`. PROVED. -/
theorem unitary2_trace_norm_le (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖U.trace‖ ≤ 2 := by
  rw [Matrix.trace_fin_two]
  calc ‖U 0 0 + U 1 1‖ ≤ ‖U 0 0‖ + ‖U 1 1‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (entry_norm_bound_of_unitary hU 0 0)
        (entry_norm_bound_of_unitary hU 1 1)
    _ = 2 := by norm_num

/-- **F_θ rejected at local unitarity**: no `2 × 2` unitary `V_p` has the trace
`p^θ + p^{-θ}` of F_θ's degree-two local factor (eigenvalues `p^{±θ}`). PROVED. -/
theorem ftheta_not_unitary {p θ : ℝ} (hp : 1 < p) (hθ : θ ≠ 0) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    U.trace ≠ ((p ^ θ + p ^ (-θ) : ℝ) : ℂ) := by
  intro h
  have h1 := unitary2_trace_norm_le U hU
  rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 := ftheta_trace_gt_two hp hθ
  rw [abs_of_pos (by linarith)] at h1
  linarith

/-! ### (e) Control 2: Davenport–Heilbronn fails at Euler locality, coefficient `n = 6` -/

/-- The character mod 5 with `χ(2) = i` (so `χ(3) = -i`, `χ(4) = -1`, `χ(5) = 0`). -/
def chi5 (n : ℕ) : ℂ :=
  if n % 5 = 1 then 1 else if n % 5 = 2 then I else if n % 5 = 3 then -I
  else if n % 5 = 4 then -1 else 0

/-- Davenport–Heilbronn Dirichlet coefficients,
`D = ½(1 - iκ) L(s, χ) + ½(1 + iκ) L(s, χ̄)`, for a real parameter `κ`. -/
noncomputable def dhCoeff (κ : ℝ) (n : ℕ) : ℂ :=
  (1 - I * κ) / 2 * chi5 n + (1 + I * κ) / 2 * (starRingEnd ℂ) (chi5 n)

theorem dhCoeff_one (κ : ℝ) : dhCoeff κ 1 = 1 := by
  simp [dhCoeff, chi5]; ring

theorem dhCoeff_two (κ : ℝ) : dhCoeff κ 2 = κ := by
  simp [dhCoeff, chi5]; ring_nf; simp [Complex.I_sq]

theorem dhCoeff_three (κ : ℝ) : dhCoeff κ 3 = -κ := by
  simp [dhCoeff, chi5]; ring_nf; simp [Complex.I_sq]

theorem dhCoeff_six (κ : ℝ) : dhCoeff κ 6 = 1 := by
  simp [dhCoeff, chi5]; ring

/-- **(16)** `a₆ = 1 ≠ -κ² = a₂ a₃`, for every real `κ`: the coefficients are not multiplicative
at coprime integers, so no normalized Euler product represents `D`. PROVED. -/
theorem dh_not_multiplicative (κ : ℝ) : dhCoeff κ 6 ≠ dhCoeff κ 2 * dhCoeff κ 3 := by
  rw [dhCoeff_six, dhCoeff_two, dhCoeff_three]
  intro h
  have : ((1 + κ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
  have h' : (1 + κ ^ 2 : ℝ) = 0 := by exact_mod_cast this
  nlinarith [sq_nonneg κ]

/-- **(17)** The `n = 6` coefficient of `-D'/D`: any `c` with `c 1 = 0` obeying the
Dirichlet-convolution relation `a(n) log n = Σ_{d ∣ n} c(d) a(n/d)` (that is, `-D' = D·(-D'/D)`)
at `n = 2, 3, 6` has `c 6 = (1 + κ²) log 6`, which is nonzero. PROVED. -/
theorem dh_logDeriv_six (κ : ℝ) (c : ℕ → ℂ) (h1 : c 1 = 0)
    (hrec : ∀ n ∈ ({2, 3, 6} : Finset ℕ),
      dhCoeff κ n * (Real.log n : ℂ) = ∑ d ∈ n.divisors, c d * dhCoeff κ (n / d)) :
    c 6 = ((1 + κ ^ 2) * Real.log 6 : ℝ) ∧ c 6 ≠ 0 := by
  have e2 := hrec 2 (by simp)
  have e3 := hrec 3 (by simp)
  have e6 := hrec 6 (by simp)
  have d2 : Nat.divisors 2 = {1, 2} := by decide
  have d3 : Nat.divisors 3 = {1, 3} := by decide
  have d6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [d2, Finset.sum_pair (by norm_num)] at e2
  rw [d3, Finset.sum_pair (by norm_num)] at e3
  rw [d6, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num)] at e6
  simp only [Nat.reduceDiv, Nat.cast_ofNat, dhCoeff_one, dhCoeff_two, dhCoeff_three,
    dhCoeff_six, h1] at e2 e3 e6
  have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hl6c : ((Real.log 6 : ℝ) : ℂ) = (Real.log 2 : ℂ) + (Real.log 3 : ℂ) := by
    exact_mod_cast hl6
  have hc : c 6 = ((1 + κ ^ 2) * Real.log 6 : ℝ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one]
    linear_combination (-1 : ℂ) * e6 - (κ : ℂ) * e2 + (κ : ℂ) * e3 - (κ : ℂ) ^ 2 * hl6c
  refine ⟨hc, ?_⟩
  rw [hc]
  have : 0 < (1 + κ ^ 2) * Real.log 6 :=
    mul_pos (by positivity) (Real.log_pos (by norm_num))
  exact_mod_cast this.ne'

/-- `6` is not a prime power. PROVED. -/
theorem six_not_primePow : ¬ IsPrimePow 6 := by decide

/-- **Euler locality at `n = 6`**: the von Mangoldt weight, hence every Euler-local channel of
family (7), vanishes at `n = 6`, while `-D'/D` has a nonzero `6^{-s}` coefficient. PROVED. -/
theorem vonMangoldt_six : ArithmeticFunction.vonMangoldt 6 = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.2 six_not_primePow

end GppFactorMapCGC

#print axioms GppFactorMapCGC.fb_mem_window
#print axioms GppFactorMapCGC.prime2_witness_signed
#print axioms GppFactorMapCGC.prime2_witness_negative
#print axioms GppFactorMapCGC.no_class9_of_negativeFamilies
#print axioms GppFactorMapCGC.onePrimeObstruction_of_eq10
#print axioms GppFactorMapCGC.not_placewise_of_eq10
#print axioms GppFactorMapCGC.ftheta_trace_gt_two
#print axioms GppFactorMapCGC.ftheta_not_unitary
#print axioms GppFactorMapCGC.dh_not_multiplicative
#print axioms GppFactorMapCGC.dh_logDeriv_six
#print axioms GppFactorMapCGC.vonMangoldt_six
