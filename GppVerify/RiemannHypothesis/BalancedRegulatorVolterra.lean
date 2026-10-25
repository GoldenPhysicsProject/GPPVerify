import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Astra's balanced-regulator Volterra identity

Source: Astra, `work/2026-10-20_astra_balanced_regulator_transfer.md` (GPP-bridge), the
"exact Volterra relation". Daniel Toupin / Golden Physics Project, with AI assistance from Astra
(statement) and Claude Code (formalization).

Astra's regularised signal is `J_e = M_e − C_e`, with
`M_e(t) = 2 Σ_{n ≤ e^t} Λ(n) n^{−e} (n^{−1/2} − e^{−t/2})`, and claims for every `t ≥ 0`
`J_e(t) = e^{−et} J₀(t) + e(1+2e) ∫₀ᵗ e^{−eu} J₀(u) du + e(1−2e) ∫₀ᵗ e^{−(t−u)/2} e^{−eu} J₀(u) du`.

Every piece of `J_e` is a superposition of the **atoms**
`g_{e,s}(t) = e^{−es} · max(e^{−s/2} − e^{−t/2}, 0)` (`atom`). The prime-power cell `n` is
`2Λ(n) g_{e, log n}` (`atom_log`), and the endpoint term `2(1 − e^{−t/2})` is `2 g_{e,0}`.

* `mul_integral_exp`: `c ∫_a^b e^{cu} du = e^{cb} − e^{ca}` for every real `c`, including `0`.
* `volterra_atom`: the Volterra identity holds for each atom `g_{e,s}`, `s ≥ 0`, at every `e`
  and every `t`. There are no exceptional `e`: the coefficients `e(1+2e)` and `e(1−2e)` vanish
  exactly where the antiderivatives degenerate.
* `volterra_sum`: hence it holds for every finite superposition `Σ_k c_k g_{e, s_k}`, and
  `volterra_primeSignal` for each truncation `Σ_{n<N} 2Λ(n) g_{e, log n}` of `M_e`
  (`primeSignal_eq`: it equals `M_e(t)` once `e^t < N`).
* `volterra_cont`: it holds for every continuum superposition `∫₀ᵗ w(s) g_{e,s}(t) ds` with `w`
  continuous and `t ≥ 0` (one Fubini swap on `[0,t]²`). `continuum_eq`: Astra's
  `∫₁^{e^t} (x^{−1/2} − e^{−t/2}) x^{−e} dx` is the case `w = exp` (substitution `x = e^s`).
* `balanced_zero_eq`: at `e = 0`, with `X = e^t`, `J₀(log X) = 2Σ_{n≤X} Λ(n)/√n − 2ψ(X)/√X − 2√X + 2`
  (Astra, `work/2026-10-20_astra_laplace_growth_mobius_audit.md`).
* `volterra_balanced`, with `balanced_eq`: **Astra's identity for `J_e = M_e − C_e` itself**,
  for every `e ∈ ℝ` and `t ≥ 0`, with `M_e` truncated at any `N > e^t` (the truncation does not
  change `M_e` on `[0, t]`).

The identity is exact and holds for every real `e`; the notes' numerical check (15 cases, error
`< 10⁻⁵⁰`) is consistent with it.

**Scope.** Astra's Laplace-side factorization `L_e(z) = [(z+e)(z+e+½)/(z(z+½))] L₀(z+e)`, the
local uniform convergence `J_e → J₀`, and the pole-transfer sufficient condition are not
formalized. Nothing here bears on the location of the zeros, and no claim is made about RH.
-/

open Real intervalIntegral Finset

set_option autoImplicit false

namespace GppBalancedRegulator

/-- The atom `g_{e,s}(t) = e^{−es} max(e^{−s/2} − e^{−t/2}, 0)`. -/
noncomputable def atom (e s t : ℝ) : ℝ := exp (-e * s) * max (exp (-s / 2) - exp (-t / 2)) 0

lemma atom_of_le {e s t : ℝ} (h : s ≤ t) :
    atom e s t = exp (-e * s) * (exp (-s / 2) - exp (-t / 2)) := by
  rw [atom, max_eq_left]
  exact sub_nonneg.mpr (exp_le_exp.mpr (by linarith))

lemma atom_of_ge {e s t : ℝ} (h : t ≤ s) : atom e s t = 0 := by
  rw [atom, max_eq_right, mul_zero]
  exact sub_nonpos.mpr (exp_le_exp.mpr (by linarith))

lemma continuous_atom (e s : ℝ) : Continuous (atom e s) := by
  unfold atom; fun_prop

/-- The prime-power cell: for `n ≥ 1`, `g_{e, log n}(t) = n^{−e}(n^{−1/2} − e^{−t/2})` if
`n ≤ e^t`, and `0` otherwise. -/
theorem atom_log {n : ℕ} (hn : 1 ≤ n) (e t : ℝ) :
    atom e (Real.log n) t =
      if (n : ℝ) ≤ exp t then (n : ℝ) ^ (-e) * ((n : ℝ) ^ (-(1 / 2) : ℝ) - exp (-t / 2)) else 0 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ exp t ↔ Real.log n ≤ t := by
    rw [← log_le_iff_le_exp hpos]
  split_ifs with h
  · rw [atom_of_le (hle.mp h), rpow_def_of_pos hpos, rpow_def_of_pos hpos]
    congr 2 <;> ring_nf
  · exact atom_of_ge (le_of_lt (not_le.mp (fun h' => h (hle.mpr h'))))

/-- `c ∫_a^b e^{cu} du = e^{cb} − e^{ca}`, for every `c` (including `c = 0`). -/
lemma mul_integral_exp (c a b : ℝ) : c * ∫ u in a..b, exp (c * u) = exp (c * b) - exp (c * a) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [intervalIntegral.integral_comp_mul_left (fun x => exp x) hc, integral_exp, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

lemma continuous_kernel1 (e s : ℝ) : Continuous fun u => exp (-e * u) * atom 0 s u := by
  have := continuous_atom 0 s; fun_prop

lemma continuous_kernel2 (e s t : ℝ) :
    Continuous fun u => exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u := by
  have := continuous_atom 0 s; fun_prop

lemma integral_kernel_zero {f : ℝ → ℝ} {s t : ℝ} (h0 : 0 ≤ s) (hts : t ≤ s) :
    ∫ u in (0 : ℝ)..t, f u * atom 0 s u = 0 := by
  rw [integral_congr (g := fun _ => (0 : ℝ)), integral_zero]
  intro u hu
  have hu' : u ≤ s := by
    rcases le_total 0 t with h | h
    · rw [Set.uIcc_of_le h] at hu; exact hu.2.trans hts
    · rw [Set.uIcc_of_ge h] at hu; exact hu.2.trans h0
  simp [atom_of_ge hu']

lemma split_integral {f : ℝ → ℝ} {s : ℝ} (hf : Continuous fun u => f u * atom 0 s u) (t : ℝ)
    (h0 : 0 ≤ s) :
    ∫ u in (0 : ℝ)..t, f u * atom 0 s u = ∫ u in s..t, f u * atom 0 s u := by
  rw [← integral_add_adjacent_intervals (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s t),
    integral_kernel_zero h0 le_rfl, zero_add]

lemma int1 {e s t : ℝ} (h0 : 0 ≤ s) (hs : s ≤ t) :
    ∫ u in (0 : ℝ)..t, exp (-e * u) * atom 0 s u =
      exp (-s / 2) * (∫ u in s..t, exp (-e * u)) - ∫ u in s..t, exp (-(e + 1 / 2) * u) := by
  rw [split_integral (continuous_kernel1 e s) t h0, ← integral_const_mul,
    ← integral_sub ((Continuous.intervalIntegrable (by fun_prop) _ _)) ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  refine integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hs] at hu
  simp only [atom_of_le hu.1, neg_zero, zero_mul, exp_zero, one_mul,
    show -(e + 1 / 2) * u = -e * u + -u / 2 by ring, exp_add]
  ring

lemma int2 {e s t : ℝ} (h0 : 0 ≤ s) (hs : s ≤ t) :
    ∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u =
      exp (-t / 2) * (exp (-s / 2) * (∫ u in s..t, exp ((1 / 2 - e) * u)) -
        ∫ u in s..t, exp (-e * u)) := by
  rw [split_integral (continuous_kernel2 e s t) t h0, ← integral_const_mul,
    ← integral_sub ((Continuous.intervalIntegrable (by fun_prop) _ _)) ((Continuous.intervalIntegrable (by fun_prop) _ _)), ← integral_const_mul]
  refine integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hs] at hu
  have h1 : exp (u / 2) * exp (-u / 2) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  simp only [atom_of_le hu.1, neg_zero, zero_mul, exp_zero, one_mul,
    show -(t - u) / 2 = -t / 2 + u / 2 by ring, show (1 / 2 - e) * u = u / 2 + -e * u by ring,
    exp_add]
  linear_combination -(exp (-t / 2) * exp (-e * u)) * h1

/-- **Astra's Volterra identity, one atom.** For `s ≥ 0` and all real `e`, `t`. -/
theorem volterra_atom {s : ℝ} (h0 : 0 ≤ s) (e t : ℝ) :
    atom e s t = exp (-e * t) * atom 0 s t +
      e * (1 + 2 * e) * (∫ u in (0 : ℝ)..t, exp (-e * u) * atom 0 s u) +
      e * (1 - 2 * e) * (∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u) := by
  rcases le_total t s with hts | hs
  · rw [atom_of_ge hts, atom_of_ge hts, integral_kernel_zero h0 hts,
      integral_kernel_zero (f := fun u => exp (-(t - u) / 2) * exp (-e * u)) h0 hts]
    ring
  rw [int1 h0 hs, int2 h0 hs, atom_of_le hs, atom_of_le hs]
  simp only [neg_zero, zero_mul, exp_zero, one_mul]
  have L1 := mul_integral_exp (-e) s t
  have L2 := mul_integral_exp (-(e + 1 / 2)) s t
  have L3 := mul_integral_exp (1 / 2 - e) s t
  rw [show -(e + 1 / 2) * t = -e * t + -t / 2 by ring, show -(e + 1 / 2) * s = -e * s + -s / 2 by ring,
    exp_add, exp_add] at L2
  rw [show (1 / 2 - e) * t = t / 2 + -e * t by ring, show (1 / 2 - e) * s = s / 2 + -e * s by ring,
    exp_add, exp_add] at L3
  have hC : exp (t / 2) * exp (-t / 2) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have hB : exp (s / 2) * exp (-s / 2) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  set A := exp (-e * s); set B := exp (-s / 2); set C := exp (-t / 2); set D := exp (-e * t)
  linear_combination ((1 + 2 * e) * B - (1 - 2 * e) * C) * L1 + (-2 * e) * L2 +
    (-2 * e * C * B) * L3 + (-2 * e * B * D) * hC + (2 * e * C * A) * hB

/-- A finite superposition of atoms `J_e(t) = Σ_k c_k g_{e, s_k}(t)`. -/
noncomputable def superpose {ι : Type*} (S : Finset ι) (c σ : ι → ℝ) (e t : ℝ) : ℝ :=
  ∑ k ∈ S, c k * atom e (σ k) t

/-- **Astra's Volterra identity for every finite superposition of atoms.** -/
theorem volterra_sum {ι : Type*} (S : Finset ι) (c σ : ι → ℝ) (hσ : ∀ k ∈ S, 0 ≤ σ k) (e t : ℝ) :
    superpose S c σ e t = exp (-e * t) * superpose S c σ 0 t +
      e * (1 + 2 * e) * (∫ u in (0 : ℝ)..t, exp (-e * u) * superpose S c σ 0 u) +
      e * (1 - 2 * e) *
        (∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * superpose S c σ 0 u) := by
  unfold superpose
  simp_rw [mul_sum]
  rw [integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by
      have := continuous_atom 0 (σ k); fun_prop) _ _),
    integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by
      have := continuous_atom 0 (σ k); fun_prop) _ _), mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [volterra_atom (hσ k hk) e t]
  have h1 : ∫ u in (0 : ℝ)..t, exp (-e * u) * (c k * atom 0 (σ k) u) =
      c k * ∫ u in (0 : ℝ)..t, exp (-e * u) * atom 0 (σ k) u := by
    rw [← integral_const_mul]; exact integral_congr fun u _ => by ring
  have h2 : ∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * (c k * atom 0 (σ k) u) =
      c k * ∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * atom 0 (σ k) u := by
    rw [← integral_const_mul]; exact integral_congr fun u _ => by ring
  rw [h1, h2]; ring

/-- The truncated prime signal `Σ_{n<N} 2Λ(n) g_{e, log n}`. -/
noncomputable def primeSignal (N : ℕ) (e t : ℝ) : ℝ :=
  superpose (range N) (fun n => 2 * ArithmeticFunction.vonMangoldt n) (fun n => Real.log n) e t

/-- The truncated prime signal is Astra's `M_e(t) = 2 Σ_{n ≤ e^t} Λ(n) n^{−e}(n^{−1/2} − e^{−t/2})`,
summed over `n < N`; it is independent of `N` once `e^t < N`. -/
theorem primeSignal_eq (N : ℕ) (e t : ℝ) :
    primeSignal N e t = 2 * ∑ n ∈ range N, if (n : ℝ) ≤ exp t then
      ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-e) * ((n : ℝ) ^ (-(1 / 2) : ℝ) - exp (-t / 2)))
      else 0 := by
  rw [primeSignal, superpose, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [atom_log hn]; split_ifs <;> ring

/-- **Volterra identity for the truncated prime signal**, for every `N`, `e`, `t`. -/
theorem volterra_primeSignal (N : ℕ) (e t : ℝ) :
    primeSignal N e t = exp (-e * t) * primeSignal N 0 t +
      e * (1 + 2 * e) * (∫ u in (0 : ℝ)..t, exp (-e * u) * primeSignal N 0 u) +
      e * (1 - 2 * e) *
        (∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * primeSignal N 0 u) :=
  volterra_sum _ _ _ (fun n _ => Real.log_natCast_nonneg n) e t

lemma continuous_atom₂ (e : ℝ) : Continuous fun p : ℝ × ℝ => atom e p.1 p.2 := by
  unfold atom; fun_prop

/-- Fubini on a rectangle for a jointly continuous integrand. -/
lemma swap_interval (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ u in a..b, ∫ s in c..d, F u s = ∫ s in c..d, ∫ u in a..b, F u s := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine MeasureTheory.integral_integral_swap ?_
  rw [MeasureTheory.Measure.prod_restrict]
  have h : MeasureTheory.IntegrableOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc c d)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact h.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- A continuum superposition `∫₀ᵗ w(s) g_{e,s}(t) ds`. -/
noncomputable def contSignal (w : ℝ → ℝ) (e t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, w s * atom e s t

lemma contSignal_eq_upto {w : ℝ → ℝ} (hw : Continuous w) (e : ℝ) {u T : ℝ} (huT : u ≤ T) : contSignal w e u = ∫ s in (0 : ℝ)..T, w s * atom e s u := by
  have hc : Continuous fun s => w s * atom e s u := by
    have := continuous_atom₂ e; fun_prop
  rw [contSignal, ← integral_add_adjacent_intervals (hc.intervalIntegrable 0 u)
    (hc.intervalIntegrable u T)]
  have hz : ∫ s in u..T, w s * atom e s u = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)), integral_zero]
    intro s hs
    rw [Set.uIcc_of_le huT] at hs
    simp [atom_of_ge hs.1]
  rw [hz, add_zero]

lemma continuous_contSignal {w : ℝ → ℝ} (hw : Continuous w) (e : ℝ) :
    Continuous (contSignal w e) := by
  unfold contSignal
  have := continuous_atom₂ e
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => w s * atom e s t) (by fun_prop) continuous_id

lemma swap_kernel {w : ℝ → ℝ} (hw : Continuous w) (k : ℝ → ℝ → ℝ)
    (hk : Continuous (Function.uncurry k)) {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, k t u * contSignal w 0 u =
      ∫ s in (0 : ℝ)..t, w s * ∫ u in (0 : ℝ)..t, k t u * atom 0 s u := by
  have hk' : Continuous fun u => k t u := hk.comp (continuous_const.prodMk continuous_id)
  calc ∫ u in (0 : ℝ)..t, k t u * contSignal w 0 u
      = ∫ u in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, k t u * (w s * atom 0 s u) := by
        refine integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le ht] at hu
        rw [contSignal_eq_upto hw 0 hu.2, ← integral_const_mul]
    _ = ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..t, k t u * (w s * atom 0 s u) := by
        refine swap_interval _ ?_ ht ht
        have := continuous_atom₂ 0
        have h2 : Continuous fun p : ℝ × ℝ => atom 0 p.2 p.1 :=
          this.comp (continuous_snd.prodMk continuous_fst)
        exact (hk'.comp continuous_fst).mul ((hw.comp continuous_snd).mul h2)
    _ = ∫ s in (0 : ℝ)..t, w s * ∫ u in (0 : ℝ)..t, k t u * atom 0 s u := by
        refine integral_congr fun s _ => ?_
        rw [← integral_const_mul]
        exact integral_congr fun u _ => by ring

/-- **Astra's Volterra identity for every continuum superposition**, `t ≥ 0`. -/
theorem volterra_cont {w : ℝ → ℝ} (hw : Continuous w) (e : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    contSignal w e t = exp (-e * t) * contSignal w 0 t +
      e * (1 + 2 * e) * (∫ u in (0 : ℝ)..t, exp (-e * u) * contSignal w 0 u) +
      e * (1 - 2 * e) *
        (∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * contSignal w 0 u) := by
  rw [swap_kernel hw (fun _ u => exp (-e * u)) (by fun_prop) ht,
    swap_kernel hw (fun t u => exp (-(t - u) / 2) * exp (-e * u)) (by fun_prop) ht]
  have hc1 : Continuous fun s => w s * ∫ u in (0 : ℝ)..t, exp (-e * u) * atom 0 s u := by
    have := continuous_atom₂ 0
    exact hw.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s u => exp (-e * u) * atom 0 s u) (by fun_prop) 0 t)
  have hc2 : Continuous fun s =>
      w s * ∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u := by
    have := continuous_atom₂ 0
    exact hw.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s u => exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u) (by fun_prop) 0 t)
  have hc0 : Continuous fun s => w s * atom 0 s t := by
    have := continuous_atom₂ 0; fun_prop
  have hpt : ∫ s in (0 : ℝ)..t, w s * atom e s t =
      ∫ s in (0 : ℝ)..t, (exp (-e * t) * (w s * atom 0 s t) +
        e * (1 + 2 * e) * (w s * ∫ u in (0 : ℝ)..t, exp (-e * u) * atom 0 s u) +
        e * (1 - 2 * e) *
          (w s * ∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * atom 0 s u)) := by
    refine integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    rw [volterra_atom hs.1 e t]
    ring
  rw [contSignal, contSignal, hpt, integral_add
      (((hc0.const_mul _).intervalIntegrable 0 t).add ((hc1.const_mul _).intervalIntegrable 0 t))
      ((hc2.const_mul _).intervalIntegrable 0 t),
    integral_add ((hc0.const_mul _).intervalIntegrable 0 t) ((hc1.const_mul _).intervalIntegrable 0 t),
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- Astra's continuum term is the superposition with weight `w(s) = e^s`: for `t ≥ 0`,
`∫₁^{e^t} (x^{−1/2} − e^{−t/2}) x^{−e} dx = ∫₀ᵗ e^s g_{e,s}(t) ds`. -/
theorem continuum_eq (e : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in (1 : ℝ)..exp t, (x ^ (-(1 / 2) : ℝ) - exp (-t / 2)) * x ^ (-e) = contSignal exp e t := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := t) (f := exp)
    (f' := exp) (g := fun x => (x ^ (-(1 / 2) : ℝ) - exp (-t / 2)) * x ^ (-e))
    continuous_exp.continuousOn (fun x _ => hasDerivAt_exp x) (fun x _ => (exp_pos x).le)
  rw [exp_zero] at h
  rw [← h, contSignal]
  refine integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  simp only [Function.comp, atom_of_le hs.2, ← exp_mul]
  rw [show s * (-(1 / 2) : ℝ) = -s / 2 by ring, show s * -e = -e * s by ring]
  ring

/-- Astra's balanced signal: prime truncation minus continuum minus endpoint. For `e^t < N` and
`t ≥ 0` this is `J_e(t) = M_e(t) − C_e(t)` (`primeSignal_eq`, `continuum_eq`, and
`2(1 − e^{−t/2}) = 2 g_{e,0}(t)`). -/
noncomputable def balanced (N : ℕ) (e t : ℝ) : ℝ :=
  primeSignal N e t - 2 * contSignal exp e t - 2 * atom e 0 t

lemma endpoint_eq (e : ℝ) {t : ℝ} (ht : 0 ≤ t) : atom e 0 t = 1 - exp (-t / 2) := by
  rw [atom_of_le ht]; simp

/-- `balanced` is Astra's `M_e − C_e` written out: for `t ≥ 0`, the prime sum over `n < N` with
`n ≤ e^t` (all of `M_e(t)` once `e^t < N`), minus `2∫₁^{e^t} (x^{−1/2} − e^{−t/2}) x^{−e} dx`, minus
`2(1 − e^{−t/2})`. -/
theorem balanced_eq (N : ℕ) (e : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    balanced N e t =
      2 * (∑ n ∈ range N, if (n : ℝ) ≤ exp t then ArithmeticFunction.vonMangoldt n *
        ((n : ℝ) ^ (-e) * ((n : ℝ) ^ (-(1 / 2) : ℝ) - exp (-t / 2))) else 0) -
      (2 * (∫ x in (1 : ℝ)..exp t, (x ^ (-(1 / 2) : ℝ) - exp (-t / 2)) * x ^ (-e)) +
        2 * (1 - exp (-t / 2))) := by
  rw [balanced, primeSignal_eq, continuum_eq e ht, endpoint_eq e ht]; ring

/-- **The unregularised signal in closed form** (Astra, `work/2026-10-20_astra_laplace_growth_mobius_audit.md`):
for `t ≥ 0`, with `X = e^t`, `J₀(log X) = 2 Σ_{n ≤ X} Λ(n)/√n − 2ψ(X)/√X − 2√X + 2`. -/
theorem balanced_zero_eq (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    balanced N 0 t =
      2 * (∑ n ∈ range N, if (n : ℝ) ≤ exp t then
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2) : ℝ) else 0) -
      2 * (∑ n ∈ range N, if (n : ℝ) ≤ exp t then ArithmeticFunction.vonMangoldt n else 0) *
        exp (-t / 2) - 2 * exp (t / 2) + 2 := by
  rw [balanced_eq N 0 ht]
  simp only [neg_zero, rpow_zero, mul_one, one_mul]
  have hI : ∫ x in (1 : ℝ)..exp t, (x ^ (-(1 / 2) : ℝ) - exp (-t / 2)) =
      2 * (exp (t / 2) - 1) - (exp t - 1) * exp (-t / 2) := by
    rw [integral_sub (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
      intervalIntegrable_const, integral_rpow (Or.inl (by norm_num)), integral_const, smul_eq_mul,
      one_rpow, ← exp_mul]
    norm_num
    ring_nf
  have hsum : ∀ n ∈ range N, (if (n : ℝ) ≤ exp t then ArithmeticFunction.vonMangoldt n *
      ((n : ℝ) ^ (-(1 / 2) : ℝ) - exp (-t / 2)) else 0) =
      (if (n : ℝ) ≤ exp t then ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2) : ℝ) else 0) -
        (if (n : ℝ) ≤ exp t then ArithmeticFunction.vonMangoldt n else 0) * exp (-t / 2) := by
    intro n _; split_ifs <;> ring
  rw [sum_congr rfl hsum, sum_sub_distrib, ← sum_mul, hI]
  have hx : exp t * exp (-t / 2) = exp (t / 2) := by rw [← exp_add]; ring_nf
  linear_combination 2 * hx

/-- **Astra's exact Volterra relation for `J_e`**, for every truncation `N`, every `e` and every
`t ≥ 0`. -/
theorem volterra_balanced (N : ℕ) (e : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    balanced N e t = exp (-e * t) * balanced N 0 t +
      e * (1 + 2 * e) * (∫ u in (0 : ℝ)..t, exp (-e * u) * balanced N 0 u) +
      e * (1 - 2 * e) *
        (∫ u in (0 : ℝ)..t, exp (-(t - u) / 2) * exp (-e * u) * balanced N 0 u) := by
  have hP : Continuous (primeSignal N 0) := by
    unfold primeSignal superpose
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_atom 0 _)
  have hC := continuous_contSignal continuous_exp 0
  have hA := continuous_atom 0 0
  have hsplit : ∀ k : ℝ → ℝ → ℝ, Continuous (Function.uncurry k) →
      ∫ u in (0 : ℝ)..t, k t u * balanced N 0 u =
        (∫ u in (0 : ℝ)..t, k t u * primeSignal N 0 u) -
          2 * (∫ u in (0 : ℝ)..t, k t u * contSignal exp 0 u) -
          2 * (∫ u in (0 : ℝ)..t, k t u * atom 0 0 u) := by
    intro k hk
    have hk' : Continuous fun u => k t u := hk.comp (continuous_const.prodMk continuous_id)
    have hpt : ∫ u in (0 : ℝ)..t, k t u * balanced N 0 u =
        ∫ u in (0 : ℝ)..t, (k t u * primeSignal N 0 u - 2 * (k t u * contSignal exp 0 u) -
          2 * (k t u * atom 0 0 u)) :=
      integral_congr fun u _ => by rw [balanced]; ring
    have h1 : Continuous fun u => k t u * primeSignal N 0 u := hk'.mul hP
    have h2 : Continuous fun u => 2 * (k t u * contSignal exp 0 u) := (hk'.mul hC).const_mul 2
    have h3 : Continuous fun u => 2 * (k t u * atom 0 0 u) := (hk'.mul hA).const_mul 2
    rw [hpt, integral_sub ((h1.intervalIntegrable 0 t).sub (h2.intervalIntegrable 0 t))
        (h3.intervalIntegrable 0 t),
      integral_sub (h1.intervalIntegrable 0 t) (h2.intervalIntegrable 0 t),
      integral_const_mul, integral_const_mul]
  rw [hsplit (fun _ u => exp (-e * u)) (by fun_prop),
    hsplit (fun t u => exp (-(t - u) / 2) * exp (-e * u)) (by fun_prop)]
  have hp := volterra_primeSignal N e t
  have hc := volterra_cont continuous_exp e ht
  have ha := volterra_sum {()} (fun _ => 1) (fun _ => 0) (fun _ _ => le_rfl) e t
  simp only [superpose, sum_singleton, one_mul] at ha
  simp only [balanced]
  linear_combination hp - 2 * hc - 2 * ha

end GppBalancedRegulator
