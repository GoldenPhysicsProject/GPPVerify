/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok; T2 statement from Flint,
converse argument from Codex, surrounding tree from Claude Code, audited by Turbo)
-/
import GppVerify.RiemannHypothesis.MobiusEchoSubpower
import GppVerify.RiemannHypothesis.MertensMellin
import GppVerify.RiemannHypothesis.CausalEnergyZero

/-!
# T2: subpower Möbius energy from Mertens decay, and from RH given the Mertens converse

Flint's D6-1 target T2 (bridge `4db46ac`): under RH, at `c = 1/ζ(1/2)`,
`∃ N_j → ∞, ∀ η > 0, ∀ᶠ j, Q c (log N_j) ≤ N_j^η`, with `Q = GppMobiusEcho.Q`. That is the right side
of `GppMobiusEcho.storage_work_iff_subpower_energy`. The argument is Codex's partial summation
(GPPDiscovery2 `0abf88b`), run here from the coefficients `μ(n)/n` of `GppMertensMellin.mert`.

Write `A(n) = Σ_{k ≤ n} μ(k)/k`, so that `‖mert n‖ = |A n|`, and `S(k) = Σ_{n ≤ k} μ(n)/√n`
(`GppMobiusEcho.S`).

* `abel_S`: `S(k) = A(k)√k − Σ_{n<k} A(n)(√(n+1) − √n)` (discrete partial summation; unconditional).
* `sum_log_ratio`: `Σ_{n<N} log((n+1)/n) = log N` (unconditional).
* `abs_S_le`: if `|A n| ≤ C n^{−(1/2−ε)}` for `n ≥ 1`, then `|S k| ≤ C N^ε (1 + 2 log N)` for
  `k ≤ N`, `N ≥ 1`.
* `Q_le`: under the same bound, `Q c (log N) ≤ log N · (C N^ε (1 + 2 log N) + |c|)²`.
* `subpower_of_mertensDecay`: `MertensDecay` (the exact hypothesis shape of
  `GppMertensMellin.riemannHypothesis_of_mertens_decay`) gives, for **every real `c`** and every
  `η > 0`, `Q c (log N) ≤ N^η` for all large `N`.
* `exists_subpower_seq_of_mertensDecay`: the same, in T2's single-sequence-first form.
* `subpower_of_rh` (**T2**): given `hT1 : RiemannHypothesis → MertensDecay`, RH gives T2's form at
  `c = cHalf = Re(1/ζ(1/2))`.
* `rh_of_subpowerSeq`: T2's form at any real `c` gives `RiemannHypothesis` (the sparse-cutoff
  criterion `GppSparseCutoff.riemannHypothesis_of_nat_subpower` with
  `GppCausalEnergy.energyZeroInequality_causal`); no hypothesis.
* `mertensDecay_iff_subpower`: given `hT1`, `MertensDecay` ↔ T2's form, for every real `c`.
* `rh_iff_subpower`: given `hT1`, `RiemannHypothesis` ↔ T2's form, for every real `c`.

Hypotheses taken: `MertensDecay` in the first five, and `hT1 : RiemannHypothesis → MertensDecay`
(T1, the classical Littlewood converse; Claude Code's lane) in `subpower_of_rh` and `rh_iff_subpower`.
No `sorry`, no `admit`, no `axiom`.

— Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
-/

open Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GppSubpowerOfRH

/-- The Mertens decay hypothesis, in the exact shape taken by
`GppMertensMellin.riemannHypothesis_of_mertens_decay` (Flint's T1 is `RiemannHypothesis → MertensDecay`). -/
def MertensDecay : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
    ‖GppMertensMellin.mert t‖ ≤ C * t ^ (-(1 / 2 - ε))

/-- T2's single-sequence-first subpower form for the Möbius energy at constant `c`. -/
def SubpowerSeq (c : ℝ) : Prop :=
  ∃ Nj : ℕ → ℕ, Tendsto Nj atTop atTop ∧ (∀ j, 1 ≤ Nj j) ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, GppMobiusEcho.Q c (Real.log (Nj j)) ≤ (Nj j : ℝ) ^ η

/-- The constant `c = 1/ζ(1/2)`, taken as a real number via the real part. -/
noncomputable def cHalf : ℝ := (1 / riemannZeta (1 / 2)).re

/-- `A(n) = Σ_{k ≤ n} μ(k)/k`, the real Mertens sum. -/
noncomputable def A (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (μ k : ℝ) / k

theorem A_zero : A 0 = 0 := by simp [A]

theorem norm_mert_nat (n : ℕ) : ‖GppMertensMellin.mert n‖ = |A n| := by
  unfold GppMertensMellin.mert GppMertensMellin.coef A
  rw [Nat.floor_natCast]
  have : (∑ k ∈ Finset.Icc 1 n, ((μ k : ℂ) / (k : ℂ))) =
      ((∑ k ∈ Finset.Icc 1 n, (μ k : ℝ) / k : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs]

theorem a_eq (n : ℕ) : GppMobiusEcho.a n = (μ n : ℝ) / n * Real.sqrt n := by
  unfold GppMobiusEcho.a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    calc (μ n : ℝ) / Real.sqrt n = (μ n : ℝ) / (Real.sqrt n * Real.sqrt n) * Real.sqrt n := by
          field_simp
      _ = (μ n : ℝ) / n * Real.sqrt n := by rw [h2]

/-- **Discrete partial summation** from `μ(n)/n` to `μ(n)/√n`. -/
theorem abel_S (k : ℕ) :
    GppMobiusEcho.S k =
      A k * Real.sqrt k - ∑ n ∈ Finset.range k, A n * (Real.sqrt (n + 1) - Real.sqrt n) := by
  induction k with
  | zero => simp [GppMobiusEcho.S, A]
  | succ k ih =>
    have hS : GppMobiusEcho.S (k + 1) = GppMobiusEcho.S k + GppMobiusEcho.a (k + 1) := by
      unfold GppMobiusEcho.S; rw [Finset.sum_Icc_succ_top (by omega)]
    have hA : A (k + 1) = A k + (μ (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      unfold A; rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hS, ih, hA, a_eq, Finset.sum_range_succ]
    push_cast
    ring

/-- `Σ_{n<N} log((n+1)/n) = log N` (the `n = 0` term is `log 0 = 0` in Lean's conventions). -/
theorem sum_log_ratio (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.log ((n + 1 : ℝ) / n) = Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [Real.log_div (by positivity) hN0.ne']
      push_cast; ring

theorem log_ratio_nonneg (n : ℕ) : 0 ≤ Real.log ((n + 1 : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    apply Real.log_nonneg
    rw [le_div_iff₀ hn0]; linarith

/-- `1/(n+1) ≤ log((n+1)/n)` for `n ≥ 1`. -/
theorem inv_succ_le_log_ratio {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n + 1 : ℝ) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / (n + 1) by positivity)
  have hinv : Real.log ((n + 1 : ℝ) / n) = - Real.log (n / (n + 1)) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv]
  have : (n : ℝ) / (n + 1) - 1 = - (1 / (n + 1)) := by field_simp; ring
  linarith

theorem sqrt_succ_sub_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n + 1) - Real.sqrt n ≤ 1 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs1 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt (by positivity)
  have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hle : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
  rw [le_div_iff₀ hs]
  nlinarith

section Bounds

variable {C ε : ℝ}

/-- From the decay of `A`: each partial-summation term is at most `2 C N^ε log((n+1)/n)`. -/
theorem term_le (hε : 0 < ε)
    (hA : ∀ n : ℕ, 1 ≤ n → |A n| ≤ C * (n : ℝ) ^ (-(1 / 2 - ε)))
    {N n : ℕ} (hnN : n ≤ N) :
    |A n| * (Real.sqrt (n + 1) - Real.sqrt n) ≤
      2 * C * (N : ℝ) ^ ε * Real.log ((n + 1 : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [A_zero]
  · have hn1 : 1 ≤ n := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hC : 0 ≤ C := by
      have := hA n hn1
      have hp : 0 < (n : ℝ) ^ (-(1 / 2 - ε)) := Real.rpow_pos_of_pos hn0 _
      exact (mul_nonneg_iff_of_pos_right hp).mp ((abs_nonneg _).trans this)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hd0 : 0 ≤ Real.sqrt (n + 1) - Real.sqrt n :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    -- `n^{-(1/2-ε)} / √n = n^ε / n`
    have hpow : (n : ℝ) ^ (-(1 / 2 - ε)) * (1 / Real.sqrt n) = (n : ℝ) ^ ε / n := by
      rw [show -(1 / 2 - ε) = ε - 1 / 2 by ring, Real.rpow_sub hn0, ← Real.sqrt_eq_rpow,
        div_mul_div_comm, mul_one, Real.mul_self_sqrt hn0.le]
    have hmono : (n : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN) hε.le
    have hlog := inv_succ_le_log_ratio hn1
    have hNe : 0 ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
    calc |A n| * (Real.sqrt (n + 1) - Real.sqrt n)
        ≤ (C * (n : ℝ) ^ (-(1 / 2 - ε))) * (1 / Real.sqrt n) :=
          mul_le_mul (hA n hn1) (sqrt_succ_sub_le hn1) hd0
            (mul_nonneg hC (Real.rpow_nonneg hn0.le _))
      _ = C * ((n : ℝ) ^ ε / n) := by rw [mul_assoc, hpow]
      _ ≤ C * ((N : ℝ) ^ ε / n) := by gcongr
      _ = C * (N : ℝ) ^ ε * (1 / n) := by ring
      _ ≤ C * (N : ℝ) ^ ε * (2 * (1 / ((n : ℝ) + 1))) := by
          gcongr
          rw [div_le_iff₀ hn0]
          field_simp
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          linarith
      _ ≤ C * (N : ℝ) ^ ε * (2 * Real.log ((n + 1 : ℝ) / n)) := by gcongr
      _ = 2 * C * (N : ℝ) ^ ε * Real.log ((n + 1 : ℝ) / n) := by ring

/-- **Bound on the partial sums `S`.** If `|A n| ≤ C n^{−(1/2−ε)}` for `n ≥ 1`, then
`|S k| ≤ C N^ε (1 + 2 log N)` whenever `k ≤ N` and `N ≥ 1`. -/
theorem abs_S_le (hε : 0 < ε)
    (hA : ∀ n : ℕ, 1 ≤ n → |A n| ≤ C * (n : ℝ) ^ (-(1 / 2 - ε)))
    {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    |GppMobiusEcho.S k| ≤ C * (N : ℝ) ^ ε * (1 + 2 * Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C := by
    have h1 := hA 1 le_rfl
    simp at h1
    linarith [abs_nonneg (A 1)]
  have hNe : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hN) hε.le
  -- head term
  have hhead : |A k * Real.sqrt k| ≤ C * (N : ℝ) ^ ε := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [A_zero]; exact mul_nonneg hC (by linarith)
    · have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hpow : (k : ℝ) ^ (-(1 / 2 - ε)) * Real.sqrt k = (k : ℝ) ^ ε := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk0']; ring_nf
      calc |A k| * Real.sqrt k ≤ C * (k : ℝ) ^ (-(1 / 2 - ε)) * Real.sqrt k :=
            mul_le_mul_of_nonneg_right (hA k hk0) (Real.sqrt_nonneg _)
        _ = C * (k : ℝ) ^ ε := by rw [mul_assoc, hpow]
        _ ≤ C * (N : ℝ) ^ ε := by
            gcongr
  -- tail sum
  have htail : |∑ n ∈ Finset.range k, A n * (Real.sqrt (n + 1) - Real.sqrt n)| ≤
      2 * C * (N : ℝ) ^ ε * Real.log N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range k, |A n * (Real.sqrt (n + 1) - Real.sqrt n)|
        ≤ ∑ n ∈ Finset.range k, 2 * C * (N : ℝ) ^ ε * Real.log ((n + 1 : ℝ) / n) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hnk : n < k := Finset.mem_range.mp hn
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith)))]
          exact term_le hε hA (by omega)
      _ ≤ ∑ n ∈ Finset.range N, 2 * C * (N : ℝ) ^ ε * Real.log ((n + 1 : ℝ) / n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk) ?_
          intro n _ _
          have := log_ratio_nonneg n
          positivity
      _ = 2 * C * (N : ℝ) ^ ε * Real.log N := by
          rw [← Finset.mul_sum, sum_log_ratio]
  rw [abel_S]
  calc |A k * Real.sqrt k - ∑ n ∈ Finset.range k, A n * (Real.sqrt (n + 1) - Real.sqrt n)|
      ≤ |A k * Real.sqrt k| + |∑ n ∈ Finset.range k, A n * (Real.sqrt (n + 1) - Real.sqrt n)| :=
        abs_sub _ _
    _ ≤ C * (N : ℝ) ^ ε + 2 * C * (N : ℝ) ^ ε * Real.log N := add_le_add hhead htail
    _ = C * (N : ℝ) ^ ε * (1 + 2 * Real.log N) := by ring

/-- **Energy bound.** Under the same decay of `A`, for every real `c` and `N ≥ 1`:
`Q c (log N) ≤ log N · (C N^ε (1 + 2 log N) + |c|)²`. -/
theorem Q_le (hε : 0 < ε)
    (hA : ∀ n : ℕ, 1 ≤ n → |A n| ≤ C * (n : ℝ) ^ (-(1 / 2 - ε))) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    GppMobiusEcho.Q c (Real.log N) ≤
      Real.log N * (C * (N : ℝ) ^ ε * (1 + 2 * Real.log N) + |c|) ^ 2 := by
  set B := C * (N : ℝ) ^ ε * (1 + 2 * Real.log N) + |c| with hB
  rw [(GppMobiusEcho.energy_identity c hN).2]
  have hb : ∀ k ∈ Finset.Ico 1 N, (GppMobiusEcho.b c k) ^ 2 ≤ B ^ 2 := by
    intro k hk
    have hkN : k ≤ N := (Finset.mem_Ico.mp hk).2.le
    have h1 : |GppMobiusEcho.b c k| ≤ B := by
      unfold GppMobiusEcho.b
      calc |GppMobiusEcho.S k - c| ≤ |GppMobiusEcho.S k| + |c| := abs_sub _ _
        _ ≤ B := by rw [hB]; linarith [abs_S_le hε hA hN hkN]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∑ k ∈ Finset.Ico 1 N, Real.log ((k + 1 : ℝ) / k) * (GppMobiusEcho.b c k) ^ 2
      ≤ ∑ k ∈ Finset.Ico 1 N, Real.log ((k + 1 : ℝ) / k) * B ^ 2 :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hb k hk) (log_ratio_nonneg k))
    _ ≤ ∑ k ∈ Finset.range N, Real.log ((k + 1 : ℝ) / k) * B ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro k hk; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        · intro k _ _; have := log_ratio_nonneg k; positivity
    _ = Real.log N * B ^ 2 := by rw [← Finset.sum_mul, sum_log_ratio]

end Bounds

/-- **Mertens decay ⇒ subpower Möbius energy at every cutoff**, for every real `c`. -/
theorem subpower_of_mertensDecay (hM : MertensDecay) (c : ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, GppMobiusEcho.Q c (Real.log N) ≤ (N : ℝ) ^ η := by
  intro η hη
  set ε := min (η / 8) (1 / 4) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε2 : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε8 : ε ≤ η / 8 := min_le_left _ _
  obtain ⟨C, hC⟩ := hM ε hε hε2
  have hA : ∀ n : ℕ, 1 ≤ n → |A n| ≤ C * (n : ℝ) ^ (-(1 / 2 - ε)) := fun n hn => by
    rw [← norm_mert_nat]; exact hC n (by exact_mod_cast hn)
  have hC0 : 0 ≤ C := by
    have h1 := hA 1 le_rfl
    simp at h1
    linarith [abs_nonneg (A 1)]
  set D := C * (1 + 2 / ε) + |c| with hD
  have hD0 : 0 ≤ D := by
    rw [hD]; have : 0 ≤ 1 + 2 / ε := by positivity
    exact add_nonneg (mul_nonneg hC0 this) (abs_nonneg c)
  set K := D ^ 2 / ε with hK
  have hgap : 0 < η - 5 * ε := by linarith
  have hT : Tendsto (fun N : ℕ => (N : ℝ) ^ (η - 5 * ε)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop K, eventually_ge_atTop 1] with N hNK hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set u := (N : ℝ) ^ ε with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hN1 hε.le
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : Real.log N ≤ u / ε := Real.log_le_rpow_div hN0.le hε
  have hBle : C * u * (1 + 2 * Real.log N) + |c| ≤ D * u ^ 2 := by
    have h1 : C * u * (1 + 2 * Real.log N) ≤ C * u * (1 + 2 * (u / ε)) := by gcongr
    have h2 : C * u * (1 + 2 * (u / ε)) = C * u + 2 * C / ε * u ^ 2 := by field_simp
    have hu2 : 1 ≤ u ^ 2 := by nlinarith
    have h3 : C * u ≤ C * u ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hC0
    have h4 : |c| ≤ |c| * u ^ 2 := le_mul_of_one_le_right (abs_nonneg c) hu2
    rw [hD]
    have : (C * (1 + 2 / ε) + |c|) * u ^ 2 = C * u ^ 2 + 2 * C / ε * u ^ 2 + |c| * u ^ 2 := by
      field_simp
    rw [this]; linarith
  have hB0 : 0 ≤ C * u * (1 + 2 * Real.log N) + |c| :=
    add_nonneg (mul_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)) (abs_nonneg c)
  have hQ := Q_le hε hA c hN
  rw [← hu] at hQ
  have hu5 : u ^ 5 = (N : ℝ) ^ (5 * ε) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  calc GppMobiusEcho.Q c (Real.log N)
      ≤ Real.log N * (C * u * (1 + 2 * Real.log N) + |c|) ^ 2 := hQ
    _ ≤ (u / ε) * (D * u ^ 2) ^ 2 := by
        gcongr
    _ = K * u ^ 5 := by rw [hK]; field_simp
    _ ≤ (N : ℝ) ^ (η - 5 * ε) * (N : ℝ) ^ (5 * ε) := by
        rw [hu5]; gcongr
    _ = (N : ℝ) ^ η := by rw [← Real.rpow_add hN0]; ring_nf

/-- Mertens decay gives T2's single-sequence-first form (with `N_j = j + 1`), for every real `c`. -/
theorem exists_subpower_seq_of_mertensDecay (hM : MertensDecay) (c : ℝ) : SubpowerSeq c := by
  refine ⟨fun j => j + 1, tendsto_add_atTop_nat 1, fun j => Nat.le_add_left 1 j, ?_⟩
  intro η hη
  have h := subpower_of_mertensDecay hM c η hη
  have := (tendsto_add_atTop_nat 1).eventually h
  simpa using this

/-- **T2 (Flint, D6-1).** Given the Mertens converse `hT1 : RiemannHypothesis → MertensDecay` (T1),
the Riemann Hypothesis gives subpower Möbius energy along a sequence `N_j → ∞` at
`c = cHalf = Re(1/ζ(1/2))`. -/
theorem subpower_of_rh (hT1 : RiemannHypothesis → MertensDecay) (h : RiemannHypothesis) :
    SubpowerSeq cHalf :=
  exists_subpower_seq_of_mertensDecay (hT1 h) cHalf

/-- T2's form gives `RiemannHypothesis`, for every real `c` (sparse-cutoff criterion with
`energyZeroInequality_causal`). -/
theorem rh_of_subpowerSeq {c : ℝ} (h : SubpowerSeq c) : RiemannHypothesis := by
  obtain ⟨Nj, hNj, _, hsub⟩ := h
  exact GppSparseCutoff.riemannHypothesis_of_nat_subpower
    (GppCausalEnergy.energyZeroInequality_causal c) (by norm_num) hNj hsub

/-- Given the Mertens converse `hT1` (T1): `MertensDecay` ↔ T2's form, for every real `c`. -/
theorem mertensDecay_iff_subpower (c : ℝ) (hT1 : RiemannHypothesis → MertensDecay) :
    MertensDecay ↔ SubpowerSeq c :=
  ⟨fun hM => exists_subpower_seq_of_mertensDecay hM c, fun h => hT1 (rh_of_subpowerSeq h)⟩

/-- Given the Mertens converse `hT1` (T1): `RiemannHypothesis` ↔ T2's form, for every real `c`. -/
theorem rh_iff_subpower (hT1 : RiemannHypothesis → MertensDecay) (c : ℝ) :
    RiemannHypothesis ↔ SubpowerSeq c :=
  ⟨fun h => exists_subpower_seq_of_mertensDecay (hT1 h) c, rh_of_subpowerSeq⟩

end GppSubpowerOfRH

#print axioms GppSubpowerOfRH.abel_S
#print axioms GppSubpowerOfRH.abs_S_le
#print axioms GppSubpowerOfRH.Q_le
#print axioms GppSubpowerOfRH.subpower_of_mertensDecay
#print axioms GppSubpowerOfRH.exists_subpower_seq_of_mertensDecay
#print axioms GppSubpowerOfRH.subpower_of_rh
#print axioms GppSubpowerOfRH.rh_of_subpowerSeq
#print axioms GppSubpowerOfRH.mertensDecay_iff_subpower
#print axioms GppSubpowerOfRH.rh_iff_subpower
