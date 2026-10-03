import GppVerify.RiemannHypothesis.HalfDensityZetaGauge
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The finite zeta-graph metric: exact GCD kernel with harmonic taper, and the dual norm

Source: Codex, GPPDiscovery2 `research/2026-09-28_finite_zeta_graph_current_norm.md` §§1–2, and
`research/2026-10-01_halfdensity_mobius_dual_certificate.md` §1 (bridge copy through `59bf0a2`).

On `S_N = {1, …, N}` the half-density zeta synthesis is `Z_N(n,d) = √(d/n) · 1_{d ∣ n}`. Its inverse
`M_N(n,d) = μ(n/d) √(d/n) · 1_{d ∣ n}` and the identities `M Z = Z M = I` and the logarithmic gauge
identity are already in `HalfDensityZetaGauge`. This file adds what those notes build on top.

* **`gram_eq`** (the exact GCD kernel with a harmonic boundary taper). For `d, e ≥ 1`,
  `G_N(d,e) = Σ_{n ≤ N} Z_N(n,d) Z_N(n,e) = gcd(d,e)/√(de) · H_{⌊N/lcm(d,e)⌋}`,
  with `H_m = Σ_{q ≤ m} 1/q`.
* **`synth_current`.** The prime-supported current `j(n) = Λ(n)/√n` becomes smooth after
  synthesis: `(Z_N j)(n) = log n/√n`.
* **Dual norm.** With `G = ZᵀZ` and `c = Mᵀ a`: `a = Zᵀ c` (`halfZetaT_halfMobiusT`), the bound
  `⟨a,b⟩² ≤ ‖Mᵀ a‖² · ‖Z b‖²` for every `b` (`dual_norm_le`), with equality at `b = M c`
  (`dual_norm_attained`). So `‖Mᵀ a‖² = a ᵀ G⁻¹ a`, the note's
  `‖a‖²_{G̃⁻¹} = H_N ‖Mᵀ a‖²` after the normalization `G̃ = G/H_N`. This is the variational form;
  it avoids inverting a matrix.
* **`mobiusT_profile`.** For `a(n) = n^{-1/2} h(log n − t)`,
  `(Mᵀ a)(d) = d^{-1/2} Σ_{m ≤ N/d} μ(m)/m · h(log m − (t − log d))`. This is the note's boxed
  equation (1), where the second half-density turns the critical `m^{-1/2}` Möbius coefficient
  into `m^{-1}`.

## Checks

All of the above were checked by hand against the notes; no corrections.

## Scope

Finite identities. **Not formalized:** the bound `‖j_N‖_{G̃_N} ≤ log N`, the Fourier boundary
identity `B̂_h(ξ) = ĥ(−ξ)/ζ(1+iξ)` and the limit `‖Mᵀ a‖₂ = O_h(1)` (these need the analytic
boundary theory), and the nonvanishing/analyticity discussion of §0 of the first note. No RH claim.
-/

open Finset ArithmeticFunction GppHalfDensityZetaGauge
open scoped ArithmeticFunction.Moebius

namespace GppFiniteZetaGraph

/-- The index set `{1, …, N}`. -/
def S (N : ℕ) : Finset ℕ := Finset.Icc 1 N

theorem divisorClosed (N : ℕ) : DivisorClosed (S N) where
  zero_not_mem := by simp [S]
  dvd_mem := by
    intro n hn d hd
    simp only [S, Finset.mem_Icc] at hn ⊢
    have hn0 : n ≠ 0 := by omega
    have hd0 : d ≠ 0 := fun h => hn0 (by simpa [h] using hd)
    exact ⟨Nat.pos_of_ne_zero hd0, (Nat.le_of_dvd (by omega) hd).trans hn.2⟩

/-- The synthesis kernel `Z_N(n,d) = √(d/n) · 1_{d ∣ n}`. -/
noncomputable def zEntry (n d : ℕ) : ℝ := if d ∣ n then Real.sqrt ((d : ℝ) / n) else 0

/-- The Gram kernel `G_N(d,e) = Σ_{n ≤ N} Z_N(n,d) Z_N(n,e)`. -/
noncomputable def gram (N d e : ℕ) : ℝ := ∑ n ∈ S N, zEntry n d * zEntry n e

/-- The harmonic number `H_m = Σ_{q=1}^m 1/q`. -/
noncomputable def harm (m : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 m, (1 : ℝ) / q

/-- **The exact GCD kernel with a harmonic taper.**
`G_N(d,e) = gcd(d,e)/√(de) · H_{⌊N/lcm(d,e)⌋}` for `d, e ≥ 1`. -/
theorem gram_eq (N d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    gram N d e = (Nat.gcd d e : ℝ) / Real.sqrt ((d : ℝ) * e) * harm (N / Nat.lcm d e) := by
  set l := Nat.lcm d e with hl
  have hl0 : 0 < l := Nat.lcm_pos hd he
  have hde : (Nat.gcd d e : ℝ) * l = (d : ℝ) * e := by exact_mod_cast Nat.gcd_mul_lcm d e
  have hdepos : (0 : ℝ) < (d : ℝ) * e := by positivity
  have hsq : Real.sqrt ((d : ℝ) * e) * Real.sqrt ((d : ℝ) * e) = (d : ℝ) * e :=
    Real.mul_self_sqrt hdepos.le
  have hs0 : 0 < Real.sqrt ((d : ℝ) * e) := Real.sqrt_pos.mpr hdepos
  -- Only multiples of `l` contribute.
  have h1 : gram N d e = ∑ n ∈ (S N).filter (l ∣ ·), Real.sqrt ((d : ℝ) * e) / n := by
    unfold gram
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    by_cases hdn : d ∣ n
    · by_cases hen : e ∣ n
      · have hln : l ∣ n := Nat.lcm_dvd hdn hen
        rw [if_pos hln]
        unfold zEntry
        rw [if_pos hdn, if_pos hen, ← Real.sqrt_mul (by positivity)]
        have : (d : ℝ) / n * ((e : ℝ) / n) = (d * e) / (n : ℝ) ^ 2 := by field_simp
        rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq hn0'.le]
      · have hln : ¬ l ∣ n := fun h => hen ((Nat.dvd_lcm_right d e).trans h)
        rw [if_neg hln]; unfold zEntry; rw [if_neg hen]; simp
    · have hln : ¬ l ∣ n := fun h => hdn ((Nat.dvd_lcm_left d e).trans h)
      rw [if_neg hln]; unfold zEntry; rw [if_neg hdn]; simp
  rw [h1]
  -- Reindex `n = l q`.
  have h2 : ∑ n ∈ (S N).filter (l ∣ ·), Real.sqrt ((d : ℝ) * e) / n =
      ∑ q ∈ Finset.Icc 1 (N / l), Real.sqrt ((d : ℝ) * e) / ((l * q : ℕ) : ℝ) := by
    symm
    refine Finset.sum_nbij' (fun q => l * q) (fun n => n / l) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_Icc, S, Finset.mem_filter] at hq ⊢
      refine ⟨⟨Nat.mul_pos hl0 (by omega), ?_⟩, dvd_mul_right l q⟩
      calc l * q ≤ l * (N / l) := Nat.mul_le_mul_left _ hq.2
        _ ≤ N := Nat.mul_div_le N l
    · intro n hn
      simp only [Finset.mem_Icc, S, Finset.mem_filter] at hn ⊢
      obtain ⟨⟨hn1, hn2⟩, ⟨k, rfl⟩⟩ := hn
      rw [Nat.mul_div_cancel_left _ hl0]
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · simp [h] at hn1
        · exact h
      · exact (Nat.le_div_iff_mul_le hl0).mpr (by linarith [hn2, Nat.mul_comm l k])
    · intro q hq; simp [Nat.mul_div_cancel_left _ hl0]
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro q hq; rfl
  rw [h2]
  unfold harm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hq0 : (0 : ℝ) < q := by
    have := (Finset.mem_Icc.mp hq).1; exact_mod_cast this
  have hl0' : (0 : ℝ) < l := by exact_mod_cast hl0
  push_cast
  field_simp
  nlinarith [hde, hsq]

/-! ### The synthesized current -/

/-- The vacuum delta `e₁`. -/
noncomputable def e1 (n : ℕ) : ℝ := if n = 1 then 1 else 0

/-- The half-density von Mangoldt current `j(n) = Λ(n)/√n`. -/
noncomputable def jN (n : ℕ) : ℝ := (Λ n : ℝ) / Real.sqrt n

lemma halfVonMangoldt_e1 (N : ℕ) {n : ℕ} (hn : n ∈ S N) :
    halfVonMangoldt (S N) e1 n = jN n := by
  unfold halfVonMangoldt jN
  have h1 : (1 : ℕ) ∈ (S N).filter (· ∣ n) := by
    simp only [Finset.mem_filter, S, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨le_refl 1, by omega⟩, one_dvd n⟩
  rw [Finset.sum_eq_single 1]
  · simp [e1]
    rw [div_eq_mul_inv]
  · intro d _ hd1; simp [e1, hd1]
  · intro h; exact absurd h1 h

lemma halfZeta_e1 (N : ℕ) {n : ℕ} (hn : n ∈ S N) :
    halfZeta (S N) e1 n = 1 / Real.sqrt n := by
  unfold halfZeta
  have h1 : (1 : ℕ) ∈ (S N).filter (· ∣ n) := by
    simp only [Finset.mem_filter, S, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨le_refl 1, by omega⟩, one_dvd n⟩
  rw [Finset.sum_eq_single 1]
  · simp [e1]
  · intro d _ hd1; simp [e1, hd1]
  · intro h; exact absurd h1 h

/-- **Synthesis smooths the von Mangoldt current.** `(Z_N j)(n) = log n/√n` for `n ≤ N`. -/
theorem synth_current (N : ℕ) {n : ℕ} (hn : n ∈ S N) :
    halfZeta (S N) jN n = Real.log n / Real.sqrt n := by
  have hS := divisorClosed N
  set g : ℕ → ℝ := logMul (halfZeta (S N) e1) with hg
  have hj : ∀ m ∈ S N, halfMobius (S N) g m = jN m := by
    intro m hm
    have := half_density_gauge hS e1 hm
    have h0 : logMul e1 m = 0 := by
      unfold logMul e1
      by_cases hm1 : m = 1 <;> simp [hm1]
    rw [h0, sub_zero, halfVonMangoldt_e1 N hm] at this
    exact this
  have hZ : halfZeta (S N) jN n = halfZeta (S N) (halfMobius (S N) g) n := by
    unfold halfZeta
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd' : d ∈ S N := (Finset.mem_filter.mp hd).1
    rw [hj d hd']
  rw [hZ, halfZeta_halfMobius hS g hn, hg]
  unfold logMul
  rw [halfZeta_e1 N hn]
  ring

/-! ### Adjoints and the dual norm -/

lemma adjoint_gen (T : Finset ℕ) (k : ℕ → ℕ → ℝ) (b c : ℕ → ℝ) :
    ∑ n ∈ T, (∑ d ∈ T.filter (· ∣ n), k n d * b d) * c n =
      ∑ d ∈ T, b d * ∑ n ∈ T.filter (d ∣ ·), k n d * c n := by
  calc ∑ n ∈ T, (∑ d ∈ T.filter (· ∣ n), k n d * b d) * c n
      = ∑ n ∈ T, ∑ d ∈ T.filter (· ∣ n), k n d * b d * c n := by
        simp_rw [Finset.sum_mul]
    _ = ∑ d ∈ T, ∑ n ∈ T.filter (d ∣ ·), k n d * b d * c n := by
        refine Finset.sum_comm' ?_
        intro n d
        simp only [Finset.mem_filter]
        tauto
    _ = ∑ d ∈ T, b d * ∑ n ∈ T.filter (d ∣ ·), k n d * c n := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)

/-- The transpose `Zᵀ` of the half-density zeta synthesis. -/
noncomputable def halfZetaT (T : Finset ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ T.filter (d ∣ ·), Real.sqrt ((d : ℝ) / n) * c n

/-- The transpose `Mᵀ` of the half-density Möbius operator. -/
noncomputable def halfMobiusT (T : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ n ∈ T.filter (d ∣ ·), (μ (n / d) : ℝ) * Real.sqrt ((d : ℝ) / n) * a n

theorem halfZeta_adjoint (T : Finset ℕ) (b c : ℕ → ℝ) :
    ∑ n ∈ T, halfZeta T b n * c n = ∑ d ∈ T, b d * halfZetaT T c d := by
  unfold halfZeta halfZetaT
  exact adjoint_gen T (fun n d => Real.sqrt ((d : ℝ) / n)) b c

theorem halfMobius_adjoint (T : Finset ℕ) (b c : ℕ → ℝ) :
    ∑ n ∈ T, halfMobius T b n * c n = ∑ d ∈ T, b d * halfMobiusT T c d := by
  unfold halfMobius halfMobiusT
  have := adjoint_gen T (fun n d => (μ (n / d) : ℝ) * Real.sqrt ((d : ℝ) / n)) b c
  simpa [mul_assoc] using this

lemma sum_ind (T : Finset ℕ) {d₀ : ℕ} (hd₀ : d₀ ∈ T) (x : ℕ → ℝ) :
    ∑ d ∈ T, (if d = d₀ then (1 : ℝ) else 0) * x d = x d₀ := by
  simp [hd₀]

/-- **`Zᵀ Mᵀ = I`** on `S_N`. -/
theorem halfZetaT_halfMobiusT (N : ℕ) (a : ℕ → ℝ) {d : ℕ} (hd : d ∈ S N) :
    halfZetaT (S N) (halfMobiusT (S N) a) d = a d := by
  have hS := divisorClosed N
  set b : ℕ → ℝ := fun n => if n = d then 1 else 0 with hb
  have e1 : ∑ n ∈ S N, halfZeta (S N) b n * halfMobiusT (S N) a n =
      halfZetaT (S N) (halfMobiusT (S N) a) d := by
    rw [halfZeta_adjoint]
    exact sum_ind (S N) hd _
  have e2 : ∑ n ∈ S N, halfMobius (S N) (halfZeta (S N) b) n * a n =
      ∑ n ∈ S N, halfZeta (S N) b n * halfMobiusT (S N) a n :=
    halfMobius_adjoint (S N) (halfZeta (S N) b) a
  have e3 : ∑ n ∈ S N, halfMobius (S N) (halfZeta (S N) b) n * a n = a d := by
    have : ∑ n ∈ S N, halfMobius (S N) (halfZeta (S N) b) n * a n =
        ∑ n ∈ S N, b n * a n :=
      Finset.sum_congr rfl (fun n hn => by rw [halfMobius_halfZeta hS b hn])
    rw [this]
    exact sum_ind (S N) hd a
  rw [← e1, ← e2, e3]

/-- **The dual-norm bound.** For every `b`: `⟨a,b⟩² ≤ ‖Mᵀ a‖² · ‖Z b‖²`. -/
theorem dual_norm_le (N : ℕ) (a b : ℕ → ℝ) :
    (∑ n ∈ S N, a n * b n) ^ 2 ≤
      (∑ d ∈ S N, halfMobiusT (S N) a d ^ 2) * (∑ n ∈ S N, halfZeta (S N) b n ^ 2) := by
  have hpair : ∑ n ∈ S N, a n * b n =
      ∑ n ∈ S N, halfMobiusT (S N) a n * halfZeta (S N) b n := by
    have h := halfZeta_adjoint (S N) b (halfMobiusT (S N) a)
    calc ∑ n ∈ S N, a n * b n
        = ∑ n ∈ S N, b n * halfZetaT (S N) (halfMobiusT (S N) a) n := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [halfZetaT_halfMobiusT N a hn]; ring
      _ = ∑ n ∈ S N, halfZeta (S N) b n * halfMobiusT (S N) a n := h.symm
      _ = _ := Finset.sum_congr rfl (fun n _ => mul_comm _ _)
  rw [hpair]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The dual-norm bound is attained** at `b = M(Mᵀ a)`. There `Z b = Mᵀ a` on `S_N`, so
`⟨a,b⟩ = ‖Mᵀ a‖² = ‖Z b‖²`, and the Cauchy–Schwarz inequality above is an equality. Hence
`‖Mᵀ a‖² = a ᵀ G⁻¹ a` for `G = Zᵀ Z`. -/
theorem dual_norm_attained (N : ℕ) (a : ℕ → ℝ) :
    ∃ b : ℕ → ℝ,
      (∑ n ∈ S N, a n * b n) = ∑ d ∈ S N, halfMobiusT (S N) a d ^ 2 ∧
        (∑ n ∈ S N, halfZeta (S N) b n ^ 2) = ∑ d ∈ S N, halfMobiusT (S N) a d ^ 2 := by
  have hS := divisorClosed N
  refine ⟨halfMobius (S N) (halfMobiusT (S N) a), ?_, ?_⟩
  · have h := halfMobius_adjoint (S N) (halfMobiusT (S N) a) a
    calc ∑ n ∈ S N, a n * halfMobius (S N) (halfMobiusT (S N) a) n
        = ∑ n ∈ S N, halfMobius (S N) (halfMobiusT (S N) a) n * a n :=
          Finset.sum_congr rfl (fun n _ => mul_comm _ _)
      _ = ∑ d ∈ S N, halfMobiusT (S N) a d * halfMobiusT (S N) a d := h
      _ = _ := Finset.sum_congr rfl (fun d _ => (sq _).symm)
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [halfZeta_halfMobius hS _ hn]

/-! ### The profile formula -/

/-- **Equation (1).** For `a(n) = n^{-1/2} h(log n − t)`:
`(Mᵀ a)(d) = d^{-1/2} Σ_{m ≤ N/d} μ(m)/m · h(log m − (t − log d))`. -/
theorem mobiusT_profile (N d : ℕ) (hd : 0 < d) (h : ℝ → ℝ) (t : ℝ) :
    halfMobiusT (S N) (fun n => ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * h (Real.log n - t)) d =
      ((d : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ m ∈ Finset.Icc 1 (N / d), (μ m : ℝ) / m * h (Real.log m - (t - Real.log d)) := by
  unfold halfMobiusT
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc, S, Finset.mem_filter] at hm ⊢
    refine ⟨⟨Nat.mul_pos hd (by omega), ?_⟩, dvd_mul_right d m⟩
    calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left _ hm.2
      _ ≤ N := Nat.mul_div_le N d
  · intro n hn
    simp only [Finset.mem_Icc, S, Finset.mem_filter] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, ⟨k, rfl⟩⟩ := hn
    rw [Nat.mul_div_cancel_left _ hd]
    refine ⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by linarith [hn2, Nat.mul_comm d k])⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0] at hn1
    · exact h0
  · intro m hm; simp [Nat.mul_div_cancel_left _ hd]
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hdm : (d * m) / d = m := Nat.mul_div_cancel_left _ hd
    rw [hdm]
    push_cast
    have e1 : Real.sqrt ((d : ℝ) / ((d : ℝ) * m)) = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [show (d : ℝ) / ((d : ℝ) * m) = (m : ℝ)⁻¹ by field_simp, Real.sqrt_inv,
        Real.sqrt_eq_rpow, ← Real.rpow_neg hm0.le]
    have e2 : ((d : ℝ) * m) ^ (-(1 / 2 : ℝ)) = (d : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hd0.le hm0.le
    have e3 : Real.log ((d : ℝ) * m) - t = Real.log m - (t - Real.log d) := by
      rw [Real.log_mul hd0.ne' hm0.ne']; ring
    have e4 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) = (m : ℝ)⁻¹ := by
      rw [← Real.rpow_add hm0]; norm_num [Real.rpow_neg_one]
    rw [e1, e2, e3]
    have : (μ m : ℝ) / m * h (Real.log m - (t - Real.log d)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) =
        (μ m : ℝ) * (m : ℝ)⁻¹ * (d : ℝ) ^ (-(1 / 2 : ℝ)) * h (Real.log m - (t - Real.log d)) := by
      ring
    rw [mul_comm ((d : ℝ) ^ (-(1 / 2 : ℝ))), this, ← e4]
    ring

end GppFiniteZetaGraph
