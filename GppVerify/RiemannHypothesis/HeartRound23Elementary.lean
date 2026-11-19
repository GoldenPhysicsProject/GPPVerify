/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Round 23 elementary lemmas (F1–F7) from GPPDiscovery5

Formalization of the elementary lemmas F1–F7 of Heart of the Cosmos's Round 23 request (bridge
`CONVERSATION-week-025`, "Formalization requests from Heart (Round 23, F1–F14)"). Notation as there:
`L = log X`, `b_k = 2k + 1/2`, `T(L) = Σ e^{−b_k L}/b_k²`,
`S(L) = Σ_{n ≤ e^L} Λ(n) n^{−1/2} (L − log n)`.

* F1 `HR23_F1_exp_ineq`, `HR23_F1_arch_convexity_pos`
* F2 `HR23_F2_geometric_T`, `HR23_F2_tail`
* F3 `HR23_F3_two_tangent`
* F4 `HR23_F4_prime_sum_affine`, `HR23_F4_affine_between`, `HR23_S_continuous`
* F5 `HR23_F5a_laplace_arch`, `HR23_F5b_laplace_positive_part`, `HR23_F5c_partial_fractions`
* F6 `HR23_F6_cos_identity`, `HR23_F6_box_gram_psd`
* F7 `HR23_F7_prime_term_mean_zero`

No zeta zero is an input; everything is unconditional elementary analysis. No `sorry`, no `axiom`.
-/

namespace GppHeartRound23

open Real Set MeasureTheory Filter Topology ArithmeticFunction
open scoped Matrix

/-! ## F1 Archimedean convexity -/

/-- **F1.** For `L ≥ log 2`: `(e^L + 1)(1 − e^{−2L}) > 1`. (With `x = e^L ≥ 2` this is
`x³ − x − 1 > 0`.) -/
theorem HR23_F1_exp_ineq {L : ℝ} (hL : Real.log 2 ≤ L) :
    1 < (Real.exp L + 1) * (1 - Real.exp (-(2 * L))) := by
  have hx : 2 ≤ Real.exp L := by
    have := Real.exp_le_exp.mpr hL
    rwa [Real.exp_log (by norm_num)] at this
  have h2 : Real.exp (-(2 * L)) = ((Real.exp L) ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    have := Real.exp_nat_mul L 2
    push_cast at this
    exact this
  rw [h2]
  have hxp : 0 < Real.exp L := by positivity
  have hx2 : 0 < (Real.exp L) ^ 2 := by positivity
  rw [show (1 : ℝ) - ((Real.exp L) ^ 2)⁻¹ = ((Real.exp L) ^ 2 - 1) / (Real.exp L) ^ 2 by
    field_simp]
  rw [← mul_div_assoc, lt_div_iff₀ hx2]
  nlinarith [sq_nonneg (Real.exp L), mul_pos hxp hxp, mul_pos (mul_pos hxp hxp) hxp]

/-- **F1 (consequence).** For `L ≥ log 2`:
`e^{L/2} + e^{−L/2} − e^{−L/2}/(1 − e^{−2L}) > 0`, the second derivative of the archimedean part
`A(L) = 4(e^{L/2} − 2 + e^{−L/2}) + c₁ L + C₂ − T(L)` once `T″(L) = e^{−L/2}/(1 − e^{−2L})`
(see `HR23_F2_geometric_T`). -/
theorem HR23_F1_arch_convexity_pos {L : ℝ} (hL : Real.log 2 ≤ L) :
    0 < Real.exp (L / 2) + Real.exp (-L / 2) - Real.exp (-L / 2) / (1 - Real.exp (-(2 * L))) := by
  have hF1 := HR23_F1_exp_ineq hL
  have hq : Real.exp (-(2 * L)) < 1 := by
    have : Real.exp (-(2 * L)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith [lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hL])
    simpa using this
  have hD : 0 < 1 - Real.exp (-(2 * L)) := by linarith
  have hu : 0 < Real.exp (-L / 2) := Real.exp_pos _
  have hsplit : Real.exp (L / 2) = Real.exp (-L / 2) * Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  generalize Real.exp (-L / 2) = u at hu ⊢
  generalize Real.exp L = E at hF1 ⊢
  generalize Real.exp (-(2 * L)) = q at hD hF1 ⊢
  have hD' : 1 - q ≠ 0 := hD.ne'
  have : u * E + u - u / (1 - q) = u * (((E + 1) * (1 - q) - 1) / (1 - q)) := by
    field_simp
  rw [this]
  exact mul_pos hu (div_pos (by linarith) hD)

/-! ## F2 The geometric series for `T″` and the tail bound -/

/-- **F2.** For `L > 0`: `Σ_{k ≥ 0} e^{−(2k + 1/2)L} = e^{−L/2}/(1 − e^{−2L})`. -/
theorem HR23_F2_geometric_T {L : ℝ} (hL : 0 < L) :
    HasSum (fun k : ℕ => Real.exp (-((2 * (k : ℝ) + 1 / 2) * L)))
      (Real.exp (-L / 2) / (1 - Real.exp (-(2 * L)))) := by
  have hr0 : 0 ≤ Real.exp (-(2 * L)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * L)) < 1 := by
    have : Real.exp (-(2 * L)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-L / 2))
  have hfun : (fun k : ℕ => Real.exp (-((2 * (k : ℝ) + 1 / 2) * L)))
      = fun k : ℕ => Real.exp (-L / 2) * Real.exp (-(2 * L)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hfun, div_eq_mul_inv]
  exact h

/-- **F2 (tail).** For `L > 0` and `K ≥ 0`:
`Σ_{k ≥ K} e^{−b_k L}/b_k² ≤ e^{−b_K L}/(b_K² (1 − e^{−2L}))`, with `b_k = 2k + 1/2`
(the tail is indexed as `k ↦ k + K`). -/
theorem HR23_F2_tail {L : ℝ} (hL : 0 < L) (K : ℕ) :
    ∑' k : ℕ, Real.exp (-((2 * ((k + K : ℕ) : ℝ) + 1 / 2) * L)) / (2 * ((k + K : ℕ) : ℝ) + 1 / 2) ^ 2
      ≤ Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) /
          ((2 * (K : ℝ) + 1 / 2) ^ 2 * (1 - Real.exp (-(2 * L)))) := by
  have hr0 : 0 ≤ Real.exp (-(2 * L)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * L)) < 1 := by
    have : Real.exp (-(2 * L)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have hbK : 0 < 2 * (K : ℝ) + 1 / 2 := by positivity
  set g : ℕ → ℝ := fun k => Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) / (2 * (K : ℝ) + 1 / 2) ^ 2
    * Real.exp (-(2 * L)) ^ k with hg
  have hgs : HasSum g (Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) /
      ((2 * (K : ℝ) + 1 / 2) ^ 2 * (1 - Real.exp (-(2 * L))))) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
      (Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) / (2 * (K : ℝ) + 1 / 2) ^ 2)
    have hv : Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) / (2 * (K : ℝ) + 1 / 2) ^ 2
          * (1 - Real.exp (-(2 * L)))⁻¹
        = Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) /
          ((2 * (K : ℝ) + 1 / 2) ^ 2 * (1 - Real.exp (-(2 * L)))) := by
      rw [← div_eq_mul_inv, div_div]
    rw [← hv]
    exact this
  have hle : ∀ k : ℕ, Real.exp (-((2 * ((k + K : ℕ) : ℝ) + 1 / 2) * L))
        / (2 * ((k + K : ℕ) : ℝ) + 1 / 2) ^ 2 ≤ g k := by
    intro k
    have hbk : 2 * (K : ℝ) + 1 / 2 ≤ 2 * ((k + K : ℕ) : ℝ) + 1 / 2 := by
      push_cast; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
    have hexp : Real.exp (-((2 * ((k + K : ℕ) : ℝ) + 1 / 2) * L))
        = Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) * Real.exp (-(2 * L)) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp, hg]
    simp only
    have hden : (2 * (K : ℝ) + 1 / 2) ^ 2 ≤ (2 * ((k + K : ℕ) : ℝ) + 1 / 2) ^ 2 := by
      nlinarith
    have hpos : 0 ≤ Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) * Real.exp (-(2 * L)) ^ k := by positivity
    calc Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) * Real.exp (-(2 * L)) ^ k
          / (2 * ((k + K : ℕ) : ℝ) + 1 / 2) ^ 2
        ≤ Real.exp (-((2 * (K : ℝ) + 1 / 2) * L)) * Real.exp (-(2 * L)) ^ k
          / (2 * (K : ℝ) + 1 / 2) ^ 2 :=
          div_le_div_of_nonneg_left hpos (by positivity) hden
      _ = _ := by ring
  have hsum : Summable fun k : ℕ => Real.exp (-((2 * ((k + K : ℕ) : ℝ) + 1 / 2) * L))
      / (2 * ((k + K : ℕ) : ℝ) + 1 / 2) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hgs.summable
  calc _ ≤ ∑' k : ℕ, g k := Summable.tsum_le_tsum hle hsum hgs.summable
    _ = _ := hgs.tsum_eq

/-! ## F3 Two tangent lines -/

/-- **F3.** Let `a < b`, `f` convex on `[a, b]` with one-sided derivatives `f′(a⁺) = dₐ < 0 < d_b = f′(b⁻)`
(`HasDerivWithinAt` on `[a,b]` at the endpoints). With the crossing point
`L* = (f(b) − f(a) + dₐ a − d_b b)/(dₐ − d_b)`, every `x ∈ [a,b]` has
`f(x) ≥ f(a) + dₐ (L* − a)`. -/
theorem HR23_F3_two_tangent {f : ℝ → ℝ} {a b da db : ℝ} (hab : a < b)
    (hconv : ConvexOn ℝ (Set.Icc a b) f)
    (hda : HasDerivWithinAt f da (Set.Icc a b) a) (hdb : HasDerivWithinAt f db (Set.Icc a b) b)
    (hda0 : da < 0) (hdb0 : 0 < db) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f a + da * ((f b - f a + da * a - db * b) / (da - db) - a) ≤ f x := by
  set Lstar := (f b - f a + da * a - db * b) / (da - db) with hL
  have hne : da - db ≠ 0 := by linarith
  have hcross : f a + da * (Lstar - a) = f b + db * (Lstar - b) := by
    rw [hL]; field_simp; ring
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  -- tangent line at a: f x ≥ f a + da (x - a)
  have hta : f a + da * (x - a) ≤ f x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; simp
    · have := hconv.le_slope_of_hasDerivWithinAt ha_mem hx h hda
      rw [slope_def_field] at this
      have hxa : 0 < x - a := by linarith
      rw [le_div_iff₀ hxa] at this
      linarith
  -- tangent line at b: f x ≥ f b + db (x - b)
  have htb : f b + db * (x - b) ≤ f x := by
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; simp
    · have := hconv.slope_le_of_hasDerivWithinAt hx hb_mem h hdb
      rw [slope_def_field] at this
      have hbx : 0 < b - x := by linarith
      rw [div_le_iff₀ hbx] at this
      linarith
  by_cases hxl : x ≤ Lstar
  · nlinarith
  · rw [not_le] at hxl
    nlinarith

/-! ## F4 The prime sum is piecewise affine and continuous -/

/-- `S(L) = Σ_{n ≤ e^L} Λ(n) n^{−1/2} (L − log n)`. -/
noncomputable def HR23_S (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp L⌋₊, (vonMangoldt n) / Real.sqrt n * (L - Real.log n)

/-- `α(N) = Σ_{n ≤ N} Λ(n) n^{−1/2}`. -/
noncomputable def HR23_alpha (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n) / Real.sqrt n

/-- `β(N) = Σ_{n ≤ N} Λ(n) n^{−1/2} log n`. -/
noncomputable def HR23_beta (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n) / Real.sqrt n * Real.log n

/-- **F4 (affine on each unit).** `S(L) = α(⌊e^L⌋) L − β(⌊e^L⌋)`. -/
theorem HR23_F4_prime_sum_affine (L : ℝ) :
    HR23_S L = HR23_alpha ⌊Real.exp L⌋₊ * L - HR23_beta ⌊Real.exp L⌋₊ := by
  unfold HR23_S HR23_alpha HR23_beta
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- **F4 (between consecutive prime powers).** If `q ≤ ⌊e^L⌋` and `Λ n = 0` for every
`n` with `q < n ≤ ⌊e^L⌋` (no prime power strictly between `q` and `e^L`), then
`S(L) = α(q) L − β(q)`: the slope and intercept are those of the last prime power `q ≤ e^L`. -/
theorem HR23_F4_affine_between {L : ℝ} {q : ℕ} (hq : q ≤ ⌊Real.exp L⌋₊)
    (hgap : ∀ n : ℕ, q < n → n ≤ ⌊Real.exp L⌋₊ → vonMangoldt n = 0) :
    HR23_S L = HR23_alpha q * L - HR23_beta q := by
  rw [HR23_F4_prime_sum_affine]
  have hα : HR23_alpha ⌊Real.exp L⌋₊ = HR23_alpha q := by
    unfold HR23_alpha
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hq) fun n hn hn' => ?_
    have hn1 := Finset.mem_Icc.mp hn
    have : q < n := by
      by_contra h; exact hn' (Finset.mem_Icc.mpr ⟨hn1.1, not_lt.mp h⟩)
    simp [hgap n this hn1.2]
  have hβ : HR23_beta ⌊Real.exp L⌋₊ = HR23_beta q := by
    unfold HR23_beta
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hq) fun n hn hn' => ?_
    have hn1 := Finset.mem_Icc.mp hn
    have : q < n := by
      by_contra h; exact hn' (Finset.mem_Icc.mpr ⟨hn1.1, not_lt.mp h⟩)
    simp [hgap n this hn1.2]
  rw [hα, hβ]

/-- The same prime sum as a finite sum of positive parts, valid whenever `⌊e^L⌋ ≤ M`. -/
private theorem HR23_S_eq_posPart {L : ℝ} {M : ℕ} (hM : ⌊Real.exp L⌋₊ ≤ M) :
    HR23_S L = ∑ n ∈ Finset.Icc 1 M, (vonMangoldt n) / Real.sqrt n * max (L - Real.log n) 0 := by
  unfold HR23_S
  have hsub : Finset.Icc 1 ⌊Real.exp L⌋₊ ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc_right hM
  rw [← Finset.sum_subset hsub (f := fun n : ℕ =>
      (vonMangoldt n) / Real.sqrt n * max (L - Real.log n) 0)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 := Finset.mem_Icc.mp hn
    have hnle : (n : ℝ) ≤ Real.exp L := by
      have := Nat.floor_le (Real.exp_pos L).le
      exact le_trans (Nat.cast_le.mpr hn1.2) this
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1.1
    have : Real.log n ≤ L := by
      rw [← Real.exp_le_exp, Real.exp_log hn0]; exact hnle
    rw [max_eq_left (by linarith)]
  · intro n hn hn'
    have hn1 := Finset.mem_Icc.mp hn
    have hlt : ⌊Real.exp L⌋₊ < n := by
      by_contra h; exact hn' (Finset.mem_Icc.mpr ⟨hn1.1, not_lt.mp h⟩)
    have hgt : Real.exp L < n := by
      have h1 := Nat.lt_floor_add_one (Real.exp L)
      have h2 : ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hlt
      push_cast at h2; linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1.1
    have : L < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hgt
    rw [max_eq_right (by linarith)]; simp

/-- **F4 (continuity).** `S` is continuous on all of `ℝ` (in particular on `(0, ∞)`, including at
each `L = log q`, where the newly entering term vanishes). -/
theorem HR23_S_continuous : Continuous HR23_S := by
  rw [continuous_iff_continuousAt]
  intro L0
  set M : ℕ := ⌊Real.exp L0⌋₊ + 1 with hM
  have hcont : Continuous fun L : ℝ => ∑ n ∈ Finset.Icc 1 M,
      (vonMangoldt n) / Real.sqrt n * max (L - Real.log n) 0 := by fun_prop
  have hopen : IsOpen {L : ℝ | Real.exp L < M} :=
    isOpen_lt (by fun_prop) continuous_const
  have hmem : L0 ∈ {L : ℝ | Real.exp L < M} := by
    show Real.exp L0 < M
    rw [hM]; push_cast
    exact Nat.lt_floor_add_one _
  refine hcont.continuousAt.congr ?_
  filter_upwards [hopen.mem_nhds hmem] with L hL
  symm
  apply HR23_S_eq_posPart
  have : ⌊Real.exp L⌋₊ < M := (Nat.floor_lt (Real.exp_pos L).le).mpr hL
  exact this.le

/-! ## F5(c) Partial fractions -/

/-- **F5(c).** For `σ > 1/2`: `1/(σ + 1/2) + 1/(σ − 1/2) = 2σ/(σ² − 1/4)`. -/
theorem HR23_F5c_partial_fractions {σ : ℝ} (hσ : 1 / 2 < σ) :
    1 / (σ + 1 / 2) + 1 / (σ - 1 / 2) = 2 * σ / (σ ^ 2 - 1 / 4) := by
  have h1 : σ + 1 / 2 ≠ 0 := by linarith
  have h2 : σ - 1 / 2 ≠ 0 := by linarith
  have h3 : σ ^ 2 - 1 / 4 ≠ 0 := by
    have : σ ^ 2 - 1 / 4 = (σ + 1 / 2) * (σ - 1 / 2) := by ring
    rw [this]; exact mul_ne_zero h1 h2
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring

/-! ## F6 The box Gram matrix is PSD -/

/-- **F6 (identity).** `1 − cos x − cos y + cos (x − y) = (1 − cos x)(1 − cos y) + sin x sin y`
(equivalently `Re[(1 − e^{ix})(1 − e^{−iy})]`). -/
theorem HR23_F6_cos_identity (x y : ℝ) :
    1 - Real.cos x - Real.cos y + Real.cos (x - y)
      = (1 - Real.cos x) * (1 - Real.cos y) + Real.sin x * Real.sin y := by
  rw [Real.cos_sub]; ring

private theorem posSemidef_rank_one (c : ℝ) (hc : 0 ≤ c) {m : ℕ} (v : Fin m → ℝ) :
    (c • Matrix.vecMulVec v v).PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star v)
  simpa using h.smul hc

/-- **F6.** For real `γ₁…γ_N`, weights `w_k ≥ 0` and reals `a₁…a_m`, the matrix
`G_{ij} = Σ_k w_k (1 − cos γ_k a_i − cos γ_k a_j + cos γ_k (a_i − a_j))` is positive semidefinite
(it is `Σ_k w_k (u_k u_kᵀ + s_k s_kᵀ)` with `u_k(i) = 1 − cos γ_k a_i`, `s_k(i) = sin γ_k a_i`). -/
theorem HR23_F6_box_gram_psd {N m : ℕ} (γ w : Fin N → ℝ) (hw : ∀ k, 0 ≤ w k) (a : Fin m → ℝ) :
    (Matrix.of fun i j : Fin m => ∑ k, w k * (1 - Real.cos (γ k * a i) - Real.cos (γ k * a j)
        + Real.cos (γ k * (a i - a j)))).PosSemidef := by
  have hG : (Matrix.of fun i j : Fin m => ∑ k, w k * (1 - Real.cos (γ k * a i)
        - Real.cos (γ k * a j) + Real.cos (γ k * (a i - a j))))
      = ∑ k, ((w k) • Matrix.vecMulVec (fun i => 1 - Real.cos (γ k * a i))
            (fun i => 1 - Real.cos (γ k * a i))
          + (w k) • Matrix.vecMulVec (fun i => Real.sin (γ k * a i))
            (fun i => Real.sin (γ k * a i))) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := HR23_F6_cos_identity (γ k * a i) (γ k * a j)
    rw [← mul_sub] at this
    rw [this]
    ring
  rw [hG]
  exact Matrix.posSemidef_sum _ fun k _ =>
    (posSemidef_rank_one (w k) (hw k) _).add (posSemidef_rank_one (w k) (hw k) _)

/-! ## F7 No single prime term is passive -/

/-- **F7.** For `n ≥ 2`: `lim_{T → ∞} (1/T) ∫₀^T cos(γ log n) dγ = 0`. -/
theorem HR23_F7_prime_term_mean_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ γ in (0 : ℝ)..T, Real.cos (γ * Real.log n)) atTop (𝓝 0) := by
  have hc : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hint : ∀ T : ℝ, ∫ γ in (0 : ℝ)..T, Real.cos (γ * Real.log n)
      = Real.sin (T * Real.log n) / Real.log n := by
    intro T
    rw [intervalIntegral.integral_comp_mul_right (fun x => Real.cos x) hc.ne']
    simp [integral_cos]
    field_simp
  simp_rw [hint]
  have hbound : ∀ T : ℝ, 0 < T →
      |(1 / T) * (Real.sin (T * Real.log n) / Real.log n)| ≤ (1 / Real.log n) * (1 / T) := by
    intro T hT
    have h1 : |1 / T| = 1 / T := abs_of_pos (by positivity)
    have h2 : |Real.sin (T * Real.log n) / Real.log n| ≤ 1 / Real.log n := by
      rw [abs_div, abs_of_pos hc]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hc.le
    rw [abs_mul, h1]
    calc (1 / T) * |Real.sin (T * Real.log n) / Real.log n|
        ≤ (1 / T) * (1 / Real.log n) := by gcongr
      _ = (1 / Real.log n) * (1 / T) := by ring
  have hlim : Tendsto (fun T : ℝ => (1 / Real.log n) * (1 / T)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (Real.log n)⁻¹)).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa [one_div] using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  exact hbound T hT

/-! ## F5(a),(b) Laplace transforms of the pieces -/

/-- **F5(a).** For `σ > 1/2`:
`∫₀^∞ e^{−σL} · 4(e^{L/2} − 2 + e^{−L/2}) dL = 2/(σ(σ² − 1/4))`. -/
theorem HR23_F5a_laplace_arch {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)))
      = 2 / (σ * (σ ^ 2 - 1 / 4)) := by
  have hfun : ∀ L : ℝ, Real.exp (-σ * L) * (4 * (Real.exp (L / 2) - 2 + Real.exp (-L / 2)))
      = 4 * Real.exp (-(σ - 1 / 2) * L) - 8 * Real.exp (-σ * L)
        + 4 * Real.exp (-(σ + 1 / 2) * L) := by
    intro L
    have h1 : Real.exp (-σ * L) * Real.exp (L / 2) = Real.exp (-(σ - 1 / 2) * L) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-σ * L) * Real.exp (-L / 2) = Real.exp (-(σ + 1 / 2) * L) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination 4 * h1 + 4 * h2
  simp_rw [hfun]
  have hI : ∀ c : ℝ, 0 < c → IntegrableOn (fun L : ℝ => Real.exp (-c * L)) (Ioi 0) := fun c hc =>
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hJ : ∀ c : ℝ, 0 < c → ∫ L in Ioi (0 : ℝ), Real.exp (-c * L) = 1 / c := fun c hc => by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    simp
  have h1 := hI (σ - 1 / 2) (by linarith)
  have h2 := hI σ (by linarith)
  have h3 := hI (σ + 1 / 2) (by linarith)
  have hA : Integrable (fun L : ℝ => 4 * Real.exp (-(σ - 1 / 2) * L))
      (volume.restrict (Ioi (0 : ℝ))) := h1.const_mul 4
  have hB : Integrable (fun L : ℝ => 8 * Real.exp (-σ * L))
      (volume.restrict (Ioi (0 : ℝ))) := h2.const_mul 8
  have hC : Integrable (fun L : ℝ => 4 * Real.exp (-(σ + 1 / 2) * L))
      (volume.restrict (Ioi (0 : ℝ))) := h3.const_mul 4
  have hAB : Integrable (fun L : ℝ => 4 * Real.exp (-(σ - 1 / 2) * L) - 8 * Real.exp (-σ * L))
      (volume.restrict (Ioi (0 : ℝ))) := hA.sub hB
  rw [integral_add hAB hC, integral_sub hA hB, integral_const_mul, integral_const_mul,
    integral_const_mul, hJ _ (by linarith), hJ _ (by linarith), hJ _ (by linarith)]
  have hs1 : σ - 1 / 2 ≠ 0 := by linarith
  have hs2 : σ + 1 / 2 ≠ 0 := by linarith
  have hs3 : σ ≠ 0 := by linarith
  have hs4 : σ ^ 2 - 1 / 4 ≠ 0 := by
    have : σ ^ 2 - 1 / 4 = (σ + 1 / 2) * (σ - 1 / 2) := by ring
    rw [this]; exact mul_ne_zero hs2 hs1
  rw [show σ ^ 2 - 1 / 4 = (σ - 1 / 2) * (σ + 1 / 2) by ring]
  have hs5 : -1 + σ * 2 ≠ 0 := by linarith
  have hs6 : 1 + σ * 2 ≠ 0 := by linarith
  have hs7 : σ * 2 - 1 ≠ 0 := by linarith
  have hs8 : σ * 2 + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **F5(b).** For `σ > 0` and `a ≥ 0`: `∫₀^∞ e^{−σL} (L − a)₊ dL = e^{−σ a}/σ²`. -/
theorem HR23_F5b_laplace_positive_part {σ a : ℝ} (hσ : 0 < σ) (ha : 0 ≤ a) :
    ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * max (L - a) 0 = Real.exp (-σ * a) / σ ^ 2 := by
  have hshift : ∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * max (L - a) 0
      = ∫ L in Ioi a, Real.exp (-σ * L) * max (L - a) 0 := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi ha) fun L hL => ?_
    have hLa : L ≤ a := by
      by_contra h; exact hL.2 (Set.mem_Ioi.mpr (not_le.mp h))
    rw [max_eq_right (by linarith)]; simp
  rw [hshift]
  set g : ℝ → ℝ := fun L => -(Real.exp (-σ * L) * ((L - a) / σ + 1 / σ ^ 2)) with hg
  have hderiv : ∀ L ∈ Ioi a, HasDerivAt g (Real.exp (-σ * L) * max (L - a) 0) L := by
    intro L hL
    have hLa : 0 < L - a := by have := Set.mem_Ioi.mp hL; linarith
    have h1 : HasDerivAt (fun L : ℝ => Real.exp (-σ * L)) (Real.exp (-σ * L) * (-σ)) L := by
      have := (hasDerivAt_id L).const_mul (-σ)
      simpa using this.exp
    have h2 : HasDerivAt (fun L : ℝ => (L - a) / σ + 1 / σ ^ 2) (1 / σ) L := by
      have := ((hasDerivAt_id L).sub_const a).div_const σ
      simpa using this.add_const (1 / σ ^ 2)
    have := (h1.mul h2).neg
    rw [max_eq_left hLa.le]
    refine this.congr_deriv ?_
    field_simp
    ring
  have hlim : Tendsto g atTop (𝓝 0) := by
    have e1 : Tendsto (fun L : ℝ => Real.exp (-σ * L)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -σ < 0))
      simpa [Function.comp_def] using this
    have e2 : Tendsto (fun L : ℝ => L ^ (1 : ℝ) * Real.exp (-σ * L)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 σ hσ
    have : Tendsto (fun L : ℝ => -((1 / σ) * (L ^ (1 : ℝ) * Real.exp (-σ * L))
        + (-(a / σ) + 1 / σ ^ 2) * Real.exp (-σ * L))) atTop (𝓝 (-((1 / σ) * 0
        + (-(a / σ) + 1 / σ ^ 2) * 0))) :=
      ((e2.const_mul (1 / σ)).add (e1.const_mul _)).neg
    simp only [mul_zero, add_zero, neg_zero] at this
    refine this.congr fun L => ?_
    simp only [hg, Real.rpow_one]
    field_simp
    ring
  have hnn : ∀ L ∈ Ioi a, 0 ≤ Real.exp (-σ * L) * max (L - a) 0 := fun L _ =>
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  have hcont : ContinuousWithinAt g (Ici a) a := by
    have : Continuous g := by simp only [hg]; fun_prop
    exact this.continuousWithinAt
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp only [hg]
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end GppHeartRound23

#print axioms GppHeartRound23.HR23_F1_exp_ineq
#print axioms GppHeartRound23.HR23_F1_arch_convexity_pos
#print axioms GppHeartRound23.HR23_F2_geometric_T
#print axioms GppHeartRound23.HR23_F2_tail
#print axioms GppHeartRound23.HR23_F3_two_tangent
#print axioms GppHeartRound23.HR23_F4_prime_sum_affine
#print axioms GppHeartRound23.HR23_F4_affine_between
#print axioms GppHeartRound23.HR23_S_continuous
#print axioms GppHeartRound23.HR23_F5a_laplace_arch
#print axioms GppHeartRound23.HR23_F5b_laplace_positive_part
#print axioms GppHeartRound23.HR23_F5c_partial_fractions
#print axioms GppHeartRound23.HR23_F6_cos_identity
#print axioms GppHeartRound23.HR23_F6_box_gram_psd
#print axioms GppHeartRound23.HR23_F7_prime_term_mean_zero
