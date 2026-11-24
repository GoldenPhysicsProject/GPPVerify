/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import GppVerify.RiemannHypothesis.HeartLandauWindow

/-!
# F13S: fourth-power sampling ⇒ the F13W window hypothesis at `ε = 0` (CONDITIONAL)

The sampling reduction is **Codex's** (bridge `194c6ba`, `GPPDiscovery2@31e47f8`,
`experiments/short_reciprocal/fourth_power_windows.md`), audited PASS by **Turbo** (D4). This file
formalises it on top of F13W (`GppHeartWindow`, GPPVerify #651).

With Round 23's `D = A − S` (`GppHeartLaplace.Dfun`):

* `Dfun_cell` — for every integer `k ≥ 1` and `L ∈ [4 log k, 4 log (k+1)]`,
  `min (D (4 log k)) (D (4 log (k+1))) − 8 ≤ D L`.
  Pieces, each stated separately:
  - `S_convex_comb`: `S` is convex (a positive combination of `(L − log n)₊`);
  - `Q_convex_comb`: `T(L) − 4e^{−L/2} = Σ_{k≥1} e^{−b_k L}/b_k²` is convex on `L ≥ 0`;
  - `P_convexOn`: `M L²/2 − 4 e^{L/2}` is convex on `[a, b]` when `e^{b/2} ≤ M` — this is the
    bound `A″ ≤ e^{L/2}` in convex form (the subtracted `e^{−L/2}` of `A″` is the `k = 0` term of `T″`);
  - `Dfun_chord`: `D(x) ≥ min(D a, D b) − e^{b/2}(b − a)²/8` on `[a, b] ⊆ [0, ∞)`;
  - `cell_penalty`: `e^{b/2}(b−a)²/8 = 2(k+1)² log(1+1/k)² ≤ 8`.
  The `k = 1` cell (`a = 0`) needs no limit: no second derivative is ever evaluated; only
  convexity inequalities between the three points are used, and `D(0) = 0` is a genuine value.
* `window_of_samples` — if for some `B` and arbitrarily large `K`, `−B ≤ D(4 log k)` for every
  integer `k ∈ [K, ⌈K^{3/2}⌉]`, then the F13W hypothesis holds at `ε = 0`, `δ = ½`, `C = B + 8`.
* `F13S_xiE_ne_zero`, `F13S_riemannZeta_ne_zero` — under that sampling floor, `ξ_E ≠ 0` on
  `Re s > ½`, and `ζ(s) ≠ 0` on `Re s > ½`, `s ≠ 1`.

**CONDITIONAL.** A floor on the samples `D(4 log k)` is RH-strength; it is **not** proved here or
anywhere in this repository. No zeta zero is an input; no `sorry`, no `axiom`.
-/

namespace GppHeartSampling

open Set GppHeartLaplace GppHeartRound23 GppHeartWindow GppHeartReduction

/-! ### Convexity along a pair of points, passed through `tsum` -/

theorem tsum_convex_comb {f : ℕ → ℝ → ℝ} {x y θ : ℝ}
    (hf : ∀ n, f n (θ * x + (1 - θ) * y) ≤ θ * f n x + (1 - θ) * f n y)
    (hx : Summable (fun n => f n x)) (hy : Summable (fun n => f n y))
    (hz : Summable (fun n => f n (θ * x + (1 - θ) * y))) :
    ∑' n, f n (θ * x + (1 - θ) * y) ≤ θ * ∑' n, f n x + (1 - θ) * ∑' n, f n y := by
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hx.mul_left θ) (hy.mul_left _)]
  exact Summable.tsum_le_tsum hf hz ((hx.mul_left θ).add (hy.mul_left _))

theorem posPart_convex_comb (c x y θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    max (θ * x + (1 - θ) * y - c) 0 ≤ θ * max (x - c) 0 + (1 - θ) * max (y - c) 0 := by
  have h1 : 0 ≤ 1 - θ := by linarith
  apply max_le
  · have := mul_le_mul_of_nonneg_left (le_max_left (x - c) 0) hθ0
    have := mul_le_mul_of_nonneg_left (le_max_left (y - c) 0) h1
    nlinarith
  · have := mul_nonneg hθ0 (le_max_right (x - c) 0)
    have := mul_nonneg h1 (le_max_right (y - c) 0)
    linarith

theorem summable_S_terms (L : ℝ) : Summable (fun n : ℕ => aN n * max (L - Real.log n) 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp L⌋₊ + 1))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have hn' : Real.exp L < n := by
    have := Nat.lt_floor_add_one (Real.exp L)
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos L) hn'
  have : L < Real.log n := by rw [Real.lt_log_iff_exp_lt hn0]; exact hn'
  rw [max_eq_right (by linarith), mul_zero]

/-- `S` is convex. -/
theorem S_convex_comb (x y θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    HR23_S (θ * x + (1 - θ) * y) ≤ θ * HR23_S x + (1 - θ) * HR23_S y := by
  rw [S_eq_tsum, S_eq_tsum, S_eq_tsum]
  refine tsum_convex_comb (f := fun n L => aN n * max (L - Real.log n) 0) (fun n => ?_)
    (summable_S_terms x) (summable_S_terms y) (summable_S_terms _)
  show aN n * max (θ * x + (1 - θ) * y - Real.log n) 0 ≤
    θ * (aN n * max (x - Real.log n) 0) + (1 - θ) * (aN n * max (y - Real.log n) 0)
  have := posPart_convex_comb (Real.log n) x y θ hθ0 hθ1
  have ha := aN_nonneg n
  have := mul_le_mul_of_nonneg_left this ha
  linarith

/-- `Q(L) = Σ_k e^{−b_{k+1} L}/b_{k+1}²` (that is, `T(L) − 4 e^{−L/2}`). -/
noncomputable def Qfun (L : ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(bk (k + 1) * L)) / bk (k + 1) ^ 2

theorem summable_T_terms {L : ℝ} (hL : 0 ≤ L) :
    Summable (fun k : ℕ => Real.exp (-(bk k * L)) / bk k ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by have := bk_pos k; positivity) (fun k => ?_)
    summable_inv_bk_sq
  have hb := bk_pos k
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem T_eq_Q {L : ℝ} (hL : 0 ≤ L) : Tfun L = 4 * Real.exp (-L / 2) + Qfun L := by
  unfold Tfun Qfun
  rw [(summable_T_terms hL).tsum_eq_zero_add]
  have h0 : bk 0 = 1 / 2 := by simp [bk]
  rw [h0, show -(1 / 2 * L) = -L / 2 by ring]
  congr 1
  norm_num
  ring

theorem Q_convex_comb {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Qfun (θ * x + (1 - θ) * y) ≤ θ * Qfun x + (1 - θ) * Qfun y := by
  have h1 : 0 ≤ 1 - θ := by linarith
  have hz : 0 ≤ θ * x + (1 - θ) * y := by positivity
  have hs : ∀ {L : ℝ}, 0 ≤ L →
      Summable (fun k : ℕ => Real.exp (-(bk (k + 1) * L)) / bk (k + 1) ^ 2) := fun hL =>
    (summable_nat_add_iff 1).mpr (summable_T_terms hL)
  refine tsum_convex_comb (f := fun k L => Real.exp (-(bk (k + 1) * L)) / bk (k + 1) ^ 2)
    (fun k => ?_) (hs hx) (hs hy) (hs hz)
  show Real.exp (-(bk (k + 1) * (θ * x + (1 - θ) * y))) / bk (k + 1) ^ 2 ≤
    θ * (Real.exp (-(bk (k + 1) * x)) / bk (k + 1) ^ 2) +
      (1 - θ) * (Real.exp (-(bk (k + 1) * y)) / bk (k + 1) ^ 2)
  have hb := bk_pos (k + 1)
  have hc := convexOn_exp.2 (mem_univ (-(bk (k + 1) * x))) (mem_univ (-(bk (k + 1) * y)))
    hθ0 h1 (by ring)
  simp only [smul_eq_mul] at hc
  have he : -(bk (k + 1) * (θ * x + (1 - θ) * y)) =
      θ * -(bk (k + 1) * x) + (1 - θ) * -(bk (k + 1) * y) := by ring
  rw [he]
  have hb2 : 0 < bk (k + 1) ^ 2 := by positivity
  rw [div_le_iff₀ hb2]
  have : θ * (Real.exp (-(bk (k + 1) * x)) / bk (k + 1) ^ 2) +
      (1 - θ) * (Real.exp (-(bk (k + 1) * y)) / bk (k + 1) ^ 2) =
      (θ * Real.exp (-(bk (k + 1) * x)) + (1 - θ) * Real.exp (-(bk (k + 1) * y))) /
        bk (k + 1) ^ 2 := by ring
  rw [this, div_mul_cancel₀ _ hb2.ne']
  exact hc

/-! ### The archimedean part: `A″ ≤ e^{L/2}` in convex form -/

/-- `P_M(L) = M L²/2 − 4 e^{L/2}`. -/
noncomputable def Pfun (M L : ℝ) : ℝ := M * L ^ 2 / 2 - 4 * Real.exp (L / 2)

theorem hasDerivAt_Pfun (M L : ℝ) :
    HasDerivAt (Pfun M) (M * L - 2 * Real.exp (L / 2)) L := by
  have h := ((hasDerivAt_pow 2 L).const_mul (M / 2)).sub
    ((((hasDerivAt_id L).div_const 2).exp).const_mul 4)
  have he : ((fun y => M / 2 * y ^ 2) - fun y => 4 * Real.exp (id y / 2)) = Pfun M := by
    funext x; simp only [Pfun, id, Pi.sub_apply]; ring
  rw [he] at h
  have hv : M / 2 * ((2 : ℕ) * L ^ (2 - 1)) - 4 * (Real.exp (id L / 2) * (1 / 2)) =
      M * L - 2 * Real.exp (L / 2) := by
    simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
  rwa [hv] at h

/-- `M L²/2 − 4 e^{L/2}` is convex on `[a, b]` once `e^{b/2} ≤ M`. -/
theorem P_convexOn {a b M : ℝ} (hM : Real.exp (b / 2) ≤ M) : ConvexOn ℝ (Icc a b) (Pfun M) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc a b)
    (fun x _ => (hasDerivAt_Pfun M x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_Pfun M x).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Icc]
  intro x _ y hy hxy
  rw [(hasDerivAt_Pfun M x).deriv, (hasDerivAt_Pfun M y).deriv]
  have h1 : Real.exp (x / 2) = Real.exp (y / 2) * Real.exp ((x - y) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (x - y) / 2 + 1 ≤ Real.exp ((x - y) / 2) := Real.add_one_le_exp _
  have h3 : Real.exp (y / 2) ≤ M :=
    le_trans (Real.exp_le_exp.mpr (by linarith [hy.2])) hM
  have hey := Real.exp_pos (y / 2)
  have h4 : Real.exp (y / 2) * ((x - y) / 2 + 1) ≤ Real.exp (x / 2) := by
    rw [h1]; exact mul_le_mul_of_nonneg_left h2 hey.le
  have h5 : Real.exp (y / 2) * (y - x) ≤ M * (y - x) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

/-! ### The chord bound for `D` -/

theorem Dfun_eq {L : ℝ} (hL : 0 ≤ L) :
    Dfun L = 4 * Real.exp (L / 2) - 8 + c1 * L + C2 - Qfun L - HR23_S L := by
  unfold Dfun; rw [T_eq_Q hL]; ring

/-- **Chord bound.** On `[a, b] ⊆ [0, ∞)`, `D(x) ≥ min(D a, D b) − e^{b/2}(b − a)²/8`. -/
theorem Dfun_chord {a b x : ℝ} (ha : 0 ≤ a) (hab : a < b) (hx : x ∈ Icc a b) :
    min (Dfun a) (Dfun b) - Real.exp (b / 2) * (b - a) ^ 2 / 8 ≤ Dfun x := by
  set M := Real.exp (b / 2) with hMdef
  set θ := (b - x) / (b - a) with hθdef
  have hba : 0 < b - a := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hx.2]) hba.le
  have hθ1 : θ ≤ 1 := (div_le_one hba).mpr (by linarith [hx.1])
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hxθ : x = θ * a + (1 - θ) * b := by
    rw [hθdef]; field_simp; ring
  have hb0 : 0 ≤ b := by linarith
  have hP := (P_convexOn (a := a) (b := b) (le_refl M)).2 (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hθ0 h1θ (by ring)
  simp only [smul_eq_mul] at hP
  have hQ := Q_convex_comb ha hb0 hθ0 hθ1
  have hS := S_convex_comb a b θ hθ0 hθ1
  rw [← hxθ] at hP hQ hS
  rw [Dfun_eq (L := x) (by linarith [hx.1]), Dfun_eq ha, Dfun_eq hb0]
  simp only [Pfun] at hP
  have hmin : min (4 * Real.exp (a / 2) - 8 + c1 * a + C2 - Qfun a - HR23_S a)
      (4 * Real.exp (b / 2) - 8 + c1 * b + C2 - Qfun b - HR23_S b) ≤
      θ * (4 * Real.exp (a / 2) - 8 + c1 * a + C2 - Qfun a - HR23_S a) +
      (1 - θ) * (4 * Real.exp (b / 2) - 8 + c1 * b + C2 - Qfun b - HR23_S b) := by
    have := min_le_left (4 * Real.exp (a / 2) - 8 + c1 * a + C2 - Qfun a - HR23_S a)
      (4 * Real.exp (b / 2) - 8 + c1 * b + C2 - Qfun b - HR23_S b)
    have := min_le_right (4 * Real.exp (a / 2) - 8 + c1 * a + C2 - Qfun a - HR23_S a)
      (4 * Real.exp (b / 2) - 8 + c1 * b + C2 - Qfun b - HR23_S b)
    nlinarith
  have hid : x ^ 2 - θ * a ^ 2 - (1 - θ) * b ^ 2 = -(θ * (1 - θ) * (b - a) ^ 2) := by
    rw [hxθ]; ring
  have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  have hpen : M * (θ * (1 - θ) * (b - a) ^ 2) ≤ M * ((b - a) ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (b - a)]) hM0
  have hlin : c1 * x = θ * (c1 * a) + (1 - θ) * (c1 * b) := by rw [hxθ]; ring
  have hMx : M * x ^ 2 = θ * (M * a ^ 2) + (1 - θ) * (M * b ^ 2) - M * (θ * (1 - θ) * (b - a) ^ 2) := by
    have : M * (x ^ 2 - θ * a ^ 2 - (1 - θ) * b ^ 2) = M * -(θ * (1 - θ) * (b - a) ^ 2) := by
      rw [hid]
    linarith
  nlinarith

/-- **Cell penalty.** For `k ≥ 1`, `e^{b/2}(b − a)²/8 ≤ 8` with `a = 4 log k`, `b = 4 log (k+1)`
(it equals `2(k+1)² log(1+1/k)²`). -/
theorem cell_penalty {k : ℝ} (hk : 1 ≤ k) :
    Real.exp (4 * Real.log (k + 1) / 2) * (4 * Real.log (k + 1) - 4 * Real.log k) ^ 2 / 8 ≤ 8 := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hexp : Real.exp (4 * Real.log (k + 1) / 2) = (k + 1) ^ 2 := by
    rw [show 4 * Real.log (k + 1) / 2 = Real.log (k + 1) + Real.log (k + 1) by ring,
      Real.exp_add, Real.exp_log hk1]; ring
  set u := Real.log (k + 1) - Real.log k with hu
  have hu_eq : u = Real.log ((k + 1) / k) := by rw [hu, Real.log_div hk1.ne' hk0.ne']
  have hu0 : 0 ≤ u := by
    rw [hu_eq]; exact Real.log_nonneg (by rw [le_div_iff₀ hk0]; linarith)
  have hu1 : u ≤ 1 / k := by
    rw [hu_eq]
    have := Real.log_le_sub_one_of_pos (show 0 < (k + 1) / k by positivity)
    have h' : (k + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have hku : k * u ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hu1 hk0.le
    rwa [mul_one_div_cancel hk0.ne'] at this
  have hu1' : u ≤ 1 := le_trans hu1 (by rw [div_le_one hk0]; exact hk)
  have hku2 : (k + 1) * u ≤ 2 := by nlinarith
  have hsq : ((k + 1) * u) ^ 2 ≤ 4 := by nlinarith [mul_nonneg hk1.le hu0]
  rw [hexp, show 4 * Real.log (k + 1) - 4 * Real.log k = 4 * u by rw [hu]; ring]
  nlinarith

/-- **The cell lemma.** For `k ≥ 1` and `L ∈ [4 log k, 4 log (k+1)]`,
`min (D (4 log k)) (D (4 log (k+1))) − 8 ≤ D L`. -/
theorem Dfun_cell {k : ℕ} (hk : 1 ≤ k) {L : ℝ}
    (hL : L ∈ Icc (4 * Real.log k) (4 * Real.log ((k : ℝ) + 1))) :
    min (Dfun (4 * Real.log k)) (Dfun (4 * Real.log ((k : ℝ) + 1))) - 8 ≤ Dfun L := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 ≤ 4 * Real.log k := by have := Real.log_nonneg hk'; linarith
  have hab : 4 * Real.log k < 4 * Real.log ((k : ℝ) + 1) := by
    have := Real.log_lt_log (by linarith) (show (k : ℝ) < k + 1 by linarith); linarith
  have hc := Dfun_chord ha hab hL
  have hp := cell_penalty hk'
  linarith

/-! ### Sampling at fourth powers ⇒ the F13W window hypothesis -/

/-- **Sampling ⇒ window (Codex's reduction).** A floor `−B ≤ D(4 log k)` at every integer
`k ∈ [K, ⌈K^{3/2}⌉]`, for arbitrarily large `K`, gives the F13W hypothesis at `ε = 0`, `δ = ½`
with `C = B + 8`: the samples cover `[4 log K, 6 log K]`, and each cell costs at most `8`. -/
theorem window_of_samples {B : ℝ}
    (hB : ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ ∀ k : ℕ, K ≤ k → k ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ →
      -B ≤ Dfun (4 * Real.log k)) :
    ∀ L₀ : ℝ, ∃ L : ℝ, L₀ ≤ L ∧
      ∀ L' ∈ Icc L (3 / 2 * L), -(B + 8) * Real.exp (0 * L') ≤ Dfun L' := by
  intro L₀
  obtain ⟨K, hK0, hK⟩ := hB (⌈Real.exp (L₀ / 4)⌉₊ + 1)
  have hK1 : 1 ≤ K := by omega
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr
  refine ⟨4 * Real.log K, ?_, ?_⟩
  · have h1 : Real.exp (L₀ / 4) ≤ K := by
      have := Nat.le_ceil (Real.exp (L₀ / 4))
      have h2 : ((⌈Real.exp (L₀ / 4)⌉₊ : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : _ ≤ K)
      linarith
    have := (Real.le_log_iff_exp_le hKpos).mpr h1
    linarith
  intro L' hL'
  rw [zero_mul, Real.exp_zero, mul_one]
  have hlo : Real.log K ≤ L' / 4 := by linarith [hL'.1]
  have hhi : L' / 4 ≤ Real.log K * (3 / 2) := by linarith [hL'.2]
  set k := ⌊Real.exp (L' / 4)⌋₊ with hkdef
  have hepos := Real.exp_pos (L' / 4)
  have hKe : (K : ℝ) ≤ Real.exp (L' / 4) := by
    rw [← Real.exp_log hKpos]; exact Real.exp_le_exp.mpr hlo
  have hkK : K ≤ k := Nat.le_floor hKe
  have hk1 : 1 ≤ k := le_trans hK1 hkK
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hk_le : (k : ℝ) ≤ Real.exp (L' / 4) := Nat.floor_le hepos.le
  have hk_lt : Real.exp (L' / 4) < k + 1 := Nat.lt_floor_add_one _
  have hpow : Real.exp (L' / 4) ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hKpos]; exact Real.exp_le_exp.mpr hhi
  have hceil : (K : ℝ) ^ ((3 : ℝ) / 2) ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := Nat.le_ceil _
  have hk_ceil : k ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have : (k : ℝ) ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by linarith
    exact_mod_cast this
  have hA : 4 * Real.log k ≤ L' := by
    have := (Real.log_le_iff_le_exp hkpos).mpr hk_le; linarith
  have hBk : -B ≤ Dfun (4 * Real.log k) := hK k hkK hk_ceil
  by_cases hk2 : k + 1 ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊
  · have hB2 := hK (k + 1) (by omega) hk2
    push_cast at hB2
    have hb : L' ≤ 4 * Real.log ((k : ℝ) + 1) := by
      have := (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < k + 1)).mpr hk_lt.le
      linarith
    have hc := Dfun_cell hk1 ⟨hA, hb⟩
    have := le_min hBk hB2
    linarith
  · have hge : ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ ≤ k := by omega
    have hge' : ((⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hge
    have heq : Real.exp (L' / 4) = k := le_antisymm (by linarith) hk_le
    have hL'eq : L' = 4 * Real.log k := by
      rw [← heq, Real.log_exp]; ring
    rw [hL'eq]; linarith

/-! ### The conditional corollaries -/

/-- **F13S (CONDITIONAL).** If for some `B` and arbitrarily large `K`, `−B ≤ D(4 log k)` at every
integer `k ∈ [K, ⌈K^{3/2}⌉]`, then `ξ_E` has no zeros on `Re s > ½`. The hypothesis is
RH-strength and is not proved. -/
theorem F13S_xiE_ne_zero
    (hS : ∃ B : ℝ, ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ ∀ k : ℕ, K ≤ k →
      k ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ → -B ≤ Dfun (4 * Real.log k)) :
    ∀ s : ℂ, 1 / 2 < s.re → xiE s ≠ 0 := by
  obtain ⟨B, hB⟩ := hS
  intro s hs
  exact F13W_three_halves (ε := 0) (C := B + 8) le_rfl (window_of_samples hB) s (by simpa using hs)

/-- **F13S for `riemannZeta` (CONDITIONAL).** Same hypothesis; `ζ(s) ≠ 0` on `Re s > ½`, `s ≠ 1`. -/
theorem F13S_riemannZeta_ne_zero
    (hS : ∃ B : ℝ, ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ ∀ k : ℕ, K ≤ k →
      k ≤ ⌈(K : ℝ) ^ ((3 : ℝ) / 2)⌉₊ → -B ≤ Dfun (4 * Real.log k)) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨B, hB⟩ := hS
  intro s hs hs1
  refine F13W_riemannZeta_ne_zero (ε := 0) (δ := 1 / 2) (C := B + 8) le_rfl (by norm_num) ?_ s
    (by simpa using hs) hs1
  intro L₀
  obtain ⟨L, hL, hb⟩ := window_of_samples hB L₀
  exact ⟨L, hL, fun L' hL' => hb L' (by norm_num at hL' ⊢; exact hL')⟩

#print axioms GppHeartSampling.Dfun_chord
#print axioms GppHeartSampling.Dfun_cell
#print axioms GppHeartSampling.window_of_samples
#print axioms GppHeartSampling.F13S_xiE_ne_zero
#print axioms GppHeartSampling.F13S_riemannZeta_ne_zero

end GppHeartSampling
