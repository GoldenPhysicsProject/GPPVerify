/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok, GPPDiscovery5)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Topology.Compactness.Compact
import GppVerify.RiemannHypothesis.OneSided
import GppVerify.RiemannHypothesis.HeartLandauReduction

/-!
# The windowed Landau reduction (F13W)

F13 (`HeartLandauReduction`) needs the one-sided bound `D(L) ≥ −C e^{εL}` for *all* `L > 0`.
F13W needs it only on **windows**: for arbitrarily large `L`, on the whole interval
`L' ∈ [L, (1+δ)L]` (any fixed `δ > 0`). In `Y = e^L` these are the windows `[Y, Y^{1+δ}]`;
`δ = ½` matches the `[Y, Y^{3/2}]` windows of Levent Alpöge's release
(`Deduction.zeroFree_of_rpow_window`, `Deduction.landau_window`), whose architecture this file
follows and credits.

* `F13W_xiE_ne_zero` — windows `[L,(1+δ)L]` ⇒ `ξ_E(s) ≠ 0` on `Re s > ½ + ε` (any `ε ≥ 0`).
* `F13W_three_halves` — the `δ = ½` case.
* `F13W_riemannZeta_ne_zero` — the same for Mathlib's `riemannZeta` off `s = 1`.

The window hypothesis is implied by F13's global one, so F13W strictly generalises F13.
The converse (zero-free half-plane ⇒ window bound) is **not** proved here.

**Route (Taylor coefficients, not Pringsheim).** Put `z = σ + iγ`, `M_k(z) = ∫₀^∞ tᵏ e^{−zt} D(t) dt`.
1. *Basic inequality* (`norm_momentLap_signed_le`): `‖M_k(z)‖ ≤ ‖M_k(σ)‖ + 2∫ tᵏe^{−σt} D⁻`,
   splitting `D = D⁺ − D⁻`.
2. *Window + tails* (`realMom_gn_le`, `tail_params`): on the window `D⁻ ≤ C e^{θt}` and the kernel
   `tᵏe^{−(σ−θ)t}/k! ≤ (σ−θ)^{−k}`; off the window two Chernoff shifts by `±l` and a choice
   `k ≈ U·l(σ−τ+l)/(l−τ)` make the kernel `≤ k!/σᵏ` times `e^{−τt}`, paid for by the absolute
   Laplace integral of `D` at `τ = 3/2`.
3. *Geometry* (`disc_and_pole`, `nearest_unique`): no real zeros of `ξ_E` on `(0,∞)` gives a pole-free
   disc about `σ` and, after a generic vertical shift `γ`, a unique nearest pole `ρ` to `z`, closer
   than that disc's radius.
4. *Coefficients* (`pole_lower_bound`, `cauchy_bound`): the pole forces `‖Φ^{(k)}(z)‖/k! ≳ ‖z−ρ‖^{−k}`,
   while 1–2 bound it by `poly(k)·e^{−k}` with `e > ‖z−ρ‖`: contradiction (`window_landau`).
5. *Instance*: `Φ(z) = (ξ_E′/ξ_E)(½+z)/z²` equals the Laplace transform of `D` on `Re z > ½`
   (complex F11 by the identity theorem, `PhiD_eq_momentLap`); zeros of `ξ_E` give simple poles
   with residue `m/ρ²` (`PhiD_pole`), isolated (`isoRight_ZD`), never real (`ZD_im_ne`).

Credit: the windowed Landau architecture (Taylor coefficients at `σ + iγ`, the window/tail split,
the dichotomy and the nearest-pole tie-break) is L. Alpöge's, from his public RH/GRH Lean release;
the proofs here are written fresh for our signed `D` with a lower window bound.
No zeta zero is an input; no `sorry`, no `axiom`.
-/

open Complex MeasureTheory Set Filter Topology
open RhWaveLean (momentLap hasDerivAt_momentLap integrable_momentLap integrable_momentLap_real')

namespace GppHeartWindow

/-- **Tail parameters.** For `δ, τ > 0` there are `σ ≥ σ₁` and `τ < l < σ - τ` such that for every
`U ≥ 1` some `k ≥ U` makes both Chernoff factors at most `1` relative to `σ^k`. -/
theorem tail_params {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (σ₁ : ℝ) :
    ∃ σ l : ℝ, σ₁ ≤ σ ∧ τ < l ∧ τ + l < σ ∧ ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      σ ^ k * Real.exp (l * U) ≤ (σ - τ + l) ^ k ∧
      σ ^ k ≤ (σ - τ - l) ^ k * Real.exp (l * ((1 + δ) * U)) := by
  set l : ℝ := τ * (2 + δ) / δ + 1 with hl
  have hδl : δ * l = τ * (2 + δ) + δ := by rw [hl]; field_simp
  have hlτ : τ < l := by
    have : τ * (2 + δ) / δ ≥ τ := by rw [ge_iff_le, le_div_iff₀ hδ]; nlinarith
    linarith
  have hl1 : 1 ≤ l := by
    have : 0 ≤ τ * (2 + δ) / δ := by positivity
    linarith
  have hl0 : 0 < l := by linarith
  have hA : 0 < l - τ := by linarith
  have hB : 0 < τ + l := by linarith
  set s : ℝ := l * (1 + δ) / (τ + l) - l / (l - τ) with hs
  have hspos : 0 < s := by
    rw [hs, sub_pos, div_lt_div_iff₀ hA hB]
    nlinarith
  set c₀ : ℝ := -(l ^ 2 * (1 + δ) / (τ + l)) - l ^ 2 / (l - τ) - 1 with hc₀
  set b : ℝ := max (l + 1) (max (σ₁ - τ) ((1 - c₀) / s)) with hb
  have hb1 : l + 1 ≤ b := le_max_left _ _
  have hb2 : σ₁ - τ ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hb3 : (1 - c₀) / s ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  set α : ℝ := l * (b + l) / (l - τ) with hα
  set β : ℝ := l * (1 + δ) * (b - l) / (τ + l) with hβ
  have hαβ : α + 1 ≤ β := by
    have e : β - α - 1 = s * b + c₀ := by
      rw [hα, hβ, hs, hc₀]; field_simp; ring
    have : 1 - c₀ ≤ s * b := by rw [div_le_iff₀ hspos] at hb3; linarith
    linarith
  have hα1 : 1 ≤ α := by
    rw [hα, le_div_iff₀ hA]; nlinarith
  refine ⟨b + τ, l, by linarith, hlτ, by linarith, fun U hU => ?_⟩
  have hbσ : b + τ - τ = b := by ring
  rw [hbσ]
  set k : ℕ := ⌈U * α⌉₊ with hk
  have hk1 : U * α ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < U * α + 1 := Nat.ceil_lt_add_one (by positivity)
  have hb0 : 0 < b := by linarith
  have hσ0 : 0 < b + τ := by linarith
  have hUk : U ≤ k := (le_mul_of_one_le_right (by linarith) hα1).trans hk1
  refine ⟨k, hUk, ?_, ?_⟩
  · -- `σ ≤ (b + l) e^{-y}`, `y = (l - τ)/(b + l)`
    set y : ℝ := (l - τ) / (b + l) with hy
    have hbl : 0 < b + l := by linarith
    have h1 : b + τ ≤ (b + l) * Real.exp (-y) := by
      have := Real.one_sub_le_exp_neg y
      have e : (b + l) * (1 - y) = b + τ := by rw [hy]; field_simp; ring
      nlinarith
    have h2 : (b + τ) ^ k ≤ (b + l) ^ k * Real.exp (-(k * y)) := by
      calc (b + τ) ^ k ≤ ((b + l) * Real.exp (-y)) ^ k := pow_le_pow_left₀ hσ0.le h1 k
        _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    have h3 : l * U ≤ k * y := by
      have : U * α * y = l * U := by rw [hα, hy]; field_simp
      have hy0 : 0 ≤ y := by positivity
      have := mul_le_mul_of_nonneg_right hk1 hy0
      linarith
    calc (b + τ) ^ k * Real.exp (l * U) ≤ (b + l) ^ k * Real.exp (-(k * y)) * Real.exp (l * U) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = (b + l) ^ k * Real.exp (l * U - k * y) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (b + l) ^ k * 1 := by
          gcongr; rw [Real.exp_le_one_iff]; linarith
      _ = _ := by rw [mul_one]
  · set w : ℝ := (τ + l) / (b - l) with hw
    have hbl : 0 < b - l := by linarith
    have h1 : b + τ ≤ (b - l) * Real.exp w := by
      have := Real.add_one_le_exp w
      have e : (b - l) * (w + 1) = b + τ := by rw [hw]; field_simp; ring
      nlinarith
    have h2 : (b + τ) ^ k ≤ (b - l) ^ k * Real.exp (k * w) := by
      calc (b + τ) ^ k ≤ ((b - l) * Real.exp w) ^ k := pow_le_pow_left₀ hσ0.le h1 k
        _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]
    have h3 : k * w ≤ l * ((1 + δ) * U) := by
      have hw0 : 0 ≤ w := by positivity
      have e : U * β * w = l * ((1 + δ) * U) := by rw [hβ, hw]; field_simp
      have h4 : (k : ℝ) ≤ U * β := by
        have h5 := mul_le_mul_of_nonneg_left hαβ (by linarith : (0:ℝ) ≤ U)
        have h6 : U * (α + 1) = U * α + U := by ring
        linarith
      have := mul_le_mul_of_nonneg_right h4 hw0
      linarith
    calc (b + τ) ^ k ≤ (b - l) ^ k * Real.exp (k * w) := h2
      _ ≤ _ := by gcongr

section Signed

variable {g : ℝ → ℝ} {σ₀ : ℝ}

/-- Positive and negative parts. -/
noncomputable def gp (g : ℝ → ℝ) (t : ℝ) : ℝ := max (g t) 0
noncomputable def gn (g : ℝ → ℝ) (t : ℝ) : ℝ := max (-g t) 0

theorem gp_nonneg (t : ℝ) : 0 ≤ gp g t := le_max_right _ _
theorem gn_nonneg (t : ℝ) : 0 ≤ gn g t := le_max_right _ _
theorem gp_sub_gn (t : ℝ) : gp g t - gn g t = g t := by
  unfold gp gn
  rcases le_total 0 (g t) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
theorem gn_le_abs (t : ℝ) : gn g t ≤ |g t| := max_le (neg_le_abs _) (abs_nonneg _)

/-- Absolute Laplace convergence of the signed function. -/
def SignedConv (g : ℝ → ℝ) (σ₀ : ℝ) : Prop :=
  ∀ τ : ℝ, σ₀ < τ → IntegrableOn (fun t : ℝ => Real.exp (-τ * t) * g t) (Ioi 0)

theorem conv_gp (hg : SignedConv g σ₀) :
    ∀ τ : ℝ, σ₀ < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * gp g t : ℝ) : ℂ)) (Ioi 0) volume := by
  intro τ hτ
  have h := (hg τ hτ).pos_part
  refine (h.congr ?_).ofReal
  filter_upwards with t
  show max (Real.exp (-τ * t) * g t) 0 = Real.exp (-τ * t) * max (g t) 0
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]

theorem conv_gn (hg : SignedConv g σ₀) :
    ∀ τ : ℝ, σ₀ < τ → IntegrableOn (fun t : ℝ ↦ ((Real.exp (-τ * t) * gn g t : ℝ) : ℂ)) (Ioi 0) volume := by
  intro τ hτ
  have h := (hg τ hτ).neg_part
  refine (h.congr ?_).ofReal
  filter_upwards with t
  show max (-(Real.exp (-τ * t) * g t)) 0 = Real.exp (-τ * t) * max (-g t) 0
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero, mul_neg]

theorem momentLap_split (hg : SignedConv g σ₀) (n : ℕ) {w : ℂ} (hw : σ₀ < w.re) :
    momentLap g n w = momentLap (gp g) n w - momentLap (gn g) n w := by
  have h1 := integrable_momentLap (fun t => gp_nonneg (g := g) t) (conv_gp hg) n hw
  have h2 := integrable_momentLap (fun t => gn_nonneg (g := g) t) (conv_gn hg) n hw
  unfold momentLap
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [← mul_sub, ← Complex.ofReal_sub, gp_sub_gn]

theorem hasDerivAt_momentLap_signed (hg : SignedConv g σ₀) (n : ℕ) {w : ℂ} (hw : σ₀ < w.re) :
    HasDerivAt (momentLap g n) (-(momentLap g (n + 1) w)) w := by
  have hP := hasDerivAt_momentLap (fun t => gp_nonneg (g := g) t) (conv_gp hg) n hw
  have hN := hasDerivAt_momentLap (fun t => gn_nonneg (g := g) t) (conv_gn hg) n hw
  have hev : (fun w => momentLap (gp g) n w - momentLap (gn g) n w) =ᶠ[𝓝 w] momentLap g n := by
    have hmem : {w' : ℂ | σ₀ < w'.re} ∈ 𝓝 w :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
    filter_upwards [hmem] with w' hw'
    exact (momentLap_split hg n hw').symm
  have := (hP.sub hN).congr_of_eventuallyEq hev.symm
  rw [momentLap_split hg (n + 1) hw]
  have e : -(momentLap (gp g) (n + 1) w - momentLap (gn g) (n + 1) w)
      = -momentLap (gp g) (n + 1) w - -momentLap (gn g) (n + 1) w := by ring
  rw [e]; exact this

theorem iteratedDeriv_momentLap_signed (hg : SignedConv g σ₀) (n : ℕ) {w : ℂ} (hw : σ₀ < w.re) :
    iteratedDeriv n (momentLap g 0) w = (-1) ^ n * momentLap g n w := by
  induction n generalizing w with
  | zero => simp
  | succ k ih =>
    have hmem : {w' : ℂ | σ₀ < w'.re} ∈ 𝓝 w :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
    have hev : (fun w' : ℂ ↦ iteratedDeriv k (momentLap g 0) w')
        =ᶠ[𝓝 w] (fun w' : ℂ ↦ (-1) ^ k * momentLap g k w') := by
      filter_upwards [hmem] with w' hw'
      exact ih hw'
    have hdm := (hasDerivAt_momentLap_signed hg k hw).const_mul ((-1 : ℂ) ^ k)
    rw [iteratedDeriv_succ, hev.deriv_eq, hdm.deriv]
    ring

/-- The real moment integral. -/
noncomputable def realMom (h : ℝ → ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-σ * t) * h t

theorem momentLap_ofReal (h : ℝ → ℝ) (n : ℕ) (σ : ℝ) :
    momentLap h n (σ : ℂ) = (realMom h n σ : ℂ) := by
  unfold momentLap realMom
  refine Eq.trans (setIntegral_congr_fun
    (g := fun t : ℝ => ((t ^ n * Real.exp (-σ * t) * h t : ℝ) : ℂ)) measurableSet_Ioi
    (fun t _ => ?_)) integral_ofReal
  push_cast
  ring_nf

theorem norm_momentLap_le {h : ℝ → ℝ} (hpos : ∀ t, 0 ≤ h t) (n : ℕ) (z : ℂ) :
    ‖momentLap h n z‖ ≤ realMom h n z.re := by
  unfold momentLap realMom
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have htpos : (0:ℝ) < t := ht
  rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_exp]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, abs_of_nonneg (hpos t)]
  have hre : (-z * (t:ℂ)).re = -z.re * t := by simp [Complex.mul_re, Complex.neg_re]
  rw [hre]

/-- **Basic inequality** (signed): `‖M_n(z)‖ ≤ ‖M_n(Re z)‖ + 2 ∫ tⁿ e^{-σt} g⁻`. -/
theorem norm_momentLap_signed_le (hg : SignedConv g σ₀) (n : ℕ) {z : ℂ} (hz : σ₀ < z.re) :
    ‖momentLap g n z‖ ≤ ‖momentLap g n (z.re : ℂ)‖ + 2 * realMom (gn g) n z.re := by
  have hzr : σ₀ < (z.re : ℂ).re := by simpa using hz
  rw [momentLap_split hg n hz, momentLap_split hg n hzr, momentLap_ofReal, momentLap_ofReal]
  have h1 := norm_momentLap_le (fun t => gp_nonneg (g := g) t) n z
  have h2 := norm_momentLap_le (fun t => gn_nonneg (g := g) t) n z
  have h3 := norm_sub_le (momentLap (gp g) n z) (momentLap (gn g) n z)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h4 := le_abs_self (realMom (gp g) n z.re - realMom (gn g) n z.re)
  linarith

end Signed


section Tail


/-- `u^k e^{-a u} ≤ k!/a^k` (local copy in the `-a * u` normal form). -/
theorem kernel_le' (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) ≤ k.factorial / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := a * u) (mul_nonneg ha.le hu) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hak : 0 < a ^ k := pow_pos ha k
  rw [div_le_iff₀ hf] at h
  rw [le_div_iff₀ hak]
  have he := Real.exp_pos (-a * u)
  calc u ^ k * Real.exp (-a * u) * a ^ k = (a * u) ^ k * Real.exp (-a * u) := by ring
    _ ≤ (Real.exp (a * u) * k.factorial) * Real.exp (-a * u) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = k.factorial := by
        rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; simp

/-- Off the window `[U, (1+δ)U]` the shifted kernel is at most `k!/σ^k`. -/
theorem kernel_off_window {k : ℕ} {σ τ l U δ t : ℝ} (hl : 0 < l) (hτl : τ + l < σ) (hσ : 0 < σ)
    (hA : σ ^ k * Real.exp (l * U) ≤ (σ - τ + l) ^ k)
    (hB : σ ^ k ≤ (σ - τ - l) ^ k * Real.exp (l * ((1 + δ) * U)))
    (ht : 0 < t) (hnot : t ∉ Icc U ((1 + δ) * U)) :
    t ^ k * Real.exp (-(σ - τ) * t) ≤ k.factorial / σ ^ k := by
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hσk : 0 < σ ^ k := pow_pos hσ k
  rw [mem_Icc, not_and_or, not_le, not_le] at hnot
  rcases hnot with h | h
  · have hp : 0 < σ - τ + l := by linarith
    have hk := kernel_le' k hp ht.le
    have e : t ^ k * Real.exp (-(σ - τ) * t)
        = t ^ k * Real.exp (-(σ - τ + l) * t) * Real.exp (l * t) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    have hpk : 0 < (σ - τ + l) ^ k := pow_pos hp k
    calc t ^ k * Real.exp (-(σ - τ + l) * t) * Real.exp (l * t)
        ≤ k.factorial / (σ - τ + l) ^ k * Real.exp (l * U) := by
          gcongr
      _ ≤ k.factorial / σ ^ k := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpk hσk]
          calc (k.factorial : ℝ) * Real.exp (l * U) * σ ^ k
              = k.factorial * (σ ^ k * Real.exp (l * U)) := by ring
            _ ≤ k.factorial * (σ - τ + l) ^ k := by gcongr
  · have hp : 0 < σ - τ - l := by linarith
    have hk := kernel_le' k hp ht.le
    have e : t ^ k * Real.exp (-(σ - τ) * t)
        = t ^ k * Real.exp (-(σ - τ - l) * t) * Real.exp (-(l * t)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    have hpk : 0 < (σ - τ - l) ^ k := pow_pos hp k
    have hV : Real.exp (-(l * t)) ≤ Real.exp (-(l * ((1 + δ) * U))) := by
      rw [Real.exp_le_exp]; nlinarith
    calc t ^ k * Real.exp (-(σ - τ - l) * t) * Real.exp (-(l * t))
        ≤ k.factorial / (σ - τ - l) ^ k * Real.exp (-(l * ((1 + δ) * U))) := by
          gcongr
      _ ≤ k.factorial / σ ^ k := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpk hσk]
          have h1 : Real.exp (-(l * ((1 + δ) * U))) * Real.exp (l * ((1 + δ) * U)) = 1 := by
            rw [← Real.exp_add]; simp
          have h2 : 0 ≤ (k.factorial : ℝ) * Real.exp (-(l * ((1 + δ) * U))) := by positivity
          calc (k.factorial : ℝ) * Real.exp (-(l * ((1 + δ) * U))) * σ ^ k
              ≤ k.factorial * Real.exp (-(l * ((1 + δ) * U)))
                  * ((σ - τ - l) ^ k * Real.exp (l * ((1 + δ) * U))) :=
                mul_le_mul_of_nonneg_left hB h2
            _ = k.factorial * (σ - τ - l) ^ k * (Real.exp (-(l * ((1 + δ) * U)))
                  * Real.exp (l * ((1 + δ) * U))) := by ring
            _ = _ := by rw [h1, mul_one]

variable {g : ℝ → ℝ} {σ₀ : ℝ}

/-- **Window + tail bound** on the negative-part moment. -/
theorem realMom_gn_le (hg : SignedConv g σ₀) {k : ℕ} {σ τ l θ C U δ : ℝ}
    (hτ : σ₀ < τ) (hτ0 : 0 < τ) (hl : 0 < l) (hτl : τ + l < σ) (hθσ : θ < σ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hδ : 0 < δ)
    (hA : σ ^ k * Real.exp (l * U) ≤ (σ - τ + l) ^ k)
    (hB : σ ^ k ≤ (σ - τ - l) ^ k * Real.exp (l * ((1 + δ) * U)))
    (hW : ∀ u ∈ Icc U ((1 + δ) * U), -(C * Real.exp (θ * u)) ≤ g u) :
    realMom (gn g) k σ ≤ k.factorial * (C * (δ * U) / (σ - θ) ^ k
      + (∫ t in Ioi (0 : ℝ), Real.exp (-τ * t) * |g t|) / σ ^ k) := by
  have hσ : 0 < σ := by linarith
  have hσθ : 0 < σ - θ := by linarith
  set W := Icc U ((1 + δ) * U) with hWdef
  set c : ℝ := C / (σ - θ) ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  set F : ℝ → ℝ := fun t => (k.factorial : ℝ) * (W.indicator (fun _ => c) t
      + Real.exp (-τ * t) * |g t| / σ ^ k) with hF
  have hgabs : IntegrableOn (fun t => Real.exp (-τ * t) * |g t|) (Ioi 0) := by
    refine ((hg τ hτ).norm).congr ?_
    filter_upwards with t
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hind : Integrable (W.indicator (fun _ : ℝ => c)) := by
    refine (integrableOn_const ?_ ?_).integrable_indicator measurableSet_Icc
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  have hFi : IntegrableOn F (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    exact hind.integrableOn.add (hgabs.div_const _)
  have hLi : IntegrableOn (fun t => t ^ k * Real.exp (-σ * t) * gn g t) (Ioi 0) :=
    integrable_momentLap_real' (fun t => gn_nonneg (g := g) t) (conv_gn hg) k (by linarith)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), t ^ k * Real.exp (-σ * t) * gn g t ≤ F t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hf : (0 : ℝ) ≤ k.factorial := by positivity
    have h2 : 0 ≤ Real.exp (-τ * t) * |g t| / σ ^ k := by positivity
    have hkt : 0 ≤ t ^ k * Real.exp (-σ * t) := by positivity
    by_cases htW : t ∈ W
    · have hgn : gn g t ≤ C * Real.exp (θ * t) :=
        max_le (by linarith [hW t htW]) (by positivity)
      have hk := kernel_le' k hσθ ht0.le
      have e : t ^ k * Real.exp (-σ * t) * (C * Real.exp (θ * t))
          = C * (t ^ k * Real.exp (-(σ - θ) * t)) := by
        rw [show -(σ - θ) * t = -σ * t + θ * t by ring, Real.exp_add]; ring
      calc t ^ k * Real.exp (-σ * t) * gn g t
          ≤ t ^ k * Real.exp (-σ * t) * (C * Real.exp (θ * t)) :=
            mul_le_mul_of_nonneg_left hgn hkt
        _ = C * (t ^ k * Real.exp (-(σ - θ) * t)) := e
        _ ≤ C * (k.factorial / (σ - θ) ^ k) := mul_le_mul_of_nonneg_left hk hC
        _ = k.factorial * c := by rw [hc]; ring
        _ ≤ F t := by
          simp only [hF, Set.indicator_of_mem htW]
          nlinarith
    · have hk := kernel_off_window hl hτl hσ hA hB ht0 htW
      have e : t ^ k * Real.exp (-σ * t) * |g t|
          = (t ^ k * Real.exp (-(σ - τ) * t)) * (Real.exp (-τ * t) * |g t|) := by
        rw [show -σ * t = -(σ - τ) * t + -τ * t by ring, Real.exp_add]; ring
      have hE : 0 ≤ Real.exp (-τ * t) * |g t| := by positivity
      calc t ^ k * Real.exp (-σ * t) * gn g t
          ≤ t ^ k * Real.exp (-σ * t) * |g t| :=
            mul_le_mul_of_nonneg_left (gn_le_abs t) hkt
        _ = _ := e
        _ ≤ (k.factorial / σ ^ k) * (Real.exp (-τ * t) * |g t|) :=
            mul_le_mul_of_nonneg_right hk hE
        _ = F t := by
          simp only [hF, Set.indicator_of_notMem htW]
          ring
  have hmono := setIntegral_mono_on hLi hFi measurableSet_Ioi hpt
  have hint : ∫ t in Ioi (0 : ℝ), F t = k.factorial * ((∫ t in Ioi (0 : ℝ), W.indicator (fun _ => c) t)
      + (∫ t in Ioi (0 : ℝ), Real.exp (-τ * t) * |g t|) / σ ^ k) := by
    rw [hF, integral_const_mul, integral_add hind.integrableOn (hgabs.div_const _), integral_div]
  have hindle : ∫ t in Ioi (0 : ℝ), W.indicator (fun _ => c) t ≤ c * (δ * U) := by
    refine (setIntegral_le_integral hind (Eventually.of_forall
      (fun t => Set.indicator_nonneg (fun _ _ => hc0) t))).trans (le_of_eq ?_)
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul]
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by nlinarith)]
    ring
  unfold realMom
  calc _ ≤ ∫ t in Ioi (0 : ℝ), F t := hmono
    _ = _ := hint
    _ ≤ k.factorial * (c * (δ * U)
        + (∫ t in Ioi (0 : ℝ), Real.exp (-τ * t) * |g t|) / σ ^ k) := by gcongr
    _ = _ := by rw [hc]; ring

end Tail

section Geometry

variable {Z : Set ℂ}

/-- Points of `Z` are isolated in the right half-plane. -/
def IsoRight (Z : Set ℂ) : Prop := ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z

theorem re_pos_of_mem_closedBall {c w : ℂ} {R : ℝ} (hR : R < c.re) (hw : w ∈ Metric.closedBall c R) :
    0 < w.re := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  have h := Complex.abs_re_le_norm (w - c)
  rw [Complex.sub_re] at h
  have := (abs_le.mp (h.trans hw)).1
  linarith

/-- Finitely many points of `Z` in a closed disc inside the right half-plane. -/
theorem finite_inter_closedBall (hiso : IsoRight Z) {c : ℂ} {R : ℝ} (hR : R < c.re) :
    (Z ∩ Metric.closedBall c R).Finite := by
  by_contra hinf
  obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall c R) inter_subset_right
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have h := hiso x (re_pos_of_mem_closedBall hR hxK)
  exact (hacc.and_eventually h).exists.elim (fun y hy => hy.2 hy.1.1)

/-- Without real points in `Z`: a pole-free disc about `σ` and a pole whose horizontal distance
to the line `Re = σ` is less than the disc radius. -/
theorem disc_and_pole (hiso : IsoRight Z) (hnr : ∀ ρ ∈ Z, ρ.im ≠ 0) {σ θ : ℝ} (hθ : 0 < θ)
    {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    ∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D := by
  have hfin := finite_inter_closedBall hiso (c := (σ : ℂ)) (R := σ - θ) (by simp; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨σ - θ, le_rfl, fun w hw hb => ?_, ρ₀, h₀, by linarith⟩
    have : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩
    rw [hF] at this; exact this
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    refine ⟨dist ρs (σ : ℂ), Metric.mem_closedBall.mp hρsF.2, fun w hw hb => ?_, ρs, hρsF.1, ?_⟩
    · rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr
        (hb.le.trans (Metric.mem_closedBall.mp hρsF.2))⟩
      have := hmin w hwF
      linarith
    · rw [Complex.dist_eq_re_im]
      have him := hnr ρs hρsF.1
      have hpos : 0 < ρs.im ^ 2 := by positivity
      simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      calc σ - ρs.re ≤ |ρs.re - σ| := by rw [abs_sub_comm]; exact le_abs_self _
        _ = √((ρs.re - σ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ < √((ρs.re - σ) ^ 2 + ρs.im ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

/-- Two distinct points left of `Re = σ` are equidistant from at most one point of that line. -/
theorem equidistant_subsingleton {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ) (hab : a ≠ b) :
    {γ : ℝ | ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖}.Subsingleton := by
  have key : ∀ γ : ℝ, ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖ →
      (σ - a.re) ^ 2 + (γ - a.im) ^ 2 = (σ - b.re) ^ 2 + (γ - b.im) ^ 2 := by
    intro γ h
    have h2 := congrArg (· ^ 2) h
    simp only [Complex.sq_norm, Complex.normSq_apply] at h2
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
    nlinarith [h2]
  intro γ₁ h₁ γ₂ h₂
  have e1 := key γ₁ h₁
  have e2 := key γ₂ h₂
  by_contra hne
  have hsub : (γ₁ - γ₂) * (2 * (b.im - a.im)) = 0 := by nlinarith [e1, e2]
  have himeq : a.im = b.im := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  rw [himeq] at e1
  have hre : (σ - a.re) ^ 2 = (σ - b.re) ^ 2 := by linarith
  have hre' : a.re = b.re := by nlinarith [hre]
  exact hab (Complex.ext hre' himeq)

/-- A point `σ + iγ` whose nearest point of `Z` is unique and closer than `D`. -/
theorem nearest_unique (hiso : IsoRight Z) {σ D : ℝ} (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ)
    {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
  set ε : ℝ := min (D - (σ - ρ₁.re)) (σ - D) / 2 with hε
  have hε0 : 0 < ε := by
    have := lt_min (show 0 < D - (σ - ρ₁.re) by linarith) (show 0 < σ - D by linarith)
    rw [hε]; linarith
  have hε1 : ε ≤ (D - (σ - ρ₁.re)) / 2 := by
    rw [hε]; linarith [min_le_left (D - (σ - ρ₁.re)) (σ - D)]
  have hε2 : ε ≤ (σ - D) / 2 := by
    rw [hε]; linarith [min_le_right (D - (σ - ρ₁.re)) (σ - D)]
  set c₀ : ℂ := (σ : ℂ) + ρ₁.im * I with hc₀
  have hc₀re : c₀.re = σ := by simp [hc₀]
  have hF : (Z ∩ Metric.closedBall c₀ (D + ε)).Finite :=
    finite_inter_closedBall hiso (by rw [hc₀re]; linarith)
  set F := Z ∩ Metric.closedBall c₀ (D + ε) with hFdef
  set B : Set ℝ := ⋃ p ∈ (F ×ˢ F) ∩ {p : ℂ × ℂ | p.1 ≠ p.2},
    {γ : ℝ | ‖(σ : ℂ) + γ * I - p.1‖ = ‖(σ : ℂ) + γ * I - p.2‖} with hB
  have hBfin : B.Finite := by
    refine Set.Finite.biUnion ((hF.prod hF).subset inter_subset_left) (fun p hp => ?_)
    exact (equidistant_subsingleton (hle _ hp.1.1.1) (hle _ hp.1.2.1) hp.2).finite
  obtain ⟨γ, hγI, hγB⟩ :=
    ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).sdiff hBfin).nonempty
  set c : ℂ := (σ : ℂ) + γ * I with hc
  have hcc₀ : ‖c - c₀‖ < ε := by
    have e : c - c₀ = ((γ - ρ₁.im : ℝ) : ℂ) * I := by rw [hc, hc₀]; push_cast; ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_sub_lt_iff.mpr ⟨by linarith [hγI.2], by linarith [hγI.1]⟩
  have hc₀ρ₁ : ‖c₀ - ρ₁‖ = σ - ρ₁.re := by
    have e : c₀ - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hc₀]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hle ρ₁ h₁))]
  have hρ₁F : ρ₁ ∈ F := ⟨h₁, by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, hc₀ρ₁]; linarith⟩
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩
  have hρ₁c : ‖c - ρ₁‖ < D := by
    have := norm_sub_le_norm_sub_add_norm_sub c c₀ ρ₁
    rw [hc₀ρ₁] at this; linarith
  have hm : ‖c - ρ‖ ≤ ‖c - ρ₁‖ := hmin ρ₁ hρ₁F
  have hT : ∀ w ∈ F \ {ρ}, ‖c - ρ‖ < ‖c - w‖ := by
    intro w hw
    rcases lt_or_eq_of_le (hmin w hw.1) with h | h
    · exact h
    · exfalso
      apply hγB
      refine Set.mem_biUnion (x := (w, ρ)) ⟨⟨hw.1, hρF⟩, hw.2⟩ ?_
      show ‖c - w‖ = ‖c - ρ‖
      exact h.symm
  obtain ⟨r, hr, hrT⟩ : ∃ r, ‖c - ρ‖ < r ∧ ∀ t ∈ F \ {ρ}, r ≤ ‖c - t‖ := by
    rcases (F \ {ρ}).eq_empty_or_nonempty with hTe | hTne
    · exact ⟨‖c - ρ‖ + 1, by linarith, fun t ht => by rw [hTe] at ht; exact absurd ht (by simp)⟩
    · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {ρ}) (fun w => ‖c - w‖)
        (hF.subset sdiff_subset) hTne
      exact ⟨‖c - t₀‖, hT t₀ ht₀, htmin⟩
  refine ⟨γ, ρ, hρF.1, min r D, lt_min hr (by linarith), min_le_right _ _, fun w hw hb => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hb
  have hwF : w ∈ F := by
    refine ⟨hw, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub w c c₀
    rw [norm_sub_rev w c] at this
    linarith [min_le_right r D]
  by_contra hne
  have h3 := hrT w ⟨hwF, hne⟩
  linarith [min_le_left r D]

end Geometry

section Taylor

/-- Cauchy estimate: `‖G^{(k)}(z)‖ ≤ k! M / r'^k` for `G` holomorphic on `ball z r`, `r' < r`. -/
theorem cauchy_bound {G : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ G (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖iteratedDeriv k G z‖ ≤ k.factorial * M / r' ^ k := by
  have hsub : Metric.closedBall z r' ⊆ Metric.ball z r := Metric.closedBall_subset_ball h1
  have hcl : DiffContOnCl ℂ G (Metric.ball z r') := hd.diffContOnCl_ball hsub
  obtain ⟨C, hC⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn
    (hd.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub))
  refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k h0 hcl
    (fun w hw => (hC w hw).trans (le_max_left _ _))

theorem iteratedDeriv_simple_pole (c ρ z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z
      = c * ((-1) ^ k * (k.factorial : ℂ) * (z - ρ) ^ (-1 - (k : ℤ))) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate]
  have e : (fun s : ℂ => (s - ρ)⁻¹) = fun s : ℂ => (1 * s - ρ)⁻¹ := by
    funext s; rw [one_mul]
  rw [e, iter_deriv_inv_linear_sub]
  simp

/-- **Simple-pole lower bound** for Taylor coefficients at `z`: if the only singularity of `Φ` in
`ball z r` is a simple pole at `ρ` with residue `c`, then
`‖Φ^{(k)}(z)‖ ≥ k! ‖c‖ / ‖z-ρ‖^{k+1} - k! M / r'^k`. -/
theorem pole_lower_bound {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ} (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ,
      k.factorial * ‖c‖ / ‖z - ρ‖ ^ (k + 1) - k.factorial * M / r' ^ k ≤ ‖iteratedDeriv k Φ z‖ := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  set G : ℂ → ℂ := Function.update (fun s => Φ s - c / (s - ρ)) ρ (hfun ρ) with hG
  have hGeq : G =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ, hG, Function.update_self]
    · rw [hG, Function.update_of_ne hsρ, hs (Set.mem_compl_singleton_iff.mpr hsρ)]
      ring
  have hGd : DifferentiableOn ℂ G (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      exact ((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        rw [hG, Function.update_of_ne ht.2]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact ((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt
  obtain ⟨M, hM0, hM⟩ := cauchy_bound hGd h0 h1
  refine ⟨M, hM0, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hmemz : z ∈ Metric.ball z r \ {ρ} := ⟨Metric.mem_ball_self hr, hzρ⟩
  have hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmemz] with t ht
    simp only [Pi.add_apply, hG, Function.update_of_ne ht.2, div_eq_mul_inv]
    ring
  have hGc : ContDiffAt ℂ k G z :=
    (hGd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hzρ))
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, iteratedDeriv_simple_pole]
  have hd0 : 0 < ‖z - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzρ)
  have hpole : ‖c * ((-1) ^ k * (k.factorial : ℂ) * (z - ρ) ^ (-1 - (k : ℤ)))‖
      = k.factorial * ‖c‖ / ‖z - ρ‖ ^ (k + 1) := by
    rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv,
      norm_pow, Complex.norm_natCast]
    field_simp
  have htri := norm_sub_norm_le (c * ((-1) ^ k * (k.factorial : ℂ) * (z - ρ) ^ (-1 - (k : ℤ))))
    (-(iteratedDeriv k G z))
  rw [norm_neg, sub_neg_eq_add, add_comm] at htri
  rw [hpole] at htri
  have := hM k
  linarith

end Taylor

section Main

/-- Exponential beats affine: for `q > 1`, eventually `P + Q k < q^k`. -/
theorem eventually_affine_lt_pow {q : ℝ} (hq : 1 < q) (P Q : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → P + Q * k < q ^ k := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ 1 / q ^ k) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 hq
  have h2 : Tendsto (fun k : ℕ => (q ^ k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hq)
  have h3 : Tendsto (fun k : ℕ => P * (q ^ k)⁻¹ + Q * ((k : ℝ) ^ 1 / q ^ k)) atTop (𝓝 0) := by
    simpa using (h2.const_mul P).add (h1.const_mul Q)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h3.eventually (gt_mem_nhds one_pos))
  refine ⟨K, fun k hk => ?_⟩
  have := hK k hk
  have hqk : 0 < q ^ k := pow_pos (by linarith) k
  have e : P * (q ^ k)⁻¹ + Q * ((k : ℝ) ^ 1 / q ^ k) = (P + Q * k) / q ^ k := by
    field_simp
  rw [e, div_lt_one hqk] at this
  exact this

variable {g : ℝ → ℝ} {σ₀ : ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}

/-- Taylor coefficients of a function agreeing with the Laplace transform of `g` on `Re > σ₀`. -/
theorem norm_iteratedDeriv_eq (hg : SignedConv g σ₀) (hΦ : ∀ z : ℂ, σ₀ < z.re → Φ z = momentLap g 0 z)
    (k : ℕ) {w : ℂ} (hw : σ₀ < w.re) :
    ‖iteratedDeriv k Φ w‖ = ‖momentLap g k w‖ := by
  have hmem : {w' : ℂ | σ₀ < w'.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hev : Φ =ᶠ[𝓝 w] momentLap g 0 := by
    filter_upwards [hmem] with w' hw'
    exact hΦ w' hw'
  rw [hev.iteratedDeriv_eq, iteratedDeriv_momentLap_signed hg k hw, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul]

/-- **Windowed Landau theorem** (abstract form; architecture after L. Alpöge's
`Deduction.landau_window` / `zeroFree_of_rpow_window`, re-proved here for a signed `g` with a
lower window bound and pole set `Z` with no real points).

`g` has absolutely convergent Laplace transform on `Re > σ₀`, continued by `Φ` to `Re > 0` minus
`Z` (isolated, all simple poles, none real, all with `Re ≤ σ₀`). If `g ≥ -C e^{θu}` on windows
`[U, (1+δ)U]` for arbitrarily large `U`, then every point of `Z` has real part `≤ θ`. -/
theorem window_landau (hσ₀ : 0 ≤ σ₀) (hg : SignedConv g σ₀)
    (hΦ : ∀ z : ℂ, σ₀ < z.re → Φ z = momentLap g 0 z)
    (hZre : ∀ ρ ∈ Z, ρ.re ≤ σ₀)
    (hdiff : DifferentiableOn ℂ Φ ({z : ℂ | 0 < z.re} \ Z))
    (hiso : IsoRight Z) (hnr : ∀ ρ ∈ Z, ρ.im ≠ 0)
    (hpole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    {θ δ C : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hW : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1 + δ) * U), -(C * Real.exp (θ * u)) ≤ g u) :
    ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ₀ h₀
  by_contra hρ₀
  rw [not_le] at hρ₀
  set τ : ℝ := σ₀ + 1 with hτdef
  have hτ0 : 0 < τ := by linarith
  obtain ⟨σ, l, hσ₁, hlτ, hτlσ, htail⟩ := tail_params hδ hτ0 (σ₀ + θ + 1)
  have hl0 : 0 < l := by linarith
  have hσσ₀ : σ₀ < σ := by linarith
  have hθσ : θ < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hle : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (hZre ρ hρ).trans_lt hσσ₀
  obtain ⟨D, hDle, hfree, ρ₁, h₁, hρ₁⟩ := disc_and_pole hiso hnr hθ h₀ hρ₀ (σ := σ)
  have hDσ : D < σ := by linarith
  obtain ⟨γ, ρ, hρZ, r, hρr, hrD, huniq⟩ := nearest_unique hiso hle hDσ h₁ hρ₁
  set z : ℂ := (σ : ℂ) + γ * I with hz
  have hzre : z.re = σ := by simp [hz]
  have hne : ρ ≠ z := by
    intro h; have := hle ρ hρZ; rw [h, hzre] at this; exact lt_irrefl _ this
  set d : ℝ := ‖z - ρ‖ with hd
  have hd0 : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hdr : d < r := hρr
  -- the disc `ball z r` lies in `Re > 0`
  have hre_ball : ∀ {c : ℂ} {R : ℝ}, R ≤ c.re - θ → ∀ w ∈ Metric.ball c R, 0 < w.re := by
    intro c R hR w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re] at h
    have := (abs_lt.mp (h.trans_lt hw)).1
    linarith
  -- simple-pole lower bound at `z`
  obtain ⟨c, hc0, hp⟩ := hpole ρ hρZ
  have hdz : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}) := by
    refine hdiff.mono ?_
    rintro w ⟨hw, hw'⟩
    exact ⟨hre_ball (by rw [hzre]; linarith) w hw, fun hZ => hw' (huniq w hZ hw)⟩
  set r' : ℝ := (d + r) / 2 with hr'
  obtain ⟨M₁, hM₁0, hM₁⟩ := pole_lower_bound (r' := r') hne hdz hp (by linarith) (by linarith)
  -- Cauchy bound at the real point `σ`
  have hdσ : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D) := by
    refine hdiff.mono ?_
    intro w hw
    exact ⟨hre_ball (by simp; linarith) w hw, fun hZ => hfree w hZ hw⟩
  set e₂ : ℝ := (d + D) / 2 with he₂
  obtain ⟨M₂, hM₂0, hM₂⟩ := cauchy_bound hdσ (by linarith) (by linarith : e₂ < D)
  -- growth comparison
  set e : ℝ := min r' e₂ with he
  have he0 : 0 < e := lt_min (by linarith) (by linarith)
  have hde : d < e := lt_min (by linarith) (by linarith)
  have heσθ : e ≤ σ - θ := (min_le_right _ _).trans (by linarith)
  set I : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-τ * t) * |g t| with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun t _ => by positivity)
  set q : ℝ := e / d with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hd0]; exact hde
  obtain ⟨K, hK⟩ := eventually_affine_lt_pow hq1 (d * (M₁ + M₂ + 2 * I) / ‖c‖)
    (d * (2 * |C| * δ) / ‖c‖)
  obtain ⟨U, hU, hWU⟩ := hW (max K 1)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  obtain ⟨k, hUk, hA, hB⟩ := htail U hU1
  have hKk : K ≤ k := by
    have : (K : ℝ) ≤ k := ((le_max_left _ _).trans hU).trans hUk
    exact_mod_cast this
  have hcont := hK k hKk
  -- the chain of inequalities
  have hWabs : ∀ u ∈ Icc U ((1 + δ) * U), -(|C| * Real.exp (θ * u)) ≤ g u := by
    intro u hu
    have := hWU u hu
    have : C * Real.exp (θ * u) ≤ |C| * Real.exp (θ * u) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    linarith
  have hmom := realMom_gn_le hg (by linarith : σ₀ < τ) hτ0 hl0 hτlσ hθσ (abs_nonneg C)
    (by linarith) hδ hA hB hWabs
  have hbasic := norm_momentLap_signed_le hg k (z := z) (by rw [hzre]; exact hσσ₀)
  rw [hzre] at hbasic
  have hz' := norm_iteratedDeriv_eq hg hΦ k (w := z) (by rw [hzre]; exact hσσ₀)
  have hσ' := norm_iteratedDeriv_eq hg hΦ k (w := (σ : ℂ)) (by simpa using hσσ₀)
  have hlow := hM₁ k
  have hup := hM₂ k
  rw [hz'] at hlow
  rw [hσ'] at hup
  -- divide by `k!` and compare with `e^k`
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hek : 0 < e ^ k := pow_pos he0 k
  have hdk : 0 < d ^ k := pow_pos hd0 k
  have hr'k : e ^ k ≤ r' ^ k := pow_le_pow_left₀ he0.le (min_le_left _ _) k
  have he₂k : e ^ k ≤ e₂ ^ k := pow_le_pow_left₀ he0.le (min_le_right _ _) k
  have hσθk : e ^ k ≤ (σ - θ) ^ k := pow_le_pow_left₀ he0.le heσθ k
  have hσk : e ^ k ≤ σ ^ k := pow_le_pow_left₀ he0.le (by linarith) k
  have key : ‖c‖ / d ^ (k + 1) ≤ (M₁ + M₂ + 2 * I + 2 * |C| * δ * k) / e ^ k := by
    have h1 : k.factorial * ‖c‖ / d ^ (k + 1)
        ≤ k.factorial * M₁ / r' ^ k + k.factorial * M₂ / e₂ ^ k
          + 2 * (k.factorial * (|C| * (δ * U) / (σ - θ) ^ k + I / σ ^ k)) := by
      linarith
    have h2 : ‖c‖ / d ^ (k + 1)
        ≤ M₁ / r' ^ k + M₂ / e₂ ^ k + 2 * (|C| * (δ * U) / (σ - θ) ^ k + I / σ ^ k) := by
      have e1 : k.factorial * ‖c‖ / d ^ (k + 1) = k.factorial * (‖c‖ / d ^ (k + 1)) := by ring
      have e2 : k.factorial * M₁ / r' ^ k + k.factorial * M₂ / e₂ ^ k
          + 2 * (k.factorial * (|C| * (δ * U) / (σ - θ) ^ k + I / σ ^ k))
          = k.factorial * (M₁ / r' ^ k + M₂ / e₂ ^ k
            + 2 * (|C| * (δ * U) / (σ - θ) ^ k + I / σ ^ k)) := by ring
      rw [e1, e2] at h1
      exact le_of_mul_le_mul_left h1 hf
    have b1 : M₁ / r' ^ k ≤ M₁ / e ^ k := div_le_div_of_nonneg_left hM₁0 hek hr'k
    have b2 : M₂ / e₂ ^ k ≤ M₂ / e ^ k := div_le_div_of_nonneg_left hM₂0 hek he₂k
    have b3 : |C| * (δ * U) / (σ - θ) ^ k ≤ |C| * (δ * k) / e ^ k := by
      apply div_le_div₀ (by positivity) _ hek hσθk
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUk hδ.le) (abs_nonneg C)
    have b4 : I / σ ^ k ≤ I / e ^ k := div_le_div_of_nonneg_left hI0 hek hσk
    calc ‖c‖ / d ^ (k + 1) ≤ _ := h2
      _ ≤ M₁ / e ^ k + M₂ / e ^ k + 2 * (|C| * (δ * k) / e ^ k + I / e ^ k) := by linarith
      _ = _ := by ring
  -- contradiction with exponential growth of `q^k`
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hqk : q ^ k = e ^ k / d ^ k := by rw [hq, div_pow]
  have : q ^ k ≤ d * (M₁ + M₂ + 2 * I) / ‖c‖ + d * (2 * |C| * δ) / ‖c‖ * k := by
    rw [hqk, div_le_iff₀ hdk]
    rw [div_le_div_iff₀ (pow_pos hd0 _) hek] at key
    have e3 : (d * (M₁ + M₂ + 2 * I) / ‖c‖ + d * (2 * |C| * δ) / ‖c‖ * k) * d ^ k
        = d ^ (k + 1) * (M₁ + M₂ + 2 * I + 2 * |C| * δ * k) / ‖c‖ := by
      rw [pow_succ]; field_simp
    rw [e3, le_div_iff₀ hcn]
    calc e ^ k * ‖c‖ = ‖c‖ * e ^ k := by ring
      _ ≤ _ := key
      _ = _ := by ring
  linarith

end Main


/-! ### Instantiation at Round 23's `D` (F13W) -/

section Instance

open GppHeartReduction (xiE differentiable_xiE xiE_eq xiE_one xiE_real_ne_zero integrableOn_D)
open GppHeartLaplace (Dfun)

/-- `ξ_E(s) ≠ 0` for `Re s > 1`. -/
theorem xiE_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : xiE s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [xiE_eq hs0 hs1]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h; apply hz; rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp [hs0, this, hΛ]

/-- The continuation of the Laplace transform of `D`: `Φ(z) = (ξ_E′/ξ_E)(½+z)/z²`. -/
noncomputable def PhiD (z : ℂ) : ℂ := deriv xiE (1 / 2 + z) / xiE (1 / 2 + z) / z ^ 2

/-- Pole set: `z` with `Re z > 0` and `ξ_E(½+z) = 0`. -/
def ZD : Set ℂ := {z : ℂ | 0 < z.re ∧ xiE (1 / 2 + z) = 0}

theorem signedConv_D : SignedConv Dfun (1 / 2) := fun _ hτ => integrableOn_D hτ

theorem differentiable_shift : Differentiable ℂ (fun z : ℂ => xiE (1 / 2 + z)) := fun z =>
  (differentiable_xiE (1 / 2 + z)).comp z (differentiableAt_const _ |>.add differentiableAt_id)

theorem differentiable_deriv_shift : Differentiable ℂ (fun z : ℂ => deriv xiE (1 / 2 + z)) := fun z =>
  ((differentiable_xiE.analyticAt (1 / 2 + z)).deriv.differentiableAt).comp z
    (differentiableAt_const _ |>.add differentiableAt_id)

theorem PhiD_differentiableAt {z : ℂ} (hx : xiE (1 / 2 + z) ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ PhiD z := by
  unfold PhiD
  exact ((differentiable_deriv_shift z).div (differentiable_shift z) hx).div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 hz)

/-- `ξ_E(½ + ·)` is not locally zero anywhere. -/
theorem shift_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, xiE (1 / 2 + w) = 0 := by
  intro hev
  have hFa : AnalyticOnNhd ℂ (fun w : ℂ => xiE (1 / 2 + w)) Set.univ :=
    fun w _ => differentiable_shift.analyticAt w
  have h0 := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hev (Set.mem_univ (1 / 2 : ℂ))
  have : xiE (1 / 2 + 1 / 2) = 0 := h0
  norm_num [xiE_one] at this

theorem isoRight_ZD : IsoRight ZD := by
  intro z _
  rcases (differentiable_shift.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h (shift_not_eventually_zero z)
  · filter_upwards [h] with w hw hZ
    exact hw hZ.2

theorem ZD_re_le {ρ : ℂ} (hρ : ρ ∈ ZD) : ρ.re ≤ 1 / 2 := by
  by_contra h
  apply xiE_ne_zero_of_one_lt_re (s := 1 / 2 + ρ) (by simp; linarith) hρ.2

theorem ZD_im_ne {ρ : ℂ} (hρ : ρ ∈ ZD) : ρ.im ≠ 0 := by
  intro him
  have hρr : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h := xiE_real_ne_zero (x := 1 / 2 + ρ.re) (by linarith [hρ.1])
  apply h
  have := hρ.2
  rw [hρr] at this
  push_cast
  exact this

theorem PhiD_differentiableOn : DifferentiableOn ℂ PhiD ({z : ℂ | 0 < z.re} \ ZD) := by
  rintro z ⟨hz, hzZ⟩
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hx : xiE (1 / 2 + z) ≠ 0 := fun h => hzZ ⟨hz, h⟩
  exact (PhiD_differentiableAt hx hz0).differentiableWithinAt

/-- **Complex form of F11** on `Re z > ½`: `Φ = L[D]`. -/
theorem PhiD_eq_momentLap {z : ℂ} (hz : 1 / 2 < z.re) : PhiD z = momentLap Dfun 0 z := by
  set H : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hH
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHpre : IsPreconnected H := (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
  have hxH : ∀ w ∈ H, xiE (1 / 2 + w) ≠ 0 := fun w hw =>
    xiE_ne_zero_of_one_lt_re (by simp; have : (1:ℝ)/2 < w.re := hw; linarith)
  have hw0 : ∀ w ∈ H, w ≠ 0 := by
    intro w hw h; have : (1:ℝ)/2 < w.re := hw; rw [h] at this; simp at this; linarith
  set f : ℂ → ℂ := fun w => PhiD w - momentLap Dfun 0 w with hf
  have hfd : DifferentiableOn ℂ f H := by
    intro w hw
    exact ((PhiD_differentiableAt (hxH w hw) (hw0 w hw)).sub
      (hasDerivAt_momentLap_signed signedConv_D 0 hw).differentiableAt).differentiableWithinAt
  have hfa : AnalyticOnNhd ℂ f H := hfd.analyticOnNhd hHopen
  have hzero : ∀ σ : ℝ, 1 / 2 < σ → f (σ : ℂ) = 0 := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith
    have hF11 := GppHeartLaplace.F11_laplace_identity hσ
    have hxi : logDeriv GppHeartLaplace.xiC (((1 / 2 + σ : ℝ)) : ℂ)
        = logDeriv xiE (((1 / 2 + σ : ℝ)) : ℂ) := by
      have hev : GppHeartLaplace.xiC =ᶠ[𝓝 (((1 / 2 + σ : ℝ)) : ℂ)] xiE := by
        have h0 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 0 := isOpen_ne.mem_nhds (by
          push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
        have h1 : ∀ᶠ s : ℂ in 𝓝 (((1 / 2 + σ : ℝ)) : ℂ), s ≠ 1 := isOpen_ne.mem_nhds (by
          push_cast; intro h; have := congrArg Complex.re h; simp at this; linarith)
        filter_upwards [h0, h1] with s hs0 hs1
        exact (xiE_eq hs0 hs1).symm
      exact (logDeriv_congr_nhds hev).eq_of_nhds
    have hmom : momentLap Dfun 0 (σ : ℂ)
        = (((∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) * Dfun L : ℝ)) : ℂ) := by
      rw [momentLap_ofReal]
      unfold realMom
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      simp
    simp only [hf]
    rw [hmom, hF11, hxi, logDeriv_apply]
    unfold PhiD
    push_cast
    ring
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = 0 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[≠] (1 : ℝ), f (r : ℂ) = 0 := by
      have : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 1 / 2 < r := lt_mem_nhds (by norm_num)
      exact eventually_nhdsWithin_of_eventually_nhds (this.mono fun r hr => hzero r hr)
    have h2 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    exact h2.frequently h1.frequently
  have h1H : (1 : ℂ) ∈ H := by show (1:ℝ)/2 < (1 : ℂ).re; simp; norm_num
  have hEq := hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero hHpre h1H hfreq
  have := hEq hz
  simp only [hf, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

/-- Every point of `ZD` is a simple pole of `PhiD` (residue `m/ρ²`, `m` the multiplicity). -/
theorem PhiD_pole {ρ : ℂ} (hρ : ρ ∈ ZD) : ∃ c : ℂ, c ≠ 0 ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
    ∀ᶠ s in 𝓝[≠] ρ, PhiD s = c / (s - ρ) + h s := by
  set f : ℂ → ℂ := fun w => xiE (1 / 2 + w) with hfdef
  have hfa : AnalyticAt ℂ f ρ := differentiable_shift.analyticAt ρ
  have hρ0 : ρ ≠ 0 := by intro h; have := hρ.1; rw [h] at this; simp at this
  have hne_top : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    exact shift_not_eventually_zero ρ (analyticOrderAt_eq_top.mp htop)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  obtain ⟨G, hGa, hGρ, hev⟩ := hfa.analyticOrderAt_eq_natCast.mp hn.symm
  have hn1 : n ≠ 0 := by
    intro h0
    rw [h0] at hev
    have := hev.self_of_nhds
    simp only [pow_zero, one_smul] at this
    exact hGρ (this ▸ hρ.2)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨((m + 1 : ℕ) : ℂ) / ρ ^ 2, div_ne_zero (by exact_mod_cast Nat.succ_ne_zero m)
      (pow_ne_zero 2 hρ0),
    fun w => deriv G w / G w / w ^ 2 - ((m + 1 : ℕ) : ℂ) * (w + ρ) / (w ^ 2 * ρ ^ 2), ?_, ?_⟩
  · have hGd : AnalyticAt ℂ (deriv G) ρ := hGa.deriv
    have h1 : AnalyticAt ℂ (fun w => deriv G w / G w / w ^ 2) ρ :=
      (hGd.div hGa hGρ).div (analyticAt_id.pow 2) (pow_ne_zero 2 hρ0)
    have h2 : AnalyticAt ℂ (fun w : ℂ => ((m + 1 : ℕ) : ℂ) * (w + ρ) / (w ^ 2 * ρ ^ 2)) ρ :=
      (analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div
        ((analyticAt_id.pow 2).mul analyticAt_const) (mul_ne_zero (pow_ne_zero 2 hρ0) (pow_ne_zero 2 hρ0))
    exact h1.sub h2
  · -- local computation
    have hevE : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ (m + 1) • G z := hev
    have hev2 := hevE.eventuallyEq_nhds
    have hGev := hGa.eventually_analyticAt
    have hGne : ∀ᶠ w in 𝓝 ρ, G w ≠ 0 := hGa.continuousAt.eventually_ne hGρ
    have hw0 : ∀ᶠ w in 𝓝 ρ, w ≠ 0 := isOpen_ne.mem_nhds hρ0
    have hall := hev2.and (hGev.and (hGne.and hw0))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hall, self_mem_nhdsWithin]
      with w ⟨hfw, hGw, hGw0, hw0'⟩ hwρ
    have hwρ' : w - ρ ≠ 0 := sub_ne_zero.mpr hwρ
    have hfval : f w = (w - ρ) ^ (m + 1) * G w := by
      have := hfw.self_of_nhds
      simpa [smul_eq_mul] using this
    have hFd : HasDerivAt (fun x => (x - ρ) ^ (m + 1) * G x)
        (((m + 1 : ℕ) : ℂ) * (w - ρ) ^ m * G w + (w - ρ) ^ (m + 1) * deriv G w) w := by
      have h1 : HasDerivAt (fun x => (x - ρ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (w - ρ) ^ m) w := by
        have := (hasDerivAt_pow (m + 1) (w - ρ)).comp w ((hasDerivAt_id w).sub_const ρ)
        simpa [Function.comp_def] using this
      exact h1.mul hGw.differentiableAt.hasDerivAt
    have hdf : deriv f w = ((m + 1 : ℕ) : ℂ) * (w - ρ) ^ m * G w + (w - ρ) ^ (m + 1) * deriv G w := by
      rw [hfw.deriv_eq]
      have e : (fun z => (z - ρ) ^ (m + 1) • G z) = fun x => (x - ρ) ^ (m + 1) * G x := by
        funext x; rw [smul_eq_mul]
      rw [e]; exact hFd.deriv
    have hdx : deriv xiE (1 / 2 + w) = deriv f w := by
      rw [hfdef]; exact (deriv_comp_const_add (f := xiE) (a := 1 / 2) (x := w)).symm
    have hxw : xiE (1 / 2 + w) = f w := rfl
    unfold PhiD
    rw [hdx, hxw, hdf, hfval]
    field_simp
    ring

/-- **F13W (windowed Landau reduction).** For `ε ≥ 0`, `δ > 0` and any `C`: if for arbitrarily
large `L` the one-sided bound `D(L') ≥ −C e^{εL'}` holds on the whole window `L' ∈ [L, (1+δ)L]`,
then `ξ_E(s) ≠ 0` for every `Re s > ½ + ε`.

The hypothesis is implied by F13's global bound; windows in log scale `[L, (1+δ)L]` are
`[Y, Y^{1+δ}]` in `Y = e^L` (δ = ½ is Alpöge's `[Y, Y^{3/2}]`). 
-/
theorem F13W_xiE_ne_zero {ε δ C : ℝ} (hε0 : 0 ≤ ε) (hδ : 0 < δ)
    (hW : ∀ L₀ : ℝ, ∃ L : ℝ, L₀ ≤ L ∧
      ∀ L' ∈ Icc L ((1 + δ) * L), -C * Real.exp (ε * L') ≤ Dfun L') :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 := by
  intro s hs hzero
  set θ : ℝ := ε + (s.re - 1 / 2 - ε) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hεθ : ε ≤ θ := by rw [hθ]; linarith
  have hW' : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∀ u ∈ Icc U ((1 + δ) * U), -(|C| * Real.exp (θ * u)) ≤ Dfun u := by
    intro U₀
    obtain ⟨L, hL, hb⟩ := hW (max U₀ 0)
    refine ⟨L, (le_max_left _ _).trans hL, fun u hu => ?_⟩
    have hu0 : 0 ≤ u := ((le_max_right _ _).trans hL).trans hu.1
    have h1 := hb u hu
    have h2 : C * Real.exp (ε * u) ≤ |C| * Real.exp (θ * u) :=
      mul_le_mul (le_abs_self C) (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
        (abs_nonneg C)
    linarith
  have hρ : s - 1 / 2 ∈ ZD := ⟨by simp; linarith, by rw [add_sub_cancel]; exact hzero⟩
  have := window_landau (by norm_num) signedConv_D (fun z hz => PhiD_eq_momentLap hz)
    (fun ρ hρ => ZD_re_le hρ) PhiD_differentiableOn isoRight_ZD (fun ρ hρ => ZD_im_ne hρ)
    (fun ρ hρ => PhiD_pole hρ) hθ0 hδ hW' (s - 1 / 2) hρ
  simp at this
  rw [hθ] at this
  linarith

/-- F13W with Alpöge's window shape: `[L, 3L/2]` in log scale, i.e. `[Y, Y^{3/2}]`. -/
theorem F13W_three_halves {ε C : ℝ} (hε0 : 0 ≤ ε)
    (hW : ∀ L₀ : ℝ, ∃ L : ℝ, L₀ ≤ L ∧
      ∀ L' ∈ Icc L (3 / 2 * L), -C * Real.exp (ε * L') ≤ Dfun L') :
    ∀ s : ℂ, 1 / 2 + ε < s.re → xiE s ≠ 0 :=
  F13W_xiE_ne_zero (δ := 1 / 2) hε0 (by norm_num) (by
    intro L₀; obtain ⟨L, hL, hb⟩ := hW L₀
    exact ⟨L, hL, fun L' hL' => hb L' (by norm_num at hL' ⊢; exact hL')⟩)

/-- The same conclusion for Mathlib's `riemannZeta` (off the pole). -/
theorem F13W_riemannZeta_ne_zero {ε δ C : ℝ} (hε0 : 0 ≤ ε) (hδ : 0 < δ)
    (hW : ∀ L₀ : ℝ, ∃ L : ℝ, L₀ ≤ L ∧
      ∀ L' ∈ Icc L ((1 + δ) * L), -C * Real.exp (ε * L') ≤ Dfun L') :
    ∀ s : ℂ, 1 / 2 + ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  have hx := F13W_xiE_ne_zero hε0 hδ hW s hs
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs; simp at hs; linarith
  rw [xiE_eq hs0 hs1] at hx
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h0; apply hx; rw [h0, mul_zero]
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp at hs ⊢; linarith)
  rw [riemannZeta_def_of_ne_zero hs0]
  exact div_ne_zero hΛ hG

end Instance

end GppHeartWindow

#print axioms GppHeartWindow.window_landau
#print axioms GppHeartWindow.PhiD_eq_momentLap
#print axioms GppHeartWindow.PhiD_pole
#print axioms GppHeartWindow.F13W_xiE_ne_zero
#print axioms GppHeartWindow.F13W_three_halves
#print axioms GppHeartWindow.F13W_riemannZeta_ne_zero
