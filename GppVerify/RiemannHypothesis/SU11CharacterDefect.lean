import GppVerify.RiemannHypothesis.SU11PrimeBlaschke
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Basic

/-!
# The universal `k = ½` SU(1,1) character, and the de Branges–Rovnyak defect of a Blaschke cascade

Source: Codex, GPPDiscovery2 `research/` (bridge copy through `59bf0a2`):
* `2026-09-27_su11_character_prime_celestial_bridge.md` §§1–7;
* `2026-09-27_prime_tfd_as_debranges_blaschke_defect.md` §§1–5.

## The character

On the paired oscillator, `K_0` has spectrum `n + ½`, so the heat character is
`χ_{1/2}(ℓ) = Σ_n e^{−2ℓ(n+½)} = 1/(2 sinh ℓ)` (`heat_character`).

* `prime_anomalous`: at `ℓ_p = ½ log p`, `χ = √p/(p−1)`, the anomalous TFD covariance `A_p`;
* `prime_normal`: the normal covariance `C_p = e^{−ℓ_p} χ(ℓ_p) = 1/(p−1)`;
* `celestial_weight`: the Archimedean Plancherel weight `πλ/sinh(πλ) = 2ℓ χ(ℓ)` at `ℓ = πλ`;
* `euler_shifted_character`: `Σ_n p^{−s(n+½)} = p^{−s/2} ζ_p(s)` for `Re s > 0`;
* `casimir_half`, `casimir_principal`: `k(k−1) = −¼` at `k = ½`, and `s(s−1) = −(¼ + τ²)` on
  `s = ½ + iτ`. These are equal values of two Casimirs and **not** an identification of the
  lowest-weight and principal-series representations. The note says so too.

## The defect kernel

For a function `B` the Schur defect kernel is `D_B(z,w) = (1 − B(z) conj B(w))/(1 − z w̄)`.

* `defect_blaschke`: `D_{B_a}(z,w) = (1−a²)/((1−az)(1−a w̄))`;
* `defect_blaschke_rank_one`: this is `f(z) conj f(w)` with `f(z) = √(1−a²)/(1−az)`, which is the
  TFD coherent-state amplitude `⟨z|Ω_a⟩`;
* `defect_mul`: `D_{B_1 B_2} = D_{B_1} + B_1 B̄_1 D_{B_2}`;
* `defect_quotient`: `D_{A/B} = (D_A − D_B)/(B(z) conj B(w))`;
* `gram_re_nonneg`: a kernel that is a finite sum of rank-one kernels `F_j(z) conj F_j(w)` is
  positive semidefinite;
* `psd_congruence`: positive semidefiniteness is invariant under `K ↦ K/(B(z) conj B(w))` for
  nonvanishing `B`. Hence `D_{A/B} ⪰ 0 ⟺ D_A − D_B ⪰ 0` (`defect_quotient_psd_iff`).

That last equivalence is the note's reformulation of the prime-versus-Archimedean problem as a
kernel-domination problem. It is an equivalence of statements, not a proof of either side.

## Checks

All identities were verified by hand against the notes; no corrections. The note's remark that
local positivity "never proved RH" is correct: every `D_{B_a}` is rank one and positive
(`defect_blaschke_rank_one`), and the equivalence above shows the relative quotient subtracts two
such objects.

## Scope

Pointwise algebra and finite positive semidefiniteness. **Not formalized:** the Hardy-space
reproducing-kernel statement (that `D_B` is the reproducing kernel of the model space), the
infinite renormalized cascade, and the completed zeta transfer `Θ_ω`. No RH claim.
-/

open Complex GppSU11Prime

namespace GppSU11CharacterDefect

/-! ### The character -/

/-- **The `k = ½` heat character.** `Σ_n e^{−2ℓ(n+½)} = 1/(2 sinh ℓ)` for `ℓ > 0`. -/
theorem heat_character (ℓ : ℝ) (hℓ : 0 < ℓ) :
    HasSum (fun n : ℕ => Real.exp (-2 * ℓ * ((n : ℝ) + 1 / 2))) (1 / (2 * Real.sinh ℓ)) := by
  have hq0 : 0 ≤ Real.exp (-2 * ℓ) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * ℓ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-ℓ))
  have e1 : (fun n : ℕ => Real.exp (-2 * ℓ * ((n : ℝ) + 1 / 2))) =
      fun n => Real.exp (-ℓ) * Real.exp (-2 * ℓ) ^ n := by
    funext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hs : 0 < Real.sinh ℓ := Real.sinh_pos_iff.mpr hℓ
  have e2 : 1 / (2 * Real.sinh ℓ) = Real.exp (-ℓ) * (1 - Real.exp (-2 * ℓ))⁻¹ := by
    have h2 : Real.exp (-2 * ℓ) = Real.exp (-ℓ) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hpos : 0 < Real.exp (-ℓ) := Real.exp_pos _
    have hinv : Real.exp ℓ = (Real.exp (-ℓ))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [Real.sinh_eq, Real.exp_neg, h2]
    have h3 : (1 : ℝ) - Real.exp (-ℓ) ^ 2 ≠ 0 := by
      have : Real.exp (-ℓ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      nlinarith
    have h4 : Real.exp (-ℓ) ≠ 0 := hpos.ne'
    rw [Real.exp_neg] at h3 h4 ⊢
    field_simp
  rw [e1, e2]; exact hg

/-- **Prime anomalous covariance.** `1/(2 sinh(½ log p)) = √p/(p − 1)` for `p > 1`. -/
theorem prime_anomalous (p : ℝ) (hp : 1 < p) :
    1 / (2 * Real.sinh (1 / 2 * Real.log p)) = Real.sqrt p / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp : Real.exp (1 / 2 * Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]; congr 1; ring
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hne : p - 1 ≠ 0 := by linarith
  have h2 : 2 * Real.sinh (1 / 2 * Real.log p) = (p - 1) / Real.sqrt p := by
    rw [Real.sinh_eq, Real.exp_neg, hexp]
    field_simp
    linear_combination hsq
  rw [h2, one_div_div]

/-- **Prime normal covariance.** `e^{−ℓ_p} χ(ℓ_p) = 1/(p − 1)`. -/
theorem prime_normal (p : ℝ) (hp : 1 < p) :
    Real.exp (-(1 / 2 * Real.log p)) * (1 / (2 * Real.sinh (1 / 2 * Real.log p))) =
      1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp : Real.exp (1 / 2 * Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]; congr 1; ring
  rw [prime_anomalous p hp, Real.exp_neg, hexp]
  have hne : p - 1 ≠ 0 := by linarith
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  field_simp

/-- **The celestial Plancherel weight is the same character.**
`ℓ/sinh ℓ = 2ℓ · χ_{1/2}(ℓ)`; with `ℓ = πλ` this is `πλ/sinh(πλ)`. -/
theorem celestial_weight (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ℓ / Real.sinh ℓ = 2 * ℓ * (1 / (2 * Real.sinh ℓ)) := by
  have hs : Real.sinh ℓ ≠ 0 := (Real.sinh_pos_iff.mpr hℓ).ne'
  field_simp

/-- **The Euler factor is a shifted character.** For `p > 1` and `Re s > 0`:
`Σ_n p^{−s(n+½)} = p^{−s/2} ζ_p(s)`, with `ζ_p(s) = (1 − p^{−s})⁻¹`. -/
theorem euler_shifted_character (p : ℝ) (hp : 1 < p) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (p : ℂ) ^ (-(s * ((n : ℂ) + 1 / 2))))
      ((p : ℂ) ^ (-s / 2) * (1 - (p : ℂ) ^ (-s))⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by simpa using hs)
  have hg := (hasSum_geometric_of_norm_lt_one hnorm).mul_left ((p : ℂ) ^ (-s / 2))
  have e1 : (fun n : ℕ => (p : ℂ) ^ (-(s * ((n : ℂ) + 1 / 2)))) =
      fun n => (p : ℂ) ^ (-s / 2) * ((p : ℂ) ^ (-s)) ^ n := by
    funext n
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hp']; congr 1; ring
  rw [e1]; exact hg

/-- `k(k − 1) = −¼` at the lowest weight `k = ½`. -/
theorem casimir_half : (1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) = -(1 / 4) := by norm_num

/-- `s(s − 1) = −(¼ + τ²)` on `s = ½ + iτ`. -/
theorem casimir_principal (τ : ℝ) :
    ((1 / 2 : ℂ) + τ * Complex.I) * (((1 / 2 : ℂ) + τ * Complex.I) - 1) =
      -((1 / 4 : ℂ) + (τ : ℂ) ^ 2) := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### The defect kernel -/

/-- The Schur defect kernel `D_B(z,w) = (1 − B(z) conj B(w))/(1 − z w̄)`. -/
noncomputable def defect (B : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (1 - B z * (starRingEnd ℂ) (B w)) / (1 - z * (starRingEnd ℂ) w)

theorem conj_blaschke (a : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (blaschke (a : ℂ) w) =
      ((starRingEnd ℂ) w - a) / (1 - a * (starRingEnd ℂ) w) := by
  simp [blaschke, map_div₀, map_sub, map_mul]

/-- **The Blaschke defect.** `D_{B_a}(z,w) = (1 − a²)/((1 − az)(1 − a w̄))`. -/
theorem defect_blaschke (a : ℝ) (z w : ℂ) (hzw : 1 - z * (starRingEnd ℂ) w ≠ 0)
    (hz : 1 - (a : ℂ) * z ≠ 0) (hw : 1 - (a : ℂ) * (starRingEnd ℂ) w ≠ 0) :
    defect (blaschke (a : ℂ)) z w =
      (1 - (a : ℂ) ^ 2) / ((1 - a * z) * (1 - a * (starRingEnd ℂ) w)) := by
  unfold defect
  rw [conj_blaschke]
  unfold blaschke
  have hY : (1 - (a : ℂ) * z) * (1 - a * (starRingEnd ℂ) w) ≠ 0 := mul_ne_zero hz hw
  have hnum : (1 - (a : ℂ) * z) * (1 - a * (starRingEnd ℂ) w) -
      (z - a) * ((starRingEnd ℂ) w - a) = (1 - (a : ℂ) ^ 2) * (1 - z * (starRingEnd ℂ) w) := by
    ring
  rw [div_mul_div_comm, one_sub_div hY, div_div, hnum]
  exact mul_div_mul_right _ _ hzw

/-- The TFD amplitude `f_a(z) = √(1 − a²)/(1 − a z) = ⟨z|Ω_a⟩`. -/
noncomputable def tfdAmp (a : ℝ) (z : ℂ) : ℂ := ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) / (1 - a * z)

/-- **The defect is rank one, and its vector is the TFD coherent state.** -/
theorem defect_blaschke_rank_one (a : ℝ) (ha : |a| < 1) (z w : ℂ) :
    (1 - (a : ℂ) ^ 2) / ((1 - a * z) * (1 - a * (starRingEnd ℂ) w)) =
      tfdAmp a z * (starRingEnd ℂ) (tfdAmp a w) := by
  have hpos : 0 ≤ 1 - a ^ 2 := by nlinarith [abs_lt.mp ha, sq_abs a]
  have hsq : ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) =
      1 - (a : ℂ) ^ 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]; push_cast; ring
  unfold tfdAmp
  rw [map_div₀, Complex.conj_ofReal, map_sub, map_one, map_mul, Complex.conj_ofReal]
  rw [div_mul_div_comm, hsq]

/-- **Boundary intensity.** `‖f_a(e^{iθ})‖² = P_a(θ)`. -/
theorem tfdAmp_boundary (a θ : ℝ) (ha : |a| < 1) :
    ‖tfdAmp a (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 = poisson a θ := by
  have hpos : 0 ≤ 1 - a ^ 2 := by nlinarith [abs_lt.mp ha, sq_abs a]
  unfold tfdAmp
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hpos, Complex.sq_norm, normSq_one_sub_polar, poisson]

/-- **Product rule.** `D_{B₁B₂} = D_{B₁} + B₁ B̄₁ D_{B₂}`. -/
theorem defect_mul (B₁ B₂ : ℂ → ℂ) (z w : ℂ) (h : 1 - z * (starRingEnd ℂ) w ≠ 0) :
    defect (fun x => B₁ x * B₂ x) z w =
      defect B₁ z w + B₁ z * (starRingEnd ℂ) (B₁ w) * defect B₂ z w := by
  unfold defect
  simp only [map_mul]
  field_simp
  ring

/-- **Quotient rule.** `D_{A/B} = (D_A − D_B)/(B(z) conj B(w))`. -/
theorem defect_quotient (A B : ℂ → ℂ) (z w : ℂ) (h : 1 - z * (starRingEnd ℂ) w ≠ 0)
    (hz : B z ≠ 0) (hw : B w ≠ 0) :
    defect (fun x => A x / B x) z w =
      (defect A z w - defect B z w) / (B z * (starRingEnd ℂ) (B w)) := by
  have hw' : (starRingEnd ℂ) (B w) ≠ 0 := (map_ne_zero _).mpr hw
  unfold defect
  simp only [map_div₀]
  field_simp
  ring

/-! ### Positive semidefinite kernels -/

/-- A kernel is positive semidefinite if every finite quadratic form is real and nonnegative. -/
def IsPSD {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℂ),
    (∑ i, ∑ k, c i * (starRingEnd ℂ) (c k) * K (x i) (x k)).im = 0 ∧
      0 ≤ (∑ i, ∑ k, c i * (starRingEnd ℂ) (c k) * K (x i) (x k)).re

/-- **A finite sum of rank-one kernels is positive semidefinite.** -/
theorem gram_psd {X κ : Type*} [Fintype κ] (F : κ → X → ℂ) :
    IsPSD (fun z w => ∑ j, F j z * (starRingEnd ℂ) (F j w)) := by
  intro n x c
  have step : ∀ j : κ, (((Complex.normSq (∑ i : Fin n, c i * F j (x i)) : ℝ) : ℂ)) =
      ∑ i : Fin n, ∑ k : Fin n,
        c i * (starRingEnd ℂ) (c k) * (F j (x i) * (starRingEnd ℂ) (F j (x k))) := by
    intro j
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    simp only [map_mul]; ring
  have key : ∑ i : Fin n, ∑ k : Fin n, c i * (starRingEnd ℂ) (c k) *
        ∑ j, F j (x i) * (starRingEnd ℂ) (F j (x k)) =
      ∑ j, ((Complex.normSq (∑ i : Fin n, c i * F j (x i)) : ℝ) : ℂ) := by
    calc ∑ i : Fin n, ∑ k : Fin n, c i * (starRingEnd ℂ) (c k) *
            ∑ j, F j (x i) * (starRingEnd ℂ) (F j (x k))
        = ∑ i : Fin n, ∑ k : Fin n, ∑ j,
            c i * (starRingEnd ℂ) (c k) * (F j (x i) * (starRingEnd ℂ) (F j (x k))) := by
          simp_rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∑ j, ∑ k : Fin n,
            c i * (starRingEnd ℂ) (c k) * (F j (x i) * (starRingEnd ℂ) (F j (x k))) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ j, ∑ i : Fin n, ∑ k : Fin n,
            c i * (starRingEnd ℂ) (c k) * (F j (x i) * (starRingEnd ℂ) (F j (x k))) :=
          Finset.sum_comm
      _ = ∑ j, ((Complex.normSq (∑ i : Fin n, c i * F j (x i)) : ℝ) : ℂ) :=
          Finset.sum_congr rfl (fun j _ => (step j).symm)
  show (∑ i : Fin n, ∑ k : Fin n, c i * (starRingEnd ℂ) (c k) *
        ∑ j, F j (x i) * (starRingEnd ℂ) (F j (x k))).im = 0 ∧
      0 ≤ (∑ i : Fin n, ∑ k : Fin n, c i * (starRingEnd ℂ) (c k) *
        ∑ j, F j (x i) * (starRingEnd ℂ) (F j (x k))).re
  rw [key]
  constructor
  · rw [Complex.im_sum]; simp
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun j _ => by simpa using Complex.normSq_nonneg _)

/-- **Congruence by a nonvanishing function preserves positive semidefiniteness.** -/
theorem psd_congruence_mp {X : Type*} (K : X → X → ℂ) (B : X → ℂ) (hB : ∀ x, B x ≠ 0)
    (hK : IsPSD K) : IsPSD (fun z w => K z w / (B z * (starRingEnd ℂ) (B w))) := by
  intro n x c
  have h := hK n x (fun i => c i / B (x i))
  have e : ∀ i k : Fin n, c i * (starRingEnd ℂ) (c k) * (K (x i) (x k) /
      (B (x i) * (starRingEnd ℂ) (B (x k)))) =
      (c i / B (x i)) * (starRingEnd ℂ) (c k / B (x k)) * K (x i) (x k) := by
    intro i k
    have h1 := hB (x i); have h2 : (starRingEnd ℂ) (B (x k)) ≠ 0 := (map_ne_zero _).mpr (hB (x k))
    simp only [map_div₀]
    field_simp
  simp only [e]
  exact h

/-- **PSD is invariant under congruence by a nonvanishing function.** -/
theorem psd_congruence {X : Type*} (K : X → X → ℂ) (B : X → ℂ) (hB : ∀ x, B x ≠ 0) :
    IsPSD K ↔ IsPSD (fun z w => K z w / (B z * (starRingEnd ℂ) (B w))) := by
  constructor
  · exact psd_congruence_mp K B hB
  · intro h
    have h' := psd_congruence_mp _ (fun x => (B x)⁻¹) (fun x => inv_ne_zero (hB x)) h
    have e : (fun z w => K z w / (B z * (starRingEnd ℂ) (B w)) /
        ((B z)⁻¹ * (starRingEnd ℂ) ((B w)⁻¹))) = K := by
      funext z w
      have h1 := hB z; have h2 : (starRingEnd ℂ) (B w) ≠ 0 := (map_ne_zero _).mpr (hB w)
      simp only [map_inv₀]
      field_simp
    rwa [e] at h'

/-! ### On the open unit disk -/

/-- The open unit disk, as a type. -/
abbrev Disk : Type := {z : ℂ // ‖z‖ < 1}

lemma one_sub_mul_conj_ne (z w : Disk) : 1 - (z : ℂ) * (starRingEnd ℂ) (w : ℂ) ≠ 0 := by
  intro h
  have h1 : (z : ℂ) * (starRingEnd ℂ) (w : ℂ) = 1 := by linear_combination -h
  have h2 : ‖(z : ℂ) * (starRingEnd ℂ) (w : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) z.2 w.2.le
  rw [h1] at h2; simp at h2

lemma one_sub_real_mul_ne (a : ℝ) (ha : |a| < 1) (z : Disk) : 1 - (a : ℂ) * (z : ℂ) ≠ 0 := by
  intro h
  have h1 : (a : ℂ) * (z : ℂ) = 1 := by linear_combination -h
  have h2 : ‖(a : ℂ) * (z : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) ha z.2.le
  rw [h1] at h2; simp at h2

/-- **The relative defect problem.** For `B` nonvanishing on the disk,
`D_{A/B} ⪰ 0 ⟺ D_A − D_B ⪰ 0`. -/
theorem defect_quotient_psd_iff (A B : ℂ → ℂ) (hB : ∀ z : Disk, B z ≠ 0) :
    IsPSD (fun z w : Disk => defect (fun x => A x / B x) z w) ↔
      IsPSD (fun z w : Disk => defect A z w - defect B z w) := by
  have e : (fun z w : Disk => defect (fun x => A x / B x) z w) =
      (fun z w : Disk => (defect A z w - defect B z w) / (B z * (starRingEnd ℂ) (B w))) := by
    funext z w
    exact defect_quotient A B z w (one_sub_mul_conj_ne z w) (hB z) (hB w)
  rw [e]
  exact (psd_congruence (fun z w : Disk => defect A z w - defect B z w) (fun z : Disk => B z) hB).symm

/-- **A single Blaschke defect is positive semidefinite** (it is rank one). -/
theorem blaschke_defect_psd (a : ℝ) (ha : |a| < 1) :
    IsPSD (fun z w : Disk => defect (blaschke (a : ℂ)) z w) := by
  have h := gram_psd (X := Disk) (κ := Unit) (fun _ z => tfdAmp a z)
  have e : (fun z w : Disk => defect (blaschke (a : ℂ)) z w) =
      (fun z w : Disk => ∑ _j : Unit, tfdAmp a z * (starRingEnd ℂ) (tfdAmp a w)) := by
    funext z w
    have hw : 1 - (a : ℂ) * (starRingEnd ℂ) (w : ℂ) ≠ 0 := by
      have := one_sub_real_mul_ne a ha w
      intro h0; apply this
      have := congrArg (starRingEnd ℂ) h0
      simpa [map_sub, map_mul] using this
    rw [defect_blaschke a z w (one_sub_mul_conj_ne z w) (one_sub_real_mul_ne a ha z) hw,
      defect_blaschke_rank_one a ha]
    simp
  rw [e]; exact h

/-- **The finite cascade formula.** For `B^{(N)} = ∏_{j<N} B_{a_j}`:
`D_{B^{(N)}} = Σ_{j<N} (∏_{k<j} B_k(z)) conj(∏_{k<j} B_k(w)) D_{B_j}`. -/
theorem defect_cascade (a : ℕ → ℝ) (N : ℕ) (z w : ℂ) (h : 1 - z * (starRingEnd ℂ) w ≠ 0) :
    defect (fun x => ∏ j ∈ Finset.range N, blaschke (a j : ℂ) x) z w =
      ∑ j ∈ Finset.range N,
        (∏ k ∈ Finset.range j, blaschke (a k : ℂ) z) *
          (starRingEnd ℂ) (∏ k ∈ Finset.range j, blaschke (a k : ℂ) w) *
          defect (blaschke (a j : ℂ)) z w := by
  induction N with
  | zero =>
    simp [defect]
  | succ N ih =>
    have e : (fun x => ∏ j ∈ Finset.range (N + 1), blaschke (a j : ℂ) x) =
        fun x => (∏ j ∈ Finset.range N, blaschke (a j : ℂ) x) * blaschke (a N : ℂ) x := by
      funext x; rw [Finset.prod_range_succ]
    rw [e, defect_mul _ _ z w h, ih, Finset.sum_range_succ]

/-- **The finite prime cascade has an explicit positive Gram factorization.**
`D_{B^{(N)}}(z,w) = Σ_{j<N} F_j(z) conj F_j(w)` with `F_j = (∏_{k<j} B_k) · f_{a_j}`, and so is
positive semidefinite on the disk. -/
theorem cascade_defect_psd (a : ℕ → ℝ) (ha : ∀ j, |a j| < 1) (N : ℕ) :
    IsPSD (fun z w : Disk => defect (fun x => ∏ j ∈ Finset.range N, blaschke (a j : ℂ) x) z w) := by
  have h := gram_psd (X := Disk) (κ := Fin N)
    (fun j z => (∏ k ∈ Finset.range (j : ℕ), blaschke (a k : ℂ) z) * tfdAmp (a j) z)
  have e : (fun z w : Disk => defect (fun x => ∏ j ∈ Finset.range N, blaschke (a j : ℂ) x) z w) =
      (fun z w : Disk => ∑ j : Fin N,
        ((∏ k ∈ Finset.range (j : ℕ), blaschke (a k : ℂ) z) * tfdAmp (a j) z) *
          (starRingEnd ℂ) ((∏ k ∈ Finset.range (j : ℕ), blaschke (a k : ℂ) w) *
            tfdAmp (a j) w)) := by
    funext z w
    rw [defect_cascade a N z w (one_sub_mul_conj_ne z w), ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hw : 1 - (a j : ℂ) * (starRingEnd ℂ) (w : ℂ) ≠ 0 := by
      have := one_sub_real_mul_ne (a j) (ha j) w
      intro h0; apply this
      have := congrArg (starRingEnd ℂ) h0
      simpa [map_sub, map_mul] using this
    rw [defect_blaschke (a j) z w (one_sub_mul_conj_ne z w) (one_sub_real_mul_ne (a j) (ha j) z) hw,
      defect_blaschke_rank_one (a j) (ha j), map_mul]
    ring
  rw [e]; exact h

end GppSU11CharacterDefect
