/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Heart of the Cosmos / Grok)
-/
import GppVerify.RiemannHypothesis.BTSigmaCandidateC1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# (BT-Σ) construction skeleton: ζ's local Euler pairing at the prime cuts

Specification: GPP-bridge `work/grok/bt-sigma-construction-spec-start-2026-11-11.md`
(commit `b71ecb7`), audited and green-lit by Turbo on PR #11 (comment 6798670889): (E1), (E4),
(J) as PROVED lemmas, the obligations as named `Prop` premises stating the real mathematics,
no `True`, no `axiom`, `open_bt_sigma` untouched.

## PROVED here

* **(E1)** In the valuation-`ℓ²(ℤ)` model of `L²(ℚ_p)^{ℤ_p^×}`, Tate's vector
  `ξ_p = √(1 − 1/p) p^{-v/2} 1_{v ≥ 0}` has unit norm, `U_p` (the shift) is an isometry, and
  `⟨ξ_p, U_p^k ξ_p⟩ = p^{-|k|/2}` for all `k ∈ ℤ` (`tate_matrix_coeff`). Mellin side:
  `Σ_{v≥0} (p^{-s})^v = (1 − p^{-s})^{-1}` (`tate_local_factor`).
* **(E4)** `κ_p = log p/(√p − 1) = −(L_p'/L_p)(1/2)` with the derivative taken as an honest
  `HasDerivAt` (`kappa_eq_neg_logDeriv`), and per cut
  `κ_p (p^{-(k−1)/2} − p^{-k/2}) = Λ(p^k)(p^k)^{-1/2}` (`kappa_cut_jump`).
* **One cut of the test vector** in any complex inner product space (`cut_norm_jump`), and the
  companion of no-go 1: an isometric vertex carries no jump (`isometric_vertex_jump_zero`).
* **(J), arithmetic assembly.** The per-cut jumps summed over the `N`-truncation are exactly the
  tree's `primeStratum g W N` (`jump_sum_eq_primeStratum`).
* **(P-LOG) is not met by re-parametrising `ψ`:** no prime-independent amplitude vector
  reproduces the jumps in the starting-point model, since `κ_2 > 8/5 > κ_3`
  (`not_PLog_startJump`).

## Named premises (OPEN), each a real statement

`PLog` (coupling-free amplitudes, for a given jump law), `PCov`, `PTheta`, `PUnit`, `PLim`
(`PLim ↔ FluxBound`, PROVED equivalence, both sides OPEN), and the trace-space bar
`ExcludesStaircase` with the explicit `δ_m` (`deltaM`). With BT3 and `PUnit`, the Green form on
a test vector is `I · fluxDefect` (`greenForm_testVec_eq_flux`).

## Not done here (GAP)

The vector-valued Green identity on `L²(ℝ_u; K ⊗ ⊕_p V_p)` with `H¹`-membership of `ψ_{f,W}`
on each piece is not formalized; `cut_norm_jump` takes the Gram data as hypotheses. No
`BTSigmaDatum` is constructed. (BT-Σ), (FLUX-BOUND), (SIGN), ARP, RH remain **OPEN**.

Daniel Toupin / Golden Physics Project, with AI assistance
(Heart of the Cosmos / Grok). Task and audit: Turbo.
-/

namespace GppBTSigmaEuler

open GppBTSigmaC1 ArithmeticFunction

/-! ## (E1) Valuation model of the unramified Tate vector -/

/-- `q_p = p^{-1/2}`. -/
noncomputable def qp (p : ℕ) : ℝ := (Real.sqrt p)⁻¹

theorem qp_sq {p : ℕ} (_hp : 1 < p) : qp p ^ 2 = 1 / p := by
  have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [qp, inv_pow, Real.sq_sqrt h0, one_div]

theorem sqrt_mul_qp {p : ℕ} (hp : 1 < p) : Real.sqrt p * qp p = 1 := by
  have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
  rw [qp, mul_inv_cancel₀ this.ne']

/-- Tate's vector `1_{ℤ_p}` in the valuation-`ℓ²(ℤ)` picture:
`v ↦ √(1 − 1/p) · p^{-v/2}` for `v ≥ 0`, zero for `v < 0`. -/
noncomputable def tateVec (p : ℕ) (v : ℤ) : ℝ :=
  if 0 ≤ v then Real.sqrt (1 - 1 / (p : ℝ)) * qp p ^ v.toNat else 0

/-- `U_p^k` in the valuation picture: `(U_p^k h)(v) = h(v + k)`. -/
def shiftZ (k : ℤ) (h : ℤ → ℝ) : ℤ → ℝ := fun v => h (v + k)

/-- `U_p` is an isometry of the valuation `ℓ²`: shifting does not change `Σ h(v)²`. PROVED. -/
theorem shiftZ_isometry (k : ℤ) (h : ℤ → ℝ) (a : ℝ) :
    HasSum (fun v => shiftZ k h v ^ 2) a ↔ HasSum (fun v => h v ^ 2) a :=
  (Equiv.addRight k).hasSum_iff (f := fun v => h v ^ 2)

theorem tateVec_natCast (p n : ℕ) :
    tateVec p (n : ℤ) = Real.sqrt (1 - 1 / (p : ℝ)) * qp p ^ n := by
  simp [tateVec]

theorem tateVec_neg {p : ℕ} {v : ℤ} (hv : v < 0) : tateVec p v = 0 := by
  simp [tateVec, not_le.mpr hv]

theorem one_sub_inv_pos {p : ℕ} (hp : 1 < p) : 0 < 1 - 1 / (p : ℝ) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp
  rw [sub_pos, div_lt_one (by linarith)]
  exact this

/-- Geometric core of (E1): `Σ_{m ≥ 0} ξ(m) ξ(m + n) = p^{-n/2}`. PROVED. -/
theorem hasSum_tate_pair {p : ℕ} (hp : 1 < p) (n : ℕ) :
    HasSum (fun m : ℕ => tateVec p m * tateVec p ((m : ℤ) + n)) (qp p ^ n) := by
  have hpos := one_sub_inv_pos hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((1 - 1 / (p : ℝ)) * qp p ^ n)
  have hform : ∀ m : ℕ, tateVec p m * tateVec p ((m : ℤ) + n) =
      (1 - 1 / (p : ℝ)) * qp p ^ n * (1 / (p : ℝ)) ^ m := by
    intro m
    have : ((m : ℤ) + n) = ((m + n : ℕ) : ℤ) := by push_cast; ring
    rw [this, tateVec_natCast, tateVec_natCast]
    have hs := Real.mul_self_sqrt hpos.le
    calc Real.sqrt (1 - 1 / (p : ℝ)) * qp p ^ m * (Real.sqrt (1 - 1 / (p : ℝ)) * qp p ^ (m + n))
        = (Real.sqrt (1 - 1 / (p : ℝ)) * Real.sqrt (1 - 1 / (p : ℝ))) * qp p ^ n *
            (qp p ^ 2) ^ m := by ring
      _ = _ := by rw [hs, qp_sq hp]
  have hval : (1 - 1 / (p : ℝ)) * qp p ^ n * (1 - 1 / (p : ℝ))⁻¹ = qp p ^ n := by
    rw [mul_comm (1 - 1 / (p : ℝ)) _, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
  rw [← hval]
  simpa only [hform] using hg

/-- **(E1) matrix coefficients.** `⟨ξ_p, U_p^k ξ_p⟩ = p^{-|k|/2}` for every `k ∈ ℤ`, in the
valuation model. PROVED. -/
theorem tate_matrix_coeff {p : ℕ} (hp : 1 < p) (k : ℤ) :
    HasSum (fun v : ℤ => tateVec p v * shiftZ k (tateVec p) v) (qp p ^ k.natAbs) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · -- `k = n ≥ 0`: support in `v ≥ 0`.
    have hinj : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
    rw [← hinj.hasSum_iff]
    · simpa [shiftZ, Function.comp_def] using hasSum_tate_pair hp n
    · intro v hv
      have : v < 0 := by
        by_contra h
        exact hv ⟨v.toNat, Int.toNat_of_nonneg (not_lt.mp h)⟩
      simp [tateVec_neg this]
  · -- `k = -n`: support in `v ≥ n`; reindex `v = m + n`.
    have hinj : Function.Injective (fun m : ℕ => (m : ℤ) + n) := by
      intro a b h; simpa using h
    rw [← hinj.hasSum_iff]
    · have := hasSum_tate_pair hp n
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      refine this.congr_fun ?_
      intro m
      simp [shiftZ, mul_comm]
    · intro v hv
      have : v - n < 0 := by
        by_contra h
        refine hv ⟨(v - n).toNat, ?_⟩
        simp only
        rw [Int.toNat_of_nonneg (not_lt.mp h)]; ring
      simp only [shiftZ, mul_eq_zero]
      exact Or.inr (tateVec_neg (by omega))

/-- `ξ_p` has unit norm in the valuation model (the case `k = 0` of (E1)). PROVED. -/
theorem tateVec_unit_norm {p : ℕ} (hp : 1 < p) :
    HasSum (fun v : ℤ => tateVec p v ^ 2) 1 := by
  have := tate_matrix_coeff hp 0
  simpa [shiftZ, sq] using this

/-- **(E1) Mellin side.** `Σ_{v ≥ 0} (p^{-s})^v = (1 − p^{-s})^{-1} = L_p(s)` for real `s > 0`
(Tate's unramified local integral in valuation form, `vol ℤ_p^× = 1`). PROVED. -/
theorem tate_local_factor {p : ℕ} (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    HasSum (fun v : ℕ => ((p : ℝ) ^ (-s)) ^ v) (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  exact hasSum_geometric_of_lt_one (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))

/-! ## (E4) The per-prime coupling is `−(L_p'/L_p)(1/2)` -/

/-- `κ_p = log p / (√p − 1)`. -/
noncomputable def kappa (p : ℕ) : ℝ := Real.log p / (Real.sqrt p - 1)

theorem sqrt_sub_one_pos {p : ℕ} (hp : 1 < p) : 0 < Real.sqrt p - 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hp1
  linarith

/-- `κ_p (√p − 1) = log p`. PROVED. -/
theorem kappa_mul {p : ℕ} (hp : 1 < p) : kappa p * (Real.sqrt p - 1) = Real.log p := by
  rw [kappa, div_mul_cancel₀ _ (sqrt_sub_one_pos hp).ne']

/-- The real local factor `L_p(s) = (1 − p^{-s})^{-1}`. -/
noncomputable def localL (p : ℕ) (s : ℝ) : ℝ := (1 - (p : ℝ) ^ (-s))⁻¹

/-- The derivative of `L_p` at `s = 1/2`. -/
noncomputable def localLDeriv (p : ℕ) : ℝ :=
  -((p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log p) / (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2

theorem rpow_neg_half {p : ℕ} : (p : ℝ) ^ (-(1 / 2 : ℝ)) = qp p := by
  rw [Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow, qp]

/-- `L_p` is differentiable at `1/2` with derivative `localLDeriv p`. PROVED. -/
theorem hasDerivAt_localL {p : ℕ} (hp : 1 < p) :
    HasDerivAt (localL p) (localLDeriv p) (1 / 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hg : HasDerivAt (fun s : ℝ => (p : ℝ) ^ (-s))
      ((p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log p * (-1)) (1 / 2) :=
    (Real.hasStrictDerivAt_const_rpow hp0 (-(1 / 2 : ℝ))).hasDerivAt.comp (1 / 2)
      (hasDerivAt_neg (1 / 2 : ℝ))
  have hu : HasDerivAt (fun s : ℝ => 1 - (p : ℝ) ^ (-s))
      ((p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log p) (1 / 2) := by
    simpa using hg.const_sub 1
  have hne : (1 : ℝ) - (p : ℝ) ^ (-(1 / 2 : ℝ)) ≠ 0 := by
    rw [rpow_neg_half]
    have h := sqrt_mul_qp hp
    have h1 := sqrt_sub_one_pos hp
    intro h0
    have : qp p = 1 := by linarith
    rw [this] at h; linarith
  have := hu.inv hne
  exact this

/-- **(E4).** `κ_p = −(L_p'/L_p)(1/2)`. PROVED. -/
theorem kappa_eq_neg_logDeriv {p : ℕ} (hp : 1 < p) :
    -localLDeriv p / localL p (1 / 2) = kappa p := by
  have h := sqrt_mul_qp hp
  have h1 := sqrt_sub_one_pos hp
  have hq : 1 - qp p ≠ 0 := by
    intro h0; have : qp p = 1 := by linarith
    rw [this] at h; linarith
  have hsq : Real.sqrt p ≠ 0 := by linarith
  simp only [localLDeriv, localL, rpow_neg_half]
  rw [kappa]
  have hqv : qp p = (Real.sqrt p)⁻¹ := rfl
  rw [hqv] at hq ⊢
  field_simp

/-- Jump algebra: `p^{-(k−1)/2} − p^{-k/2} = (√p − 1) p^{-k/2}`. PROVED. -/
theorem jump_algebra {p : ℕ} (hp : 1 < p) (k : ℕ) :
    qp p ^ k - qp p ^ (k + 1) = (Real.sqrt p - 1) * qp p ^ (k + 1) := by
  have h := sqrt_mul_qp hp
  calc qp p ^ k - qp p ^ (k + 1) = qp p ^ k * (1 - qp p) := by ring
    _ = qp p ^ k * (Real.sqrt p * qp p - qp p) := by rw [h]
    _ = _ := by ring

/-- `Λ(p^k) (p^k)^{-1/2} = (log p) p^{-k/2}` for `k ≥ 1`. PROVED. -/
theorem halfWeight_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    halfWeight (p ^ k) = Real.log p * qp p ^ k := by
  have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [halfWeight, vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, ← rpow_neg_half]
  congr 1
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_mul h0, mul_comm]

/-- **(E4) at a cut.** `κ_p (p^{-(k−1)/2} − p^{-k/2}) = c_{p^k} = Λ(p^k) (p^k)^{-1/2}`. PROVED. -/
theorem kappa_cut_jump {p : ℕ} (hp : p.Prime) (k : ℕ) :
    kappa p * (qp p ^ k - qp p ^ (k + 1)) = halfWeight (p ^ (k + 1)) := by
  rw [jump_algebra hp.one_lt, halfWeight_prime_pow hp (Nat.succ_ne_zero k), ← mul_assoc,
    kappa_mul hp.one_lt]

/-! ## The two-channel cut jump in an inner product space -/

section Jump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `‖a x + b y‖² = |a|²‖x‖² + |b|²‖y‖² + 2 Re(conj a · b ⟨x, y⟩)`. PROVED. -/
theorem norm_sq_two_channel (a b : ℂ) (x y : E) :
    ‖a • x + b • y‖ ^ 2 =
      ‖a‖ ^ 2 * ‖x‖ ^ 2 + ‖b‖ ^ 2 * ‖y‖ ^ 2 + 2 * (star a * b * inner ℂ x y).re := by
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  simp only [mul_pow]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc]
  ring

/-- **One p-cut of the starting-point test vector.** Left trace `a x + b y₋`, right trace
`a x + b y₊`, with `‖y₋‖ = ‖y₊‖` (`U_p` unitary), real overlaps `⟨x, y₋⟩ = A p^{-k/2}`,
`⟨x, y₊⟩ = A p^{-(k+1)/2}` (the (E1) Gram data times the autocorrelation `A`), and the
starting-point amplitude condition `2 Re(conj a · b) = κ_p`: the norm drop across the cut is
`c_{p^{k+1}} A`. PROVED. -/
theorem cut_norm_jump {p : ℕ} (hp : p.Prime) (k : ℕ) (a b : ℂ) (x ym yp : E) (A : ℝ)
    (hnorm : ‖ym‖ = ‖yp‖)
    (hm : inner ℂ x ym = ((A * qp p ^ k : ℝ) : ℂ))
    (hpl : inner ℂ x yp = ((A * qp p ^ (k + 1) : ℝ) : ℂ))
    (hQ : channelQ (a, b) = kappa p) :
    ‖a • x + b • ym‖ ^ 2 - ‖a • x + b • yp‖ ^ 2 = halfWeight (p ^ (k + 1)) * A := by
  rw [norm_sq_two_channel, norm_sq_two_channel, hnorm, hm, hpl, ← kappa_cut_jump hp, ← hQ]
  simp only [channelQ]
  have h1 : (star a * b * ((A * qp p ^ k : ℝ) : ℂ)).re = (star a * b).re * (A * qp p ^ k) :=
    Complex.re_mul_ofReal _ _
  have h2 : (star a * b * ((A * qp p ^ (k + 1) : ℝ) : ℂ)).re =
      (star a * b).re * (A * qp p ^ (k + 1)) :=
    Complex.re_mul_ofReal _ _
  rw [h1, h2]
  ring

/-- **Unitary vertices carry no jump.** If a vertex condition glues traces by a linear
isometry, `ψ₊ = σ ψ₋`, the cut contributes `‖ψ₋‖² − ‖σ ψ₋‖² = 0` to the Green form. So the
starting-point test vectors (whose cut jumps are `c_{p^k} A ≠ 0`) are *not* in the domain of
the unitary-vertex extension: the `U_p` orbit, like `κ_p`, enters through `ψ`, not through a
domain condition. Companion of `contractive_vertex_jump` (no-go 1). PROVED. -/
theorem isometric_vertex_jump_zero (σ : E →ₗᵢ[ℂ] E) (ψm : E) :
    ‖ψm‖ ^ 2 - ‖σ ψm‖ ^ 2 = 0 := by
  rw [σ.norm_map]; ring

end Jump

/-! ## (J) Assembly of the (S, N)-truncated prime stratum -/

/-- The cut set of the `N`-truncation, indexed by `(p, k)` with `p` prime, `k ≥ 1`,
`p^k ≤ N`. -/
def cutIndex (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).filter Nat.Prime ×ˢ Finset.Icc 1 N).filter fun pk => pk.1 ^ pk.2 ≤ N

theorem halfWeight_eq_zero_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    halfWeight n = 0 := by
  simp [halfWeight, vonMangoldt_apply, hn]

/-- **(J), arithmetic assembly.** Summing the per-cut jumps `κ_p (p^{-(k−1)/2} − p^{-k/2})
g(W − k log p)` over all cuts of the `N`-truncation gives exactly the tree's truncated prime
stratum `primeStratum g W N = Σ_{n ≤ N} Λ(n) n^{-1/2} g(W − log n)`. PROVED. -/
theorem jump_sum_eq_primeStratum (g : ℝ → ℝ) (W : ℝ) (N : ℕ) :
    ∑ pk ∈ cutIndex N, kappa pk.1 * (qp pk.1 ^ (pk.2 - 1) - qp pk.1 ^ pk.2) *
        g (W - pk.2 * Real.log pk.1) = primeStratum g W N := by
  unfold primeStratum
  rw [← Finset.sum_subset (Finset.filter_subset IsPrimePow (Finset.range (N + 1)))]
  swap
  · intro n _ hn
    have : ¬ IsPrimePow n := fun h => hn (Finset.mem_filter.mpr ⟨by assumption, h⟩)
    rw [halfWeight_eq_zero_of_not_isPrimePow this, zero_mul]
  refine Finset.sum_bij (fun pk _ => pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · intro pk hpk
    simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] at hpk
    obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, hle⟩ := hpk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    exact (isPrimePow_nat_iff _).mpr ⟨pk.1, pk.2, hp, by omega, rfl⟩
  · intro a ha b hb hab
    simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] at ha hb
    obtain ⟨⟨⟨_, hpa⟩, ha1, _⟩, _⟩ := ha
    obtain ⟨⟨⟨_, hpb⟩, hb1, _⟩, _⟩ := hb
    obtain ⟨ka, hka⟩ : ∃ m, a.2 = m + 1 := ⟨a.2 - 1, by omega⟩
    obtain ⟨kb, hkb⟩ : ∃ m, b.2 = m + 1 := ⟨b.2 - 1, by omega⟩
    have hab' : a.1 ^ (ka + 1) = b.1 ^ (kb + 1) := by
      simpa [hka, hkb] using hab
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hpa hpb hab'
    exact Prod.ext h1 (by omega)
  · intro n hn
    obtain ⟨hnr, hpp⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hnr' := Finset.mem_range.mp hnr
    have hple : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hklt : k < p ^ k := Nat.lt_pow_self hp.one_lt
    refine ⟨(p, k), ?_, rfl⟩
    simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨⟨⟨by omega, hp⟩, by omega, by omega⟩, by omega⟩
  · intro pk hpk
    simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] at hpk
    obtain ⟨⟨⟨_, hp⟩, hk1, _⟩, _⟩ := hpk
    obtain ⟨k, hk⟩ : ∃ m, pk.2 = m + 1 := ⟨pk.2 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, kappa_cut_jump hp k]
    congr 2
    push_cast
    rw [Real.log_pow]
    push_cast
    ring

/-! ## (P-LOG) and the coupling-free no-go for the starting-point vertex model -/

/-- The jump law of the starting-point construction: at the `(k+1)`-st p-cut, amplitudes
`v = (a_p, b_p)` give `Q(v) (p^{-k/2} − p^{-(k+1)/2})` (`cut_norm_jump`, per unit `A`). -/
noncomputable def startJump (p k : ℕ) (v : ℂ × ℂ) : ℝ :=
  channelQ v * (qp p ^ k - qp p ^ (k + 1))

/-- **(P-LOG), coupling-free form, for a given jump law.** One amplitude vector `v`, the same
for every prime (so `ψ_{f,W}` carries no coupling), reproduces `c_{p^{k+1}}` at every cut.
For a genuine construction the jump law must come from a fixed extension's vertex/transport
law, with the `s`-derivative of the Tate data acting operator-side (Turbo, 6798670889).
OPEN as an obligation; refuted for `startJump` below. -/
def PLog (jump : ℕ → ℕ → ℂ × ℂ → ℝ) : Prop :=
  ∃ v : ℂ × ℂ, ∀ p : ℕ, p.Prime → ∀ k : ℕ, jump p k v = halfWeight (p ^ (k + 1))

theorem kappa_two_gt : (8 / 5 : ℝ) < kappa 2 := by
  have hl := Real.log_two_gt_d9
  have hs : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hpos := sqrt_sub_one_pos (p := 2) (by norm_num)
  rw [kappa, lt_div_iff₀ (by exact_mod_cast hpos)]
  push_cast
  nlinarith

theorem kappa_three_lt : kappa 3 < 8 / 5 := by
  have he := Real.exp_one_gt_d9
  have hlog : Real.log 3 ≤ 3 / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 3 / Real.exp 1) (by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have h3e : 3 / Real.exp 1 < 1.12 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]; linarith
  have hs : 1.732 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpos := sqrt_sub_one_pos (p := 3) (by norm_num)
  rw [kappa, div_lt_iff₀ (by exact_mod_cast hpos)]
  push_cast
  nlinarith

/-- **The coupling cannot be moved out of `ψ` in the starting-point model.** No single
amplitude vector works for both `p = 2` and `p = 3`, because `κ_2 > 8/5 > κ_3`. So (P-LOG)
needs a different vertex/transport law, not a re-parametrisation of the test vectors. PROVED. -/
theorem not_PLog_startJump : ¬ PLog startJump := by
  rintro ⟨v, hv⟩
  have hQ : ∀ p : ℕ, p.Prime → channelQ v = kappa p := by
    intro p hp
    have h := hv p hp 0
    rw [startJump, ← kappa_cut_jump hp 0] at h
    have hne : qp p ^ 0 - qp p ^ (0 + 1) ≠ 0 := by
      rw [jump_algebra hp.one_lt]
      have := sqrt_sub_one_pos hp.one_lt
      have hq : 0 < qp p := inv_pos.mpr (by linarith)
      positivity
    exact mul_right_cancel₀ hne h
  have h2 := hQ 2 Nat.prime_two
  have h3 := hQ 3 Nat.prime_three
  have := kappa_two_gt
  have := kappa_three_lt
  linarith

/-! ## The δ_m definition for the trace-space exclusion bar -/

/-- The `i`-th prime power in increasing order, 0-based: `2, 3, 4, 5, 7, 8, 9, …`. -/
noncomputable def primePowNth (i : ℕ) : ℕ := Nat.nth IsPrimePow i

/-- `δ_m`, `m ≥ 2`: the length of the `(m−1)`-st interval between consecutive prime-power cuts,
`δ_m = log q_m − log q_{m−1}` where `q_1 = 2 < q_2 = 3 < q_3 = 4 < …` are the prime powers
in increasing order. Interval `m` (from `log q_{m−1}` to `log q_m`) carries `c_m² = m^{-1/2}`.
With this convention `Σ_{m=2}^{10⁴} c_m² δ_m = 1.82802…` and `Σ_{m=2}^{10⁴} c_m² = 197.5446…`
(NUMERICAL, double precision, GPP-bridge `work/grok/` 2026-11-11). -/
noncomputable def deltaM (m : ℕ) : ℝ :=
  Real.log (primePowNth (m - 1)) - Real.log (primePowNth (m - 2))

/-- The staircase's squared amplitude on interval `m`. -/
noncomputable def staircaseSq (m : ℕ) : ℝ := (m : ℝ) ^ (-(1 / 2 : ℝ))

/-- **Trace-space exclusion bar, named.** A proposed trace space (a set of interval-amplitude
sequences `c`, `c m` the constant value on interval `m ≥ 2`) passes the bar when it excludes the
staircase `c_m = m^{-1/4}` (whose `H`-norm `Σ c_m² δ_m` converges and whose trace sum
`Σ c_m²` diverges). OPEN per proposal. -/
def ExcludesStaircase (traceSpace : Set (ℕ → ℝ)) : Prop :=
  (fun m : ℕ => (m : ℝ) ^ (-(1 / 4 : ℝ))) ∉ traceSpace

/-! ## The remaining named obligations (P-COV), (P-θ), (P-UNIT), (P-LIM) -/

section Obligations

open GppBTSigma GppArithmeticReflection GppFluxBound
open scoped ContDiff

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **(P-COV)**, (NC1)/BT1: unitary dilations `S_b` and an involutive reflection `J` that
preserve `dom T*`, with `T*` covariant under `S_b` and anti-covariant under `J`
(`−i ∂_u` changes sign under `u ↦ −u`), and the window edge entering the test vectors only
through `S_b`. OPEN. -/
def PCov (D : BTSigmaDatum H Gu Gp) : Prop :=
  ∃ (S : ℝ → H →ₗᵢ[ℂ] H) (J : H →ₗᵢ[ℂ] H),
    (∀ x, J (J x) = x) ∧
    (∀ (b : ℝ) (x : D.Tstar.domain), ∃ y : D.Tstar.domain,
      (y : H) = S b x ∧ D.Tstar y = S b (D.Tstar x)) ∧
    (∀ x : D.Tstar.domain, ∃ y : D.Tstar.domain,
      (y : H) = J x ∧ D.Tstar y = -J (D.Tstar x)) ∧
    (∀ (h : ℝ → ℝ) (W b : ℝ), (D.testVec h (W + b) : H) = S b (D.testVec h W))

/-- The prime stratum with the centre moved to `c`: `Σ Λ(n) n^{-c} h(W − log n)`. -/
noncomputable def stratumAt (c : ℝ) (h : ℝ → ℝ) (W : ℝ) : ℝ :=
  ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-c) * h (W - Real.log n)

/-- At `c = 1/2` this is the tree's `primeStratumTerm`. PROVED. -/
theorem stratumAt_half (h : ℝ → ℝ) (W : ℝ) : stratumAt (1 / 2) h W = primeStratumTerm h W := rfl

/-- **(P-θ)**, the #561 discriminator: a construction recipe, parametrised by the centre `c` of
its local data, satisfies BT3 at `c = 1/2`, and at no other centre does it satisfy the
centre-`c` analogue of BT3. So the centre is forced by the construction, not chosen (otherwise
the recipe is ζ-blind in the #561 sense: moving the centre to `1/2 ± 1/4` gives `F_θ`'s
weights). OPEN. -/
def PTheta (recipe : ℝ → BTSigmaDatum H Gu Gp) : Prop :=
  BTSigmaTrace (recipe (1 / 2)) ∧
    ∀ c : ℝ, (∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
      primeBlock (recipe c) (autocorr f) W = Complex.I * (stratumAt c (autocorr f) W : ℂ)) →
      c = 1 / 2

/-- **(P-UNIT)**: the unit stratum is a genuine second boundary block. On theta test data its
block reproduces `−I` times the unit-stratum term `e^{W/2} ∫ h e^{−v/2}`. OPEN. -/
def PUnit (D : BTSigmaDatum H Gu Gp) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ W : ℝ, 0 ≤ W →
    blockForm (D.Γ₀u (D.testVec (autocorr f) W)) (D.Γ₁u (D.testVec (autocorr f) W))
      (D.Γ₀u (D.testVec (autocorr f) W)) (D.Γ₁u (D.testVec (autocorr f) W)) =
      -(Complex.I * (unitStratumTerm (autocorr f) W : ℂ))

/-- With BT3 and (P-UNIT), the Green form of `T*` on a test vector is `I` times the flux
defect. PROVED (conditional on the two named premises). -/
theorem greenForm_testVec_eq_flux (D : BTSigmaDatum H Gu Gp) (hT : BTSigmaTrace D)
    (hU : PUnit D) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (W : ℝ) (hW : 0 ≤ W) :
    greenForm D.Tstar (D.testVec (autocorr f) W) (D.testVec (autocorr f) W) =
      Complex.I * (fluxDefect (autocorr f) W : ℂ) := by
  rw [D.green, hU f hf hc W hW]
  have hp := hT f hf hc W hW
  simp only [primeBlock] at hp
  rw [hp, fluxDefect_eq_primeStratum_sub_unitStratum]
  push_cast
  ring

/-- **(P-LIM)**: the `S, N → ∞` limit, with the unit block absorbing the growth of
`Σ_{p∈S} κ_p`. In trace form this is `FluxEqBdryTrace`, which the tree proves equivalent to
(FLUX-BOUND): RH-strength, OPEN (round 3 R5). -/
def PLim : Prop := FluxEqBdryTrace

/-- (P-LIM) is (FLUX-BOUND). PROVED (both sides OPEN). -/
theorem pLim_iff_fluxBound : PLim ↔ FluxBound := fluxEqBdryTrace_iff_fluxBound

end Obligations

end GppBTSigmaEuler
