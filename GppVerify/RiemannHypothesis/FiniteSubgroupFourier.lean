import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Finite additive Fourier duality turns a subgroup state into its annihilator state

Source: Codex, GPPDiscovery2 `research/2026-09-28_finite_selfdual_divisor_hodge_geometry.md`, §2
(the step left unformalized in `GppSelfDualDivisor`).

On `ZMod (d·M)` let `1_{H_d}` be the indicator of the subgroup `H_d = dℤ/(dM)ℤ` of multiples of `d`
(`|H_d| = M`).

* `dft_indicator`: the (unnormalized) discrete Fourier transform of `1_{H_d}` is `M · 1_{H_M}`: the
  annihilator of `H_d` is `H_M = H_{N/d}`;
* `fourier_subgroup_state`: for the normalized states `v_e = |H_e|^{-1/2} 1_{H_e}`,
  `N^{-1/2} 𝓕 v_d = v_{N/d}`. The half-density normalization is forced by unitarity of finite
  additive Fourier duality: `√(M)·M^{-1}... = d^{-1/2}`, the amplitude of the normalized annihilator
  (whose size is `d`).

## Checks and scope

The claim checks. The proof is a direct geometric-sum computation (no appeal to the general theory of
annihilators). **Not formalized:** the Hodge/Koszul reading of complementation on the squarefree
divisor cube. No RH claim.
-/

open Finset Complex

namespace GppFiniteSubgroupFourier

variable (d M : ℕ) [NeZero d] [NeZero M]

instance : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩

/-- The indicator of the multiples of `d` in `ZMod (d·M)`. -/
noncomputable def ind (e : ℕ) {N : ℕ} (x : ZMod N) : ℂ := if e ∣ x.val then 1 else 0

private theorem val_natCast_lt {N n : ℕ} (hn : n < N) : ((n : ZMod N)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

/-- **The Fourier transform of a subgroup indicator.** -/
theorem dft_indicator (k : ZMod (d * M)) :
    ZMod.dft (ind d : ZMod (d * M) → ℂ) k = if M ∣ k.val then (M : ℂ) else 0 := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  rw [ZMod.dft_apply]
  simp only [ind, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  -- reindex the multiples of `d` as `d · m`, `m < M`
  have hre : ∑ j ∈ (univ : Finset (ZMod (d * M))).filter (fun j => d ∣ j.val),
      ZMod.stdAddChar (-(j * k)) =
      ∑ m ∈ range M, ZMod.stdAddChar (-(((d * m : ℕ) : ZMod (d * M)) * k)) := by
    refine Finset.sum_nbij' (fun j => j.val / d) (fun m => ((d * m : ℕ) : ZMod (d * M)))
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_filter] at hj
      rw [mem_range]
      have := ZMod.val_lt j
      exact (Nat.div_lt_iff_lt_mul hd0).mpr (lt_of_lt_of_eq this (Nat.mul_comm d M))
    · intro m hm
      rw [mem_range] at hm
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [val_natCast_lt (by nlinarith)]
      exact dvd_mul_right d m
    · intro j hj
      rw [mem_filter] at hj
      obtain ⟨c, hc⟩ := hj.2
      have : j.val / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd0
      simp only [this]
      rw [← hc, ZMod.natCast_zmod_val]
    · intro m hm
      rw [mem_range] at hm
      show (((d * m : ℕ) : ZMod (d * M))).val / d = m
      rw [val_natCast_lt (by nlinarith)]
      exact Nat.mul_div_cancel_left m hd0
    · intro j hj
      rw [mem_filter] at hj
      obtain ⟨c, hc⟩ := hj.2
      have : j.val / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd0
      simp only [this]
      rw [← hc, ZMod.natCast_zmod_val]
  rw [hre]
  -- each term is `z^m`
  set kv : ℕ := k.val with hkv
  set z : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * kv / M)) with hz
  have hterm : ∀ m ∈ range M,
      ZMod.stdAddChar (-(((d * m : ℕ) : ZMod (d * M)) * k)) = z ^ m := by
    intro m _
    have hk : k = (kv : ZMod (d * M)) := by rw [hkv, ZMod.natCast_zmod_val]
    have harg : -(((d * m : ℕ) : ZMod (d * M)) * k) = ((-((d * m * kv : ℕ) : ℤ) : ℤ) : ZMod (d * M)) := by
      rw [hk]; push_cast; ring
    rw [harg, ZMod.stdAddChar_coe, hz, ← Complex.exp_nat_mul]
    congr 1
    have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hdiv : M ∣ kv
  · obtain ⟨q, hq⟩ := hdiv
    have hz1 : z = 1 := by
      rw [hz, hq]
      have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
      have : -(2 * (Real.pi : ℂ) * Complex.I * ((M * q : ℕ) : ℂ) / M) = ((-(q : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [if_pos ⟨q, hq⟩, hz1]
    simp
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hz, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      apply hdiv
      have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
      have h2 : (kv : ℂ) = -(n : ℂ) * M := by
        have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have := hn
        field_simp at this
        apply mul_left_cancel₀ hpi
        linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * this
      have h3 : (kv : ℤ) = -n * M := by exact_mod_cast h2
      exact ⟨(-n).toNat, by
        have : (0 : ℤ) ≤ -n := by
          by_contra hneg
          have hneg' : -n < 0 := not_le.mp hneg
          have : (-n * (M : ℤ)) < 0 := mul_neg_of_neg_of_pos hneg' (by exact_mod_cast hM0)
          omega
        zify
        rw [Int.toNat_of_nonneg this, h3]
        ring⟩
    rw [if_neg (by rintro ⟨q, hq⟩; exact hdiv ⟨q, hq⟩)]
    have hzM : z ^ M = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
      have : (M : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I * kv / M) = ((-(kv : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzM]
    simp

/-- **Normalized subgroup states are exchanged**: `N^{-1/2} 𝓕 v_d = v_{N/d}`, where
`v_d = M^{-1/2} 1_{H_d}` (`|H_d| = M`) and `v_M = d^{-1/2} 1_{H_M}` (`|H_M| = d`), `N = d M`. -/
theorem fourier_subgroup_state (k : ZMod (d * M)) :
    (((Real.sqrt ((d * M : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
        ZMod.dft (fun x : ZMod (d * M) => ((1 / Real.sqrt M : ℝ) : ℂ) * ind d x) k =
      ((1 / Real.sqrt d : ℝ) : ℂ) * ind M k := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hlin : ZMod.dft (fun x : ZMod (d * M) => ((1 / Real.sqrt M : ℝ) : ℂ) * ind d x) =
      ((1 / Real.sqrt M : ℝ) : ℂ) • ZMod.dft (ind d : ZMod (d * M) → ℂ) := by
    rw [← map_smul]; rfl
  rw [hlin, Pi.smul_apply, dft_indicator]
  push_cast
  rw [Real.sqrt_mul hd0.le]
  by_cases h : M ∣ k.val
  · simp only [ind, h, if_true, smul_eq_mul, mul_one]
    have hsd' : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    have hsM' : (Real.sqrt M : ℂ) ≠ 0 := by exact_mod_cast hsM.ne'
    have hMc : (M : ℂ) = (Real.sqrt M : ℂ) * (Real.sqrt M : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hM0.le]; simp
    field_simp
    rw [hMc]
    push_cast
    ring
  · simp [ind, h]

end GppFiniteSubgroupFourier
