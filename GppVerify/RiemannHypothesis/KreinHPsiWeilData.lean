/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Follow-up to KreinHPsi (heart/hpsi 65358d6).

# `WeilData` is inhabited, and `HPsiEquiv` is a theorem

Port of GPPDiscovery5 `lean/s-eq-delta/KreinHPsiWeilData.lean` (theorem section identical).

Labels:
* `tau_linearIndependent` (distinct triangle translates are linearly independent): PROVED.
* `exists_linear_on_li`, `exists_bilinear_on_li` (prescribe values on a linearly independent
  family): PROVED.
* `exists_translate_data` (any kernel / cosh / sinh values are realised on translates): PROVED.
  Kernel-blind: inhabiting `WeilData` carries no positivity information.
* `weilData_nonempty`, `weilData`: PROVED / CONSTRUCTED from `Kψ` (pole, primes, Γ) and the
  cosh / sinh values. No zero of ζ is an input. `B` is fixed on `F_ψ` and arbitrary on a
  complement; only its `F_ψ` part enters `HPsiWindows`.
* `hPsiWindows_iff`, `hPsiEquiv`: PROVED. The named premise `HPsiEquiv` is discharged, for
  every `WeilData`.
* `exists_weilData_iff`: PROVED (the equivalence is non-vacuous).
* `HPsi` (= H_ψ): OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinHPsi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace GppKreinHPsi

open GppKreinBridge

/-! ## 1. The triangle translates are linearly independent (PROVED) -/

theorem triPsi_eq_zero_of_one_le {t : ℝ} (h : 1 ≤ |t|) : triPsi t = 0 := by
  unfold triPsi; exact max_eq_left (by linarith)

theorem triPsi_of_abs_le {t : ℝ} (h : |t| ≤ 1) : triPsi t = 1 - |t| := by
  unfold triPsi; exact max_eq_right (by linarith)

/-- Distinct translates of `ψ` are linearly independent in `ℝ → ℝ`: evaluate just left of the
right end `a + 1` of the right-most translate, where every other translate already vanishes. -/
theorem tau_linearIndependent : LinearIndependent ℝ tau := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on_max with
  | empty => intro g _ i hi; simp at hi
  | insert a s has ih =>
    intro g hg
    obtain ⟨δ, hδ0, hδ1, hδs⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ x ∈ s, x ≤ a - δ := by
      rcases s.eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, le_rfl, by simp [h]⟩
      · refine ⟨min 1 (a - s.max' h), lt_min one_pos (sub_pos.2 (has _ (s.max'_mem h))),
          min_le_left _ _, fun x hx => ?_⟩
        have h1 := s.le_max' x hx
        have h2 := min_le_right 1 (a - s.max' h)
        linarith
    have has' : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [Finset.sum_insert has'] at hg
    have hev := congrFun hg (a + 1 - δ)
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hev
    have h0 : ∀ x ∈ s, tau x (a + 1 - δ) = 0 := by
      intro x hx
      apply triPsi_eq_zero_of_one_le
      have := hδs x hx
      rw [abs_of_nonneg (by linarith)]; linarith
    rw [Finset.sum_eq_zero (fun x hx => by rw [h0 x hx, mul_zero])] at hev
    have hta : tau a (a + 1 - δ) = δ := by
      show triPsi (a + 1 - δ - a) = δ
      rw [triPsi_of_abs_le] <;> rw [abs_of_nonneg (by linarith)] <;> linarith
    rw [hta, add_zero] at hev
    have hga : g a = 0 := (mul_eq_zero.1 hev).resolve_right hδ0.ne'
    rw [hga, zero_smul, zero_add] at hg
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hga
    · exact ih g hg i hi

/-! ## 2. Prescribing linear and bilinear maps on a linearly independent family (PROVED) -/

section Prescribe

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {ι : Type*}

/-- A linear map can take any prescribed values on a linearly independent family. -/
theorem exists_linear_on_li {v : ι → V} (hv : LinearIndependent ℝ v) (f : ι → W) :
    ∃ ℓ : V →ₗ[ℝ] W, ∀ i, ℓ (v i) = f i := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr ℝ f)
  refine ⟨g, fun i => ?_⟩
  have h := LinearMap.congr_fun hg (Module.Basis.span hv i)
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, Submodule.subtype_apply,
    Module.Basis.coe_span_apply] at h
  exact h

/-- A bilinear form can take any prescribed values on pairs from a linearly independent
family. -/
theorem exists_bilinear_on_li {v : ι → V} (hv : LinearIndependent ℝ v) (F : ι → ι → ℝ) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, ∀ i j, B (v i) (v j) = F i j := by
  choose row hrow using fun i => exists_linear_on_li hv (F i)
  obtain ⟨B, hB⟩ := exists_linear_on_li hv row
  exact ⟨B, fun i j => by rw [hB, hrow]⟩

end Prescribe

/-! ## 3. `WeilData` is inhabited (PROVED; the witness is CONSTRUCTED from `Kψ` alone) -/

/-- Kernel-blind form of the non-vacuity statement: for **any** kernel `K` and any
`ℓ_c, ℓ_s` values on translates there is a bilinear `B` and functionals with those values.
So inhabiting `WeilData` costs nothing beyond `tau_linearIndependent`, and carries no
positivity information. -/
theorem exists_translate_data (K fc fs : ℝ → ℝ) :
    ∃ (B : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) →ₗ[ℝ] ℝ) (lc ls : (ℝ → ℝ) →ₗ[ℝ] ℝ),
      (∀ x y, B (tau x) (tau y) = K (x - y)) ∧ (∀ x, lc (tau x) = fc x) ∧
        ∀ x, ls (tau x) = fs x := by
  obtain ⟨B, hB⟩ := exists_bilinear_on_li tau_linearIndependent (fun x y => K (x - y))
  obtain ⟨lc, hlc⟩ := exists_linear_on_li tau_linearIndependent fc
  obtain ⟨ls, hls⟩ := exists_linear_on_li tau_linearIndependent fs
  exact ⟨B, lc, ls, hB, hlc, hls⟩

/-- **`WeilData` is non-empty.** The data are `Kψ` (pole, primes, Γ) and the cosh / sinh
values; no zero of ζ is an input. -/
theorem weilData_nonempty : Nonempty WeilData := by
  obtain ⟨B, lc, ls, hB, hlc, hls⟩ := exists_translate_data Kpsi
    (fun x => bigPsiI2 * Real.cosh (x / 2)) (fun x => bigPsiI2 * Real.sinh (x / 2))
  exact ⟨⟨B, lc, ls, hB, hlc, hls⟩⟩

/-- A chosen witness (CONSTRUCTED). -/
noncomputable def weilData : WeilData := Classical.choice weilData_nonempty

/-! ## 4. `HPsiEquiv` (PROVED, no premise) -/

theorem bigPsiI2_pos : 0 < bigPsiI2 := by
  unfold bigPsiI2
  have : 0 < Real.sinh (1 / 4) := Real.sinh_pos_iff.2 (by norm_num)
  positivity

/-- Every element of `F_ψ` is a finite combination `Σ cᵢ τ_{xᵢ}` indexed by `Fin n`. -/
theorem exists_fin_of_mem_Fpsi {v : ℝ → ℝ} (hv : v ∈ Fpsi) :
    ∃ (n : ℕ) (x c : Fin n → ℝ), v = ∑ i, c i • tau (x i) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, rfl⟩ := hv
    exact ⟨1, fun _ => x, fun _ => 1, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨n, x, c, rfl⟩ := hv
    obtain ⟨m, y, d, rfl⟩ := hw
    exact ⟨n + m, Fin.append x y, Fin.append c d, by simp [Fin.sum_univ_add]⟩
  | smul a v _ hv =>
    obtain ⟨n, x, c, rfl⟩ := hv
    exact ⟨n, x, fun i => a * c i, by simp [Finset.smul_sum, smul_smul]⟩

theorem sum_mem_Fpsi {n : ℕ} (x c : Fin n → ℝ) : (∑ i, c i • tau (x i)) ∈ Fpsi :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x i, rfl⟩)

theorem B_sum (W : WeilData) {n : ℕ} (x c : Fin n → ℝ) :
    W.B (∑ i, c i • tau (x i)) (∑ i, c i • tau (x i)) = kform Kpsi x c := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, W.hK,
    smul_eq_mul, kform, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem lc_sum (W : WeilData) {n : ℕ} (x c : Fin n → ℝ) :
    W.lc (∑ i, c i • tau (x i)) = bigPsiI2 * ∑ i, c i * Real.cosh (x i / 2) := by
  simp only [map_sum, map_smul, W.hlc, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The windowed form equals the Toeplitz form, for every `WeilData`** (PROVED).
`⇐`: a finite family fits in one window (`fit_translates`). `⇒`: an element of `F_ψ` is a
finite combination, `B` and `ℓ_c` are fixed on it by `hK`, `hlc`, and `Ψ(i/2) ≠ 0`. -/
theorem hPsiWindows_iff (W : WeilData) : HPsiWindows W ↔ HPsi := by
  constructor
  · intro H n x c hc
    obtain ⟨L, hL⟩ := fit_translates triPsi 1 (fun t ht => triPsi_eq_zero_of_one_le ht.le) n x
    have hvS : (∑ i, c i • tau (x i)) ∈ Spsi L :=
      Submodule.mem_inf.2 ⟨sum_mem_Fpsi x c,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hL i)⟩
    have hlc : W.lc (∑ i, c i • tau (x i)) = 0 := by rw [lc_sum, hc, mul_zero]
    have h := H L _ hvS hlc
    simp only at h
    rw [hlc, B_sum] at h
    linarith
  · intro H L v hv hlc
    simp only at hlc ⊢
    obtain ⟨n, x, c, rfl⟩ := exists_fin_of_mem_Fpsi (Submodule.mem_inf.1 hv).1
    rw [lc_sum] at hlc
    have hc : ∑ i, c i * Real.cosh (x i / 2) = 0 :=
      (mul_eq_zero.1 hlc).resolve_left bigPsiI2_pos.ne'
    have h := H n x c hc
    rw [lc_sum, hc, mul_zero, B_sum]
    linarith

/-- **`HPsiEquiv` holds** (PROVED). It is no longer a premise. -/
theorem hPsiEquiv : HPsiEquiv := hPsiWindows_iff

/-- **Non-vacuous form**: there is Weil data, and for it the windowed form is exactly `H_ψ`.
`H_ψ` itself remains OPEN. -/
theorem exists_weilData_iff : ∃ W : WeilData, (HPsiWindows W ↔ HPsi) :=
  ⟨weilData, hPsiWindows_iff weilData⟩

end GppKreinHPsi
