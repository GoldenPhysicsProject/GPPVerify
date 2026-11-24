/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.IdeleQ
import GppVerify.RiemannHypothesis.AdelicPoissonCore


/-!
# Discreteness of `ℚ` in the adeles (GP1)

On the concrete adele carrier `AQ = ℝ × 𝔸_f` (Turbo's ruling, GPP-bridge PR #11,
6730857794; the identification with Mathlib's `AdeleRing ℤ ℚ` is the separate obligation
GP0), the principal adeles `q ↦ (q, (q)_v)` form a discrete subgroup
(`principal_discrete`). The open box `(-1/2, 1/2) × ∏ ℤ_v` meets them only in `0`
(`principal_mem_box`): a rational integral at every prime is an integer
(`AdelicPoissonCore`), and an integer of absolute value below `1/2` is `0`.

Cocompactness (GP2), the fundamental domain (GP3) and the covolume (GP4) remain.

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §4), audited PASS by Turbo.
-/

open IsDedekindDomain GppIdeleQ

namespace GlobalTate.Poisson

/-- The concrete adele carrier `ℝ × 𝔸_f` (Turbo, PR #11 6730857794; GP0 relates it to
Mathlib's `AdeleRing ℤ ℚ`). -/
abbrev AQ := ℝ × Af

/-- The principal adeles `q ↦ (q, (q)_v)`. -/
noncomputable def principal : ℚ →+* AQ := RingHom.prod (algebraMap ℚ ℝ) (algebraMap ℚ Af)

/-- The finite adeles that are integral at every place. -/
def intBox : Set Af := {f | ∀ v, f v ∈ v.adicCompletionIntegers ℚ}

theorem isOpen_intBox : IsOpen intBox :=
  RestrictedProduct.isOpen_forall_mem fun v => isOpen_integers v

/-- The open box `(-1/2, 1/2) × ∏ ℤ_v`. -/
def box : Set AQ := Set.Ioo (-1/2 : ℝ) (1/2) ×ˢ intBox

theorem isOpen_box : IsOpen box := isOpen_Ioo.prod isOpen_intBox

/-- **GP1 (core).** The box meets the principal adeles only in `0`. -/
theorem principal_mem_box {q : ℚ} (hq : principal q ∈ box) : q = 0 := by
  obtain ⟨hinf, hf⟩ := hq
  apply eq_zero_of_integral_of_abs_lt_one
  · intro p hp
    obtain ⟨v, hv⟩ := exists_pr_eq hp
    have h1 := (mem_integers_iff v _).1 (hf v)
    have h2 : (principal q).2 v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl
    rw [h2, lnorm_algebraMap, Padic.eq_padicNorm] at h1
    subst hv
    exact_mod_cast h1
  · have h1 : (-1 / 2 : ℝ) < q := hinf.1
    have h2 : (q : ℝ) < 1 / 2 := hinf.2
    have : |(q : ℝ)| < 1 / 2 := abs_lt.2 ⟨by linarith, h2⟩
    have : |(q : ℝ)| < 1 := by linarith
    exact_mod_cast this

/-- The principal adeles as an additive subgroup of `ℝ × 𝔸_f`. -/
noncomputable def principalSubgroup : AddSubgroup AQ := principal.range.toAddSubgroup

theorem zero_mem_box : (0 : AQ) ∈ box :=
  ⟨⟨by norm_num, by norm_num⟩, fun v => (v.adicCompletionIntegers ℚ).zero_mem⟩

/-- **GP1.** `ℚ` is discrete in the adeles `ℝ × 𝔸_f`. -/
theorem principal_discrete : DiscreteTopology principalSubgroup := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  refine isOpen_induced_iff.2 ⟨box, isOpen_box, ?_⟩
  ext ⟨x, hx⟩
  obtain ⟨q, rfl⟩ := hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    have := principal_mem_box h
    subst this
    ext <;> simp
  · intro h
    have : principal q = 0 := congrArg Subtype.val h
    simpa [this] using zero_mem_box

end GlobalTate.Poisson
