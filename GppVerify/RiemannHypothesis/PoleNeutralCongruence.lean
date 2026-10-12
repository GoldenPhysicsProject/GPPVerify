import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Pole-neutral congruence: `Q ⪰ 0 ⇔ A ⪰ 0` on the neutral subspace

Source: Codex, directive C3(i) answer (GPP-bridge PR #11 comment 6120839998, 2026-10-12),
re-deriving §§1–2 of GPPDiscovery2 `research/2026-09-30_pole_calibrated_neutral_loewner_reduction.md`.
This completes the finite algebra behind `GppRadicalPoleThreshold` (#293).

Let `A` be symmetric and invertible, and let `c` and `s` be vectors with the pole calibrations
`⟨c, A⁻¹c⟩ = −2` and `⟨s, A⁻¹s⟩ = 2`, and the parity condition `⟨c, A⁻¹s⟩ = 0`. That condition is
what "`c` even, `s` odd, `A` parity-preserving" supplies. Put `Q = A + ½ccᵀ − ½ssᵀ` and
`𝒩 = {x : ⟨c,x⟩ = ⟨s,x⟩ = 0}`.

* `congruence`: every `x` decomposes as `x = y + α A⁻¹c + β A⁻¹s` with `y ∈ 𝒩`, where
  `α = −⟨c,x⟩/2` and `β = ⟨s,x⟩/2`, and **`Q[x] = A[y]`**. The `α` and `β` directions are exact null
  directions of `Q`.
* `psd_iff`: `Q` is positive semidefinite **iff** `A` is positive semidefinite on `𝒩`.

Codex's caveat, kept: this is the **finite-dimensional** statement. The continuum version also needs
the boundary vectors `A⁻¹c`, `A⁻¹s` in the form domain plus core/density hypotheses, so the global
semilocal equivalence stays **OPEN** until those are checked. The calibrations alone are not enough:
inverse, parity and decomposition are all used. No RH claim.
-/

namespace GppPoleNeutralCongruence

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form `x ↦ xᵀ M x`. -/
def qf (M : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- The pole-completed form `Q = A + ½ccᵀ − ½ssᵀ`, as a quadratic form. -/
noncomputable def Qf (A : Matrix n n ℝ) (c s x : n → ℝ) : ℝ :=
  qf A x + (1 / 2) * (c ⬝ᵥ x) ^ 2 - (1 / 2) * (s ⬝ᵥ x) ^ 2

omit [DecidableEq n] in
lemma symm_dot {M : Matrix n n ℝ} (hM : Mᵀ = M) (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

omit [DecidableEq n] in
lemma qf_add {M : Matrix n n ℝ} (hM : Mᵀ = M) (x y : n → ℝ) :
    qf M (x + y) = qf M x + 2 * (x ⬝ᵥ (M *ᵥ y)) + qf M y := by
  unfold qf
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, symm_dot hM y x]
  ring

/-- **Congruence.** `Q[x] = A[y]` for the neutral component `y` of `x`. -/
theorem congruence (A : Matrix n n ℝ) (hA : IsUnit A.det) (hsym : Aᵀ = A) (c s : n → ℝ)
    (hc : c ⬝ᵥ (A⁻¹ *ᵥ c) = -2) (hs : s ⬝ᵥ (A⁻¹ *ᵥ s) = 2) (hcs : c ⬝ᵥ (A⁻¹ *ᵥ s) = 0)
    (x : n → ℝ) :
    let α := -(c ⬝ᵥ x) / 2
    let β := (s ⬝ᵥ x) / 2
    let y := x - α • (A⁻¹ *ᵥ c) - β • (A⁻¹ *ᵥ s)
    c ⬝ᵥ y = 0 ∧ s ⬝ᵥ y = 0 ∧ Qf A c s x = qf A y := by
  intro α β y
  have hAw : A *ᵥ (A⁻¹ *ᵥ c) = c := by rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  have hAv : A *ᵥ (A⁻¹ *ᵥ s) = s := by rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  -- `s · w = 0` by symmetry of `A⁻¹`
  have hinvsym : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hsym]
  have hsw : s ⬝ᵥ (A⁻¹ *ᵥ c) = 0 := by rw [symm_dot hinvsym, hcs]
  have hcy : c ⬝ᵥ y = 0 := by
    simp only [y, dotProduct_sub, dotProduct_smul, smul_eq_mul, hc, hcs, α, β]
    ring
  have hsy : s ⬝ᵥ y = 0 := by
    simp only [y, dotProduct_sub, dotProduct_smul, smul_eq_mul, hs, hsw, α, β]
    ring
  refine ⟨hcy, hsy, ?_⟩
  -- `x = y + (α w + β v)`
  have hx : x = y + (α • (A⁻¹ *ᵥ c) + β • (A⁻¹ *ᵥ s)) := by simp only [y]; abel
  have hyA : y ⬝ᵥ (A *ᵥ (α • (A⁻¹ *ᵥ c) + β • (A⁻¹ *ᵥ s))) = 0 := by
    rw [mulVec_add, mulVec_smul, mulVec_smul, hAw, hAv, dotProduct_add, dotProduct_smul,
      dotProduct_smul, dotProduct_comm y c, dotProduct_comm y s, hcy, hsy]
    simp
  have huA : qf A (α • (A⁻¹ *ᵥ c) + β • (A⁻¹ *ᵥ s)) = -2 * α ^ 2 + 2 * β ^ 2 := by
    unfold qf
    rw [mulVec_add, mulVec_smul, mulVec_smul, hAw, hAv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (A⁻¹ *ᵥ c) c, dotProduct_comm (A⁻¹ *ᵥ c) s, dotProduct_comm (A⁻¹ *ᵥ s) c,
      dotProduct_comm (A⁻¹ *ᵥ s) s, hc, hs, hcs, hsw]
    ring
  have hcx : c ⬝ᵥ x = -2 * α := by simp only [α]; ring
  have hsx : s ⬝ᵥ x = 2 * β := by simp only [β]; ring
  unfold Qf
  rw [hcx, hsx, hx, qf_add hsym, hyA, huA]
  ring

/-- **`Q ⪰ 0` iff `A ⪰ 0` on the neutral subspace.** -/
theorem psd_iff (A : Matrix n n ℝ) (hA : IsUnit A.det) (hsym : Aᵀ = A) (c s : n → ℝ)
    (hc : c ⬝ᵥ (A⁻¹ *ᵥ c) = -2) (hs : s ⬝ᵥ (A⁻¹ *ᵥ s) = 2) (hcs : c ⬝ᵥ (A⁻¹ *ᵥ s) = 0) :
    (∀ x, 0 ≤ Qf A c s x) ↔ (∀ y, c ⬝ᵥ y = 0 → s ⬝ᵥ y = 0 → 0 ≤ qf A y) := by
  constructor
  · intro hQ y hcy hsy
    have := hQ y
    unfold Qf at this
    rw [hcy, hsy] at this
    simpa using this
  · intro hN x
    obtain ⟨hcy, hsy, heq⟩ := congruence A hA hsym c s hc hs hcs x
    rw [heq]
    exact hN _ hcy hsy

end GppPoleNeutralCongruence
