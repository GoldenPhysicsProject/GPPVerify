/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Flint (D3 seat). Routed task: Turbo to Flint, 2026-11-12 (Heart of the Cosmos via
PR #11 comment 6832868926; Daniel's direction). Item 3 of the routed task.

# The GNS construction for the Abel–Cesàro form (on-line / tempered sector)

The `ε → 0⁺` limit of the Abel–Cesàro form of `CesaroAbelState.lean`, restricted to
characters on the critical line (`Re α = 0`, i.e. `α = iγ` with `γ ∈ ℝ`), is the
diagonal form
  `⟨a, b⟩₀ = 2 · Σ_γ conj(a_γ) · b_γ`
on finitely supported frequency functions `a b : ι →₀ ℂ` (proved on `Fin n`
families in `abelForm_limit_self_nonneg_onLine`; the diagonal selection
`ᾱᵢ + αⱼ = 0` is `γᵢ = γⱼ` there). This file performs the GNS construction for
that limit form:

* `gnsForm` (**definition**): the limit form on `ι →₀ ℂ`, for an arbitrary
  frequency index type `ι`.
* `gnsForm_self` (**PROVED**): `gnsForm a a = 2 · Σ_{γ ∈ supp a} ‖a_γ‖²`, a
  nonnegative real.
* `gnsForm_self_eq_zero` (**PROVED**): the form is positive **definite**:
  `gnsForm a a = 0 ↔ a = 0`. Hence the GNS null space is `{0}`, the quotient by
  null vectors is the identity, and the whole content of the construction is
  the completion. (This is the tempered sector only: off-line characters are
  not in this algebra — see `CesaroAbelState.lean`'s located boundary.)
* `gnsRep` (**definition**): the GNS representation, the linear map of `ι →₀ ℂ`
  into the Hilbert space `𝕜²(ι) := lp (fun _ : ι => ℂ) 2`.
* `gnsForm_eq_two_mul_inner` (**PROVED**): `gnsForm a b = 2 · ⟪gnsRep a, gnsRep b⟫`:
  the abstract form is the inner product of the completion (the factor `2` is
  the `ω_ε(1) = 2` normalisation of `CesaroAbelState.lean`, carried explicitly).
* `gnsRep_dense_range` (**PROVED**): the image of `gnsRep` is dense in `𝕜²(ι)`:
  `gnsRep` exhibits `lp (fun _ : ι => ℂ) 2` as the completion of `ι →₀ ℂ` under
  `gnsForm`, i.e. its GNS Hilbert space.

Proof-repair note (2026-11-12, bench recovery): as first drafted, the
`gnsRep_dense_range` proof did not elaborate — applying
`Metric.tendsto_atTop.mp` to `Summable.hasSum` (a `HasSum`, i.e. a `Tendsto`
of Finset sums) hit a deterministic `whnf` timeout that masked the later
steps, and `Metric.dense_iff` in this Mathlib is the
`(ball x r ∩ s).Nonempty` form, not an `∃ y ∈ s, dist` form. The proof below
routes the tail estimate through `Filter.Tendsto.eventually` with
`Metric.ball_mem_nhds` and `Filter.eventually_atTop.mp`, keeps `v` intact
(`f := ⇑v`, `hf := v.2` — `obtain ⟨f, hf⟩ := v` would consume `v`), and uses
`classical` for the `γ ∈ F` decidability in the truncation. No statement was
changed.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import GppVerify.RiemannHypothesis.CesaroAbelState

namespace GppCesaroGNS

open Complex Filter Topology Finset ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace

variable {ι : Type*}

/-- The diagonal Cesàro–Gram form on finitely supported frequency functions:
`⟨a, b⟩₀ = 2 · Σ_γ conj(a_γ) · b_γ` (the sum is over `a.support`; terms with
`γ ∉ a.support` vanish). This is the `ε → 0⁺` limit of the Abel–Cesàro form on
on-line character sums. -/
noncomputable def gnsForm (a b : ι →₀ ℂ) : ℂ :=
  a.sum fun γ x => 2 * conj x * b γ

/-- **PROVED**: `gnsForm a a = 2 · Σ_{γ ∈ supp a} ‖a_γ‖²` (a nonnegative real). -/
theorem gnsForm_self (a : ι →₀ ℂ) :
    gnsForm a a = ((2 * ∑ γ ∈ a.support, ‖a γ‖ ^ 2 : ℝ) : ℂ) := by
  have hsum : gnsForm a a = ∑ γ ∈ a.support, 2 * conj (a γ) * a γ := rfl
  rw [hsum, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_assoc, Complex.conj_mul']
  push_cast
  ring

/-- **PROVED (definiteness)**: `gnsForm a a = 0 ↔ a = 0`. The GNS null space of
the on-line Cesàro–Gram form is trivial. -/
theorem gnsForm_self_eq_zero {a : ι →₀ ℂ} : gnsForm a a = 0 ↔ a = 0 := by
  rw [gnsForm_self]
  constructor
  · intro h
    have h2 : (2 : ℝ) * ∑ γ ∈ a.support, ‖a γ‖ ^ 2 = 0 :=
      Complex.ofReal_eq_zero.mp h
    have h3 : ∑ γ ∈ a.support, ‖a γ‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · norm_num at h4
      · exact h4
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun γ _ => sq_nonneg _)] at h3
    ext γ
    by_cases hγ : γ ∈ a.support
    · have := h3 γ hγ
      simp only [sq_eq_zero_iff, norm_eq_zero] at this
      rw [this]
      simp
    · simp [Finsupp.notMem_support_iff.mp hγ]
  · intro h
    rw [h]
    simp

/-- An element of `lp` from a finitely supported function. -/
theorem finsupp_memℓp (a : ι →₀ ℂ) : Memℓp (⇑a) 2 :=
  memℓp_gen (p := 2) (by
    have : (fun γ => ‖a γ‖ ^ (2 : ℝ≥0∞).toReal) = fun γ => ‖a γ‖ ^ 2 := by
      funext γ
      simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
    rw [this]
    exact summable_of_ne_finset_zero (s := a.support) (fun γ hγ => by
      rw [Finsupp.notMem_support_iff.mp hγ]
      simp))

/-- **The GNS representation**: finitely supported frequency functions embedded
in the Hilbert space `𝕜²(ι) = lp (fun _ : ι => ℂ) 2`. -/
noncomputable def gnsRep : (ι →₀ ℂ) →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun a := ⟨⇑a, finsupp_memℓp a⟩
  map_add' a b := by
    refine Subtype.ext (funext fun γ => ?_)
    show (a + b) γ = a γ + b γ
    exact Finsupp.add_apply a b γ
  map_smul' w a := by
    refine Subtype.ext (funext fun γ => ?_)
    show (w • a) γ = w * a γ
    exact Finsupp.smul_apply w a γ

/-- The inner product on `𝕜²(ι)` of two represented vectors is the diagonal sum. -/
theorem gnsRep_inner (a b : ι →₀ ℂ) :
    ⟪gnsRep a, gnsRep b⟫ = ∑' γ, conj (a γ) * b γ := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun γ => ?_
  simp [gnsRep, RCLike.inner_apply]
  exact mul_comm _ _

/-- **PROVED**: the abstract Cesàro–Gram form is (twice) the inner product of
the GNS completion: `gnsForm a b = 2 · ⟪gnsRep a, gnsRep b⟫`. -/
theorem gnsForm_eq_two_mul_inner (a b : ι →₀ ℂ) :
    gnsForm a b = 2 * ⟪gnsRep a, gnsRep b⟫ := by
  rw [gnsRep_inner]
  have htsum : ∑' γ, conj (a γ) * b γ = ∑ γ ∈ a.support, conj (a γ) * b γ :=
    tsum_eq_sum (fun γ hγ => by
      rw [Finsupp.notMem_support_iff.mp hγ]
      simp)
  rw [htsum]
  have hsum : gnsForm a b = ∑ γ ∈ a.support, 2 * conj (a γ) * b γ := rfl
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- The squared norm on `𝕜²(ι)` is the sum of the squared norms. -/
theorem norm_sq_eq_tsum (w : lp (fun _ : ι => ℂ) 2) :
    ‖w‖ ^ 2 = ∑' γ, ‖w γ‖ ^ 2 := by
  have hrw : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => Real.rpow_ofNat x 2
  have h := lp.norm_rpow_eq_tsum (p := 2) (by
    rw [ENNReal.toReal_ofNat]; norm_num) w
  rw [ENNReal.toReal_ofNat, hrw ‖w‖, tsum_congr (fun γ => hrw ‖w γ‖)] at h
  exact h

/-- **PROVED (density / completion)**: the GNS representation has dense range:
`lp (fun _ : ι => ℂ) 2` is the completion of `ι →₀ ℂ` under `gnsForm`. -/
theorem gnsRep_dense_range :
    Dense (Set.range (gnsRep : (ι →₀ ℂ) → lp (fun _ : ι => ℂ) 2)) := by
  classical
  rw [Metric.dense_iff]
  intro v ε hε
  set f : ι → ℂ := ⇑v with hf_def
  have hf : Memℓp f 2 := v.2
  have hsumm : Summable (fun γ => ‖f γ‖ ^ 2) := by
    have h := hf.summable (p := 2) (by simp)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using h
  have hT : Tendsto (fun s : Finset ι => ∑ γ ∈ s, ‖f γ‖ ^ 2) atTop
      (𝓝 (∑' γ, ‖f γ‖ ^ 2)) := hsumm.hasSum
  have hev : ∀ᶠ s : Finset ι in atTop, dist (∑ γ ∈ s, ‖f γ‖ ^ 2)
      (∑' γ, ‖f γ‖ ^ 2) < ε ^ 2 := by
    have hmem : Metric.ball (∑' γ, ‖f γ‖ ^ 2) (ε ^ 2)
        ∈ 𝓝 (∑' γ, ‖f γ‖ ^ 2) := Metric.ball_mem_nhds _ (by positivity)
    have h := hT.eventually hmem
    exact h.mono fun s hs => Metric.mem_ball.mp hs
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp hev
  specialize hF F le_rfl
  -- the tail of the total mass past `F` is small
  have hsum_le : ∑ γ ∈ F, ‖f γ‖ ^ 2 ≤ ∑' γ, ‖f γ‖ ^ 2 :=
    hsumm.sum_le_tsum F (fun γ _ => sq_nonneg _)
  have htail : (∑' γ, ‖f γ‖ ^ 2) - ∑ γ ∈ F, ‖f γ‖ ^ 2 < ε ^ 2 := by
    have h1 : dist (∑ γ ∈ F, ‖f γ‖ ^ 2) (∑' γ, ‖f γ‖ ^ 2)
        = (∑' γ, ‖f γ‖ ^ 2) - ∑ γ ∈ F, ‖f γ‖ ^ 2 := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsum_le), neg_sub]
    rwa [h1] at hF
  -- the truncation of `f` to `F`, as a finitely supported function
  set a : ι →₀ ℂ := ∑ γ ∈ F, Finsupp.single γ (f γ) with ha
  have ha_apply : ∀ γ, a γ = if γ ∈ F then f γ else 0 := by
    intro γ
    rw [ha, Finsupp.finsetSum_apply]
    by_cases hγ : γ ∈ F
    · rw [if_pos hγ]
      rw [Finset.sum_eq_single γ]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd hγ h
    · rw [if_neg hγ]
      refine Finset.sum_eq_zero fun b hbF => ?_
      by_cases hb : b = γ
      · have hbF' : b ∉ F := by rw [hb]; exact hγ
        exact absurd hbF hbF'
      · simp [hb]
  refine ⟨gnsRep a, ?_, ⟨a, rfl⟩⟩
  have hdiff : ∀ γ, (v - gnsRep a) γ = if γ ∈ F then 0 else f γ := by
    intro γ
    have h1 : (v - gnsRep a) γ = f γ - a γ := rfl
    rw [h1, ha_apply γ]
    by_cases hγ : γ ∈ F
    · rw [if_pos hγ, if_pos hγ, sub_self]
    · rw [if_neg hγ, if_neg hγ, sub_zero]
  -- the squared norm of the error is exactly the tail mass
  have htsum : ∑' γ, ‖(v - gnsRep a) γ‖ ^ 2
      = (∑' γ, ‖f γ‖ ^ 2) - ∑ γ ∈ F, ‖f γ‖ ^ 2 := by
    have hpt : ∀ γ, ‖(v - gnsRep a) γ‖ ^ 2
        = ‖f γ‖ ^ 2 - (if γ ∈ F then ‖f γ‖ ^ 2 else 0) := by
      intro γ
      rw [hdiff γ]
      by_cases hγ : γ ∈ F <;> simp [hγ]
    have hif : Summable (fun γ => if γ ∈ F then ‖f γ‖ ^ 2 else 0) :=
      summable_of_ne_finset_zero (s := F) (fun γ hγ => if_neg hγ)
    rw [tsum_congr hpt, hsumm.tsum_sub hif,
      tsum_eq_sum (s := F) (fun γ hγ => if_neg hγ)]
    congr 1
    exact Finset.sum_congr rfl fun γ hγ => if_pos hγ
  rw [Metric.mem_ball, dist_comm (gnsRep a) v, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) hε.le, norm_sq_eq_tsum, htsum]
  exact htail

#print axioms gnsForm_self
#print axioms gnsForm_self_eq_zero
#print axioms gnsForm_eq_two_mul_inner
#print axioms norm_sq_eq_tsum
#print axioms gnsRep_dense_range

end GppCesaroGNS
