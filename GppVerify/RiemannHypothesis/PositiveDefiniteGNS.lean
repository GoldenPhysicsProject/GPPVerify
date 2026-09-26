import GppVerify.RiemannHypothesis.FiniteGNS
import GppVerify.RiemannHypothesis.HaarPositivityWeil
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# GNS for a positive-definite function on a group

`HaarPositivityWeil.lean` parked `open_gns_from_positive_type`: a positive-definite function
`P` on a group `G` generates a Hilbert space `H`, a unitary representation `π` of `G` on it and
a cyclic vector `ξ` with `P g = ⟪ξ, π g ξ⟫`. This module proves it, for an arbitrary group —
no finiteness, no topology, no measure.

## Why it sat as a stub

The gap was labelled "the bridge from a positive-definite function to a positive linear
functional on a C⋆-algebra is missing — no C⋆-norm on `MonoidAlgebra`" (2026-09-02), and
`FiniteGNS.lean` declined to build the Hilbert space on the grounds that doing so would rebuild
what Mathlib has one level up. Both statements are accurate about the C⋆ route and neither is
needed: the construction for a *group* never touches a C⋆-algebra. It is Kolmogorov's: put the
form `⟪δ_x, δ_y⟫ = P (x⁻¹ y)` on the finitely supported functions `G →₀ ℂ`, hand it to
`PreInnerProductSpace.Core` (which accepts a semidefinite form), and complete. The C⋆-norm is
what one needs to get a representation of the *group C⋆-algebra*; the unitary representation of
the group itself, which is what the stub states, comes for free because left translation
preserves the form. This is the same template Mathlib's own `PositiveLinearMap.PreGNS` /
`.GNS` uses, fed with a different form.

## Main declarations

* `PreGNS P` — `G →₀ ℂ` with the semi-inner product induced by `P`.
* `GNS P` — its completion: a complex Hilbert space.
* `vec P g` — the image of `δ_g`; `inner_vec : ⟪vec g, vec h⟫ = P (g⁻¹ * h)`.
* `dense_span_vec` — the vectors `vec g` span a dense subspace.
* `rep P g` — the unitary `GNS P ≃ₗᵢ[ℂ] GNS P` induced by left translation, with
  `rep_vec`, `rep_mul`, `rep_one`.
* `gns_from_positive_definite` — the packaged statement.
* `gns_from_positive_type` — the same for `GppHaarPositivityWeil.PositiveType` on `ℝ`.

## What this does not give

It does not give Bochner's theorem (a continuous positive-definite function on `ℝ` is the
Fourier transform of a finite positive measure), which is the analytic statement the Weil /
Wightman threads actually want and which needs spectral theory for the one-parameter group
`rep`. Nor does it give continuity of `rep` in `g` — that needs continuity of `P` and a topology
on `G`, and is not asked for here.
-/

namespace GppPositiveDefiniteGNS

open GppFiniteGNS
open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {G : Type*} [Group G] {P : G → ℂ}

/-! ## The semi-inner product on `G →₀ ℂ` -/

/-- The form `⟪f, h⟫ = ∑_{x,y} conj (f x) * h y * P (x⁻¹ * y)` on finitely supported
functions. Conjugate-linear in the first argument, as Mathlib's inner products are. -/
noncomputable def form (P : G → ℂ) (f h : G →₀ ℂ) : ℂ :=
  f.sum fun x a => h.sum fun y b => (starRingEnd ℂ) a * b * P (x⁻¹ * y)

lemma form_eq_sum (P : G → ℂ) (f h : G →₀ ℂ) :
    form P f h = ∑ x ∈ f.support, ∑ y ∈ h.support,
      (starRingEnd ℂ) (f x) * h y * P (x⁻¹ * y) := rfl

/-- The quadratic form of a positive-definite `P` over any finite set of points is a
nonnegative real. `PositiveDefinite` quantifies over `Fin n`-indexed families; this is the
same statement indexed by a `Finset`. -/
theorem PositiveDefinite.finset_nonneg (hP : PositiveDefinite P) (s : Finset G) (c : G → ℂ) :
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, (starRingEnd ℂ) (c x) * c y * P (x⁻¹ * y) := by
  set e := s.equivFin
  have h := hP s.card (fun i => (e.symm i : G)) (fun i => c (e.symm i))
  rw [Finset.sum_comm] at h
  have key : ∀ F : G → ℂ, ∑ x ∈ s, F x = ∑ i : Fin s.card, F (e.symm i) := fun F => by
    rw [← Finset.sum_coe_sort s F]
    exact (e.symm.sum_comp (fun x : s => F x)).symm
  rw [key]
  simp_rw [key]
  exact h

lemma form_self_nonneg (hP : PositiveDefinite P) (f : G →₀ ℂ) : 0 ≤ form P f f :=
  PositiveDefinite.finset_nonneg hP f.support f

lemma conj_form (hP : PositiveDefinite P) (f h : G →₀ ℂ) :
    (starRingEnd ℂ) (form P h f) = form P f h := by
  rw [form_eq_sum, form_eq_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, ← hP.conj_symm, mul_inv_rev, inv_inv]
  ring

lemma form_add_left (P : G → ℂ) (f₁ f₂ h : G →₀ ℂ) :
    form P (f₁ + f₂) h = form P f₁ h + form P f₂ h := by
  unfold form
  refine Finsupp.sum_add_index' (fun x => by simp) (fun x a b => ?_)
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [map_add]; ring

lemma form_smul_left (P : G → ℂ) (r : ℂ) (f h : G →₀ ℂ) :
    form P (r • f) h = (starRingEnd ℂ) r * form P f h := by
  unfold form
  rw [Finsupp.sum_smul_index' (fun x => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [smul_eq_mul, map_mul]; ring

lemma form_single_single (P : G → ℂ) (g h : G) :
    form P (Finsupp.single g 1) (Finsupp.single h 1) = P (g⁻¹ * h) := by
  simp [form]

/-! ## The pre-Hilbert space and its completion -/

set_option linter.unusedVariables false in
/-- `G →₀ ℂ`, to carry the semi-inner product induced by `P`. The hypothesis is an argument so
that the instances below can use it. -/
@[nolint unusedArguments]
def PreGNS (hP : PositiveDefinite P) := G →₀ ℂ

variable (hP : PositiveDefinite P)

noncomputable instance : AddCommGroup (PreGNS hP) := inferInstanceAs (AddCommGroup (G →₀ ℂ))
noncomputable instance : Module ℂ (PreGNS hP) := inferInstanceAs (Module ℂ (G →₀ ℂ))

/-- The identity, `G →₀ ℂ ≃ₗ PreGNS hP`. -/
noncomputable def toPreGNS : (G →₀ ℂ) ≃ₗ[ℂ] PreGNS hP := LinearEquiv.refl ℂ _

/-- `PositiveDefinite` is exactly what `PreInnerProductSpace.Core` asks of a form. -/
noncomputable abbrev preCore : PreInnerProductSpace.Core ℂ (PreGNS hP) where
  inner f h := form P f h
  conj_inner_symm f h := conj_form hP f h
  re_inner_nonneg f := (RCLike.nonneg_iff.mp (form_self_nonneg hP f)).1
  add_left f₁ f₂ h := form_add_left P f₁ f₂ h
  smul_left f h r := form_smul_left P r f h

noncomputable instance : SeminormedAddCommGroup (PreGNS hP) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preCore hP)
noncomputable instance : InnerProductSpace ℂ (PreGNS hP) :=
  InnerProductSpace.ofCore (preCore hP)

lemma preGNS_inner_def (f h : PreGNS hP) : ⟪f, h⟫_ℂ = form P f h := rfl

/-- **The GNS Hilbert space** of a positive-definite function. -/
abbrev GNS := Completion (PreGNS hP)

/-- The vector `δ_g`. -/
noncomputable def vec (g : G) : GNS hP := ((toPreGNS hP (Finsupp.single g 1) : PreGNS hP))

/-- **The Gram matrix of the vectors `δ_g` is `P`.** -/
theorem inner_vec (g h : G) : ⟪vec hP g, vec hP h⟫_ℂ = P (g⁻¹ * h) := by
  rw [vec, vec, Completion.inner_coe, preGNS_inner_def]
  exact form_single_single P g h

/-- **The vectors `δ_g` span a dense subspace.** They span `PreGNS` itself, and `PreGNS` is
dense in its completion. -/
theorem dense_span_vec :
    (Submodule.span ℂ (Set.range (vec hP))).topologicalClosure = ⊤ := by
  let ι : PreGNS hP →ₗ[ℂ] GNS hP := (Completion.toComplL : PreGNS hP →L[ℂ] GNS hP)
  have hr : Set.range (vec hP) = ι '' Set.range (fun g : G => toPreGNS hP (Finsupp.single g 1)) := by
    rw [← Set.range_comp]; rfl
  have htop : Submodule.span ℂ (Set.range (fun g : G => toPreGNS hP (Finsupp.single g 1))) = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    induction f using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f₁ f₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | single g a =>
      have : (Finsupp.single g a : PreGNS hP) = a • toPreGNS hP (Finsupp.single g 1) := by
        exact (Finsupp.smul_single_one g a).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  rw [hr, Submodule.span_image, htop, Submodule.map_top,
    ← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range]
  exact Completion.denseRange_coe

/-! ## The unitary representation -/

/-- **Left translation preserves the form.** This is where the group structure is used:
`(g x)⁻¹ (g y) = x⁻¹ y`. -/
lemma form_translate (P : G → ℂ) (g : G) (f h : G →₀ ℂ) :
    form P (Finsupp.equivMapDomain (Equiv.mulLeft g) f)
      (Finsupp.equivMapDomain (Equiv.mulLeft g) h) = form P f h := by
  unfold form
  rw [Finsupp.sum_equivMapDomain]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_equivMapDomain]
  refine Finsupp.sum_congr fun y _ => ?_
  simp [mul_assoc]

/-- Left translation by `g` on the pre-Hilbert space, as a linear isometry equivalence. -/
noncomputable def translate (g : G) : PreGNS hP ≃ₗᵢ[ℂ] PreGNS hP where
  toLinearEquiv := Finsupp.domLCongr (Equiv.mulLeft g)
  norm_map' f := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    congr 2
    exact form_translate P g f f

lemma translate_apply (g : G) (f : PreGNS hP) :
    translate hP g f = (Finsupp.equivMapDomain (Equiv.mulLeft g) (f : G →₀ ℂ) : PreGNS hP) :=
  rfl

lemma equivMapDomain_mulLeft_mul (g h : G) (F : G →₀ ℂ) :
    Finsupp.equivMapDomain (Equiv.mulLeft (g * h)) F
      = Finsupp.equivMapDomain (Equiv.mulLeft g) (Finsupp.equivMapDomain (Equiv.mulLeft h) F) := by
  rw [← Finsupp.equivMapDomain_trans]
  congr 1
  ext x; simp

/-- The translation, extended to the completion as a continuous linear map. -/
noncomputable def repL (g : G) : GNS hP →L[ℂ] GNS hP :=
  ((translate hP g).toContinuousLinearEquiv : PreGNS hP →L[ℂ] PreGNS hP).completion

lemma repL_coe (g : G) (f : PreGNS hP) : repL hP g f = (translate hP g f : GNS hP) :=
  ContinuousLinearMap.completion_apply_coe _ f

lemma repL_mul_apply (g h : G) (v : GNS hP) : repL hP (g * h) v = repL hP g (repL hP h v) := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    rw [repL_coe, repL_coe, repL_coe]
    congr 1
    change Finsupp.equivMapDomain (Equiv.mulLeft (g * h)) (f : G →₀ ℂ)
      = Finsupp.equivMapDomain (Equiv.mulLeft g)
          (Finsupp.equivMapDomain (Equiv.mulLeft h) (f : G →₀ ℂ))
    exact equivMapDomain_mulLeft_mul g h f

lemma repL_one_apply (v : GNS hP) : repL hP 1 v = v := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    rw [repL_coe]
    congr 1
    simp only [translate_apply]
    have : Equiv.mulLeft (1 : G) = Equiv.refl G := by ext x; simp
    rw [this]
    exact Finsupp.equivMapDomain_refl (f : G →₀ ℂ)

lemma norm_repL (g : G) (v : GNS hP) : ‖repL hP g v‖ = ‖v‖ := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f => rw [repL_coe, Completion.norm_coe, Completion.norm_coe, LinearIsometryEquiv.norm_map]

/-- **The unitary operator `π g`** on the GNS Hilbert space. -/
noncomputable def rep (g : G) : GNS hP ≃ₗᵢ[ℂ] GNS hP where
  toFun := repL hP g
  invFun := repL hP g⁻¹
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv v := by rw [← repL_mul_apply, inv_mul_cancel, repL_one_apply]
  right_inv v := by rw [← repL_mul_apply, mul_inv_cancel, repL_one_apply]
  norm_map' := norm_repL hP g

lemma rep_apply (g : G) (v : GNS hP) : rep hP g v = repL hP g v := rfl

/-- `π g δ_h = δ_{g h}`. -/
theorem rep_vec (g h : G) : rep hP g (vec hP h) = vec hP (g * h) := by
  rw [rep_apply, vec, repL_coe, vec]
  congr 1
  change Finsupp.equivMapDomain (Equiv.mulLeft g) (Finsupp.single h (1 : ℂ))
    = Finsupp.single (g * h) 1
  rw [Finsupp.equivMapDomain_single]
  rfl

theorem rep_mul (g h : G) : rep hP (g * h) = rep hP g * rep hP h := by
  ext v
  exact repL_mul_apply hP g h v

theorem rep_one : rep hP (1 : G) = 1 := by
  ext v
  exact repL_one_apply hP v

/-- **`π` as a group homomorphism into the unitary group of the GNS space.** -/
noncomputable def repHom : G →* (GNS hP ≃ₗᵢ[ℂ] GNS hP) where
  toFun := rep hP
  map_one' := rep_one hP
  map_mul' := rep_mul hP

/-- **`P` is a matrix coefficient of `π`:** `P g = ⟪δ₁, π g δ₁⟫`. -/
theorem apply_eq_inner_rep (g : G) : P g = ⟪vec hP 1, rep hP g (vec hP 1)⟫_ℂ := by
  rw [rep_vec, inner_vec, inv_one, one_mul, mul_one]

/-- `δ₁` is cyclic: its orbit under `π` spans a dense subspace. -/
theorem dense_span_orbit :
    (Submodule.span ℂ (Set.range fun g : G => rep hP g (vec hP 1))).topologicalClosure = ⊤ := by
  have : (fun g : G => rep hP g (vec hP 1)) = vec hP := by
    funext g; rw [rep_vec, mul_one]
  rw [this]; exact dense_span_vec hP

end GppPositiveDefiniteGNS

/-! ## The packaged statement -/

namespace GppPositiveDefiniteGNS

open GppFiniteGNS
open scoped InnerProductSpace

/-- **GNS for a positive-definite function on a group** (the statement parked as
`open_gns_from_positive_type`). For every positive-definite `P : G → ℂ` there is a complex
Hilbert space `H`, a homomorphism `π` from `G` into the unitary group of `H` and a vector `ξ`
whose orbit spans a dense subspace, with `P g = ⟪ξ, π g ξ⟫` for every `g`. -/
theorem gns_from_positive_definite {G : Type} [Group G] {P : G → ℂ} (hP : PositiveDefinite P) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H),
      (∀ g, P g = ⟪ξ, π g ξ⟫_ℂ) ∧
        (Submodule.span ℂ (Set.range fun g => π g ξ)).topologicalClosure = ⊤ :=
  ⟨GNS hP, inferInstance, inferInstance, inferInstance, repHom hP, vec hP 1,
    apply_eq_inner_rep hP, dense_span_orbit hP⟩

/-- A real positive-type function on `ℝ`, in `GppHaarPositivityWeil`'s sense, is
positive-definite on the group `ℝ` (written multiplicatively). The two definitions index the
Gram matrix in opposite orders; evenness, which `PositiveType` implies, reconciles them. -/
theorem positiveDefinite_of_positiveType {P : ℝ → ℝ} (hP : GppHaarPositivityWeil.PositiveType P) :
    PositiveDefinite (fun g : Multiplicative ℝ => ((P g.toAdd : ℝ) : ℂ)) := by
  intro n g c
  have h := hP n (fun i => (g i).toAdd) c
  rw [Finset.sum_comm]
  convert h using 3 with i _ j _
  simp only [toAdd_mul, toAdd_inv]
  rw [← hP.even]
  congr 3; ring

/-- **GNS for a positive-type function on `ℝ`** — the statement parked as
`open_gns_from_positive_type`, for the definition `HaarPositivityWeil.lean` actually uses.
A positive-type `P` is a matrix coefficient `P x = ⟪ξ, π x ξ⟫` of a unitary representation of
the additive group `ℝ` on a complex Hilbert space, with `ξ` cyclic. -/
theorem gns_from_positive_type {P : ℝ → ℝ} (hP : GppHaarPositivityWeil.PositiveType P) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H)) (ξ : H),
      (∀ x : ℝ, ((P x : ℝ) : ℂ) = ⟪ξ, π (Multiplicative.ofAdd x) ξ⟫_ℂ) ∧
        (Submodule.span ℂ (Set.range fun g => π g ξ)).topologicalClosure = ⊤ := by
  obtain ⟨H, i₁, i₂, i₃, π, ξ, hcoef, hdense⟩ :=
    gns_from_positive_definite (positiveDefinite_of_positiveType hP)
  exact ⟨H, i₁, i₂, i₃, π, ξ, fun x => hcoef (Multiplicative.ofAdd x), hdense⟩

end GppPositiveDefiniteGNS
