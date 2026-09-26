import Mathlib.Tactic

/-!
# Ray-field descent through sky/incidence compatibility

A global Einstein scale may be viewed in two equivalent ways:

* as one function on spacetime;
* as a family of functions along null rays which agree whenever two ray-points represent
  the same spacetime point.

The second statement is exactly the abstract form of the transverse/sky consistency
problem that remains after solving the Penrose/NSF Einstein equation separately on every
null ray.

This file formalizes the set-theoretic descent theorem with no differential geometry.
Let `Sample` denote ray-parameter samples (for example pairs `(gamma,s)`), let

  pointOf : Sample -> Point

send each sample to the spacetime point it represents, and let `f : Sample -> K` be a
raywise field.  If `pointOf` is surjective, then `f` comes from a unique spacetime field
`sigma : Point -> K` iff it is constant on the fibres of `pointOf`.

Geometric interpretation external to this file:

* the fibres of `pointOf` are the sky/incidence identifications;
* the null-surface formulation's metricity equations are a concrete differential system
  enforcing the required cross-direction descent of the conformal metric/scale;
* LeBrun's Einstein bundle packages the same compatibility holomorphically over complex
  null-geodesic space.

The theorem below does NOT identify NSF metricity with LeBrun transition functions.  It
isolates the exact descent property that such an identification must establish.
-/

namespace GppRayFieldSkyDescent

variable {Sample Point K : Type*}

/-- A raywise field is sky-compatible when it takes the same value on any two samples
representing the same spacetime point. -/
def SkyCompatible (pointOf : Sample → Point) (f : Sample → K) : Prop :=
  ∀ a b : Sample, pointOf a = pointOf b → f a = f b

/-- Any field pulled back from spacetime is automatically sky-compatible. -/
theorem pullback_is_skyCompatible
    (pointOf : Sample → Point) (sigma : Point → K) :
    SkyCompatible pointOf (fun s => sigma (pointOf s)) := by
  intro a b hab
  rw [hab]

/-- A sky-compatible ray field descends through any surjective incidence map. -/
theorem skyCompatible_descends
    (pointOf : Sample → Point) (hsurj : Function.Surjective pointOf)
    (f : Sample → K) (hf : SkyCompatible pointOf f) :
    ∃ sigma : Point → K, ∀ s : Sample, sigma (pointOf s) = f s := by
  choose representative hrep using hsurj
  let sigma : Point → K := fun x => f (representative x)
  refine ⟨sigma, ?_⟩
  intro s
  dsimp [sigma]
  apply hf
  exact hrep (pointOf s)

/-- The descended spacetime field is unique when every point is represented by a ray
sample. -/
theorem descended_field_unique
    (pointOf : Sample → Point) (hsurj : Function.Surjective pointOf)
    (f : Sample → K)
    (sigma tau : Point → K)
    (hsigma : ∀ s : Sample, sigma (pointOf s) = f s)
    (htau : ∀ s : Sample, tau (pointOf s) = f s) :
    sigma = tau := by
  funext x
  obtain ⟨s,rfl⟩ := hsurj x
  rw [hsigma s, htau s]

/-- Exact iff formulation of ray-to-spacetime descent. -/
theorem skyCompatible_iff_exists_spacetime_field
    (pointOf : Sample → Point) (hsurj : Function.Surjective pointOf)
    (f : Sample → K) :
    SkyCompatible pointOf f ↔
      ∃ sigma : Point → K, ∀ s : Sample, sigma (pointOf s) = f s := by
  constructor
  · exact skyCompatible_descends pointOf hsurj f
  · rintro ⟨sigma,hsigma⟩
    intro a b hab
    calc
      f a = sigma (pointOf a) := (hsigma a).symm
      _ = sigma (pointOf b) := by rw [hab]
      _ = f b := hsigma b

/-- Strong package: under surjective incidence, a compatible raywise field descends to a
unique spacetime field. -/
theorem sky_descent_exists_unique
    (pointOf : Sample → Point) (hsurj : Function.Surjective pointOf)
    (f : Sample → K) (hf : SkyCompatible pointOf f) :
    ∃! sigma : Point → K, ∀ s : Sample, sigma (pointOf s) = f s := by
  obtain ⟨sigma,hsigma⟩ := skyCompatible_descends pointOf hsurj f hf
  refine ⟨sigma,hsigma,?_⟩
  intro tau htau
  exact descended_field_unique pointOf hsurj f tau sigma htau hsigma

end GppRayFieldSkyDescent
