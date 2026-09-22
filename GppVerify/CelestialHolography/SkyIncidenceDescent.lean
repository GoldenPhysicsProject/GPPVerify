import Mathlib.Tactic

/-!
# Sky-incidence descent for raywise Einstein data

Let `F` be a point--ray correspondence space with projection

  point : F -> M.

A raywise field, after evaluation at the incident point, is simply a function

  shat : F -> A.

It comes from a single spacetime field `sigma : M -> A` precisely when it is constant on
the fibres of `point`, i.e. when all rays in the sky through one spacetime point give the
same evaluated value.

This is the exact set-theoretic descent statement underlying the proposed passage from a
section of the raywise rank-two Einstein system to one spacetime conformal scale.  In the
actual ambitwistor/correspondence geometry, `F` also projects to ray space `N`; pulling a
raywise solution bundle back along that second projection supplies the evaluated function
`shat`.  LeBrun's transverse holomorphic structure and the null-surface metricity equations
are candidates for the differential/holomorphic enhancement of the fibre-constancy
condition formalized here.

No claim about those differential equations is made in this file.
-/

namespace GppSkyIncidenceDescent

variable {F M A : Type*}

/-- A function on correspondence space is sky-basic if it has the same value at any two
incidence points lying over the same spacetime point. -/
def SkyBasic (point : F → M) (shat : F → A) : Prop :=
  ∀ u v : F, point u = point v → shat u = shat v

/-- Any spacetime field pulled back to correspondence space is sky-basic. -/
theorem pullback_is_skyBasic
    (point : F → M) (sigma : M → A) :
    SkyBasic point (fun u => sigma (point u)) := by
  intro u v huv
  rw [huv]

/-- If the incidence projection is surjective, every sky-basic correspondence-space field
descends to a spacetime field.  The definition uses a choice of one incident ray through
each spacetime point; sky-basicness makes the resulting value independent of that choice. -/
theorem skyBasic_descends
    (point : F → M) (hpoint : Function.Surjective point)
    (shat : F → A) (hbasic : SkyBasic point shat) :
    ∃ sigma : M → A, ∀ u : F, shat u = sigma (point u) := by
  choose lift hlift using hpoint
  let sigma : M → A := fun x => shat (lift x)
  refine ⟨sigma, ?_⟩
  intro u
  apply hbasic u (lift (point u))
  symm
  exact hlift (point u)

/-- Exact iff: under surjectivity, sky-basicness is equivalent to factorization through
spacetime. -/
theorem skyBasic_iff_factors_through_point
    (point : F → M) (hpoint : Function.Surjective point)
    (shat : F → A) :
    SkyBasic point shat ↔
      ∃ sigma : M → A, ∀ u : F, shat u = sigma (point u) := by
  constructor
  · exact skyBasic_descends point hpoint shat
  · rintro ⟨sigma,hsigma⟩ u v huv
    rw [hsigma u, hsigma v, huv]

/-- Uniqueness of the descended spacetime field when the incidence projection is
surjective. -/
theorem descended_field_unique
    (point : F → M) (hpoint : Function.Surjective point)
    (shat : F → A)
    (sigma tau : M → A)
    (hsigma : ∀ u : F, shat u = sigma (point u))
    (htau : ∀ u : F, shat u = tau (point u)) :
    sigma = tau := by
  funext x
  obtain ⟨u,hu⟩ := hpoint x
  have h1 := hsigma u
  have h2 := htau u
  rw [hu] at h1 h2
  exact h1.symm.trans h2

/-- Pairwise formulation on a named sky fibre. -/
def SkyFibre (point : F → M) (x : M) := {u : F // point u = x}

/-- Sky-basicness says exactly that the restriction to every sky fibre is constant. -/
theorem skyBasic_restrict_constant
    (point : F → M) (shat : F → A) (hbasic : SkyBasic point shat)
    (x : M) (u v : SkyFibre point x) :
    shat u.1 = shat v.1 := by
  apply hbasic u.1 v.1
  exact u.2.trans v.2.symm

end GppSkyIncidenceDescent
