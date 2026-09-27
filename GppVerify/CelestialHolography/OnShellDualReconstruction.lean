import Mathlib.Tactic

/-!
# On-shell reconstruction of a dual/chiral field

This module formalizes the logical structure exposed by chiral first-order gravity.
A deformation/configuration variable `V` reconstructs geometric data `Metric`; the
field equation for an auxiliary dual variable `B` determines its spacetime image
`Gamma` from that geometry; and an injective Penrose-type transform then determines
`B` itself (modulo whatever quotient/gauge has already been built into the type).

This is deliberately abstract.  It does NOT claim that Sharma's twistor `B` is
pointwise equal to a function of the almost-complex deformation off shell.  It says
precisely what must be supplied to conclude that its physical on-shell class carries
no independent information beyond the reconstructed geometry.
-/

namespace GppOnShellDualReconstruction

variable {V Metric B Gamma : Type*}

/-- Abstract reconstruction package. -/
structure ReconstructionData where
  metricOf : V → Metric
  gammaOfMetric : Metric → Gamma
  penroseB : B → Gamma

/-- On-shell compatibility means the spacetime image of `B` equals the dual/chiral
connection determined by the reconstructed metric. -/
def OnShell (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (v : V) (b : B) : Prop :=
  R.penroseB b = R.gammaOfMetric (R.metricOf v)

/-- If the Penrose transform is injective on the physical `B`-classes, then at fixed
`v` there is at most one on-shell `B`.  Thus the dual field has no independent
on-shell degree of freedom at that level. -/
theorem onShell_B_unique
    (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (hP : Function.Injective R.penroseB)
    (v : V) (b₁ b₂ : B)
    (h₁ : OnShell R v b₁) (h₂ : OnShell R v b₂) :
    b₁ = b₂ := by
  apply hP
  rw [h₁, h₂]

/-- If a right inverse/reconstruction of the Penrose transform is available on the
relevant spacetime image, the on-shell dual field is explicitly a composite function
of the original deformation variable. -/
def reconstructedB
    (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (liftB : Gamma → B) : V → B :=
  fun v => liftB (R.gammaOfMetric (R.metricOf v))

/-- A right inverse for `penroseB` gives an on-shell reconstructed dual field. -/
theorem reconstructedB_onShell
    (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (liftB : Gamma → B)
    (hRight : ∀ γ, R.penroseB (liftB γ) = γ)
    (v : V) :
    OnShell R v (reconstructedB R liftB v) := by
  simp [OnShell, reconstructedB, hRight]

/-- With both injectivity and a right inverse, every on-shell dual field equals the
explicit reconstruction from `v`. -/
theorem onShell_B_eq_reconstructed
    (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (liftB : Gamma → B)
    (hRight : ∀ γ, R.penroseB (liftB γ) = γ)
    (hP : Function.Injective R.penroseB)
    (v : V) (b : B)
    (hb : OnShell R v b) :
    b = reconstructedB R liftB v := by
  apply hP
  rw [hb]
  simp [reconstructedB, hRight]

/-- Off-shell independence is logically compatible with on-shell uniqueness: the type
`B` may contain many elements while the field equation selects at most one for each
configuration `v`. -/
theorem offShell_many_onShell_unique
    (R : ReconstructionData (V:=V) (Metric:=Metric) (B:=B) (Gamma:=Gamma))
    (hP : Function.Injective R.penroseB)
    (v : V) :
    ∀ b₁ b₂ : B, OnShell R v b₁ → OnShell R v b₂ → b₁ = b₂ := by
  intro b₁ b₂ h₁ h₂
  exact onShell_B_unique R hP v b₁ b₂ h₁ h₂

end GppOnShellDualReconstruction
