import Mathlib.Tactic

/-!
# Flat-ball gravitational first law from the scalar curvature Green identity

Let N_l=(l²-r²)/(2l) and let gamma_ij be a smooth metric perturbation
of a flat spatial ball with fixed coordinate domain.

The continuum twice-integrated scalar curvature identity is
  ∫_B N_l δR
   = [2(n-1)/l] δV - 2 δA,
where δV=1/2∫ tr gamma and δA=1/2∮ q^ij gamma_ij.
The proof is by Green's theorem, N_l|boundary=0 and
∂_n N_l=-1. It assumes no homogeneity of gamma.

Together with the linearized time-symmetric Einstein Hamiltonian
constraint δR=16πG δrho, it gives
  δA - k δV = -8πG ∫N_l δrho, k=(n-1)/l.
Matched conformal matter modular first law then yields
  δS_gen=eta*k δV.

This Lean file proves:
(A) the exact linear-functional consequences of the Green identity
    and Einstein constraint under explicitly stated hypotheses;
(B) a concrete nonconstant radial metric gamma_ij = a delta_ij
    + b x_i x_j, for which all scalar/geometric moments are computed
    exactly and the Green identity holds as an algebraic identity.

It does NOT formalize arbitrary smooth Riemannian metrics, the
divergence theorem, the physical Einstein constraint, or QFT KMS.
Those are physical/analytic inputs, not custom axioms in Lean.
-/

namespace GppDiamondFlatFirstLaw

section RadialPolynomial

/-- Integrals for gamma_ij=a δ_ij+b x_i x_j on the Euclidean n-ball:
the ball moment is ∫r²=(n/(n+2)) R² V.
The actual spatial volume variation is half the integrated trace. -/
noncomputable def radialVolumeVariation
    (n R V a b : ℝ) : ℝ :=
  (V / 2) * (n * a + b * n * R^2 / (n+2))

/-- At r=R, gamma_AB = a q_AB because x is purely normal. -/
noncomputable def radialAreaVariation
    (n A a : ℝ) : ℝ :=
  (A / 2) * (n-1) * a

/-- δR = n(n-1)b; average CKV lapse on ball is RV/(n+2). -/
noncomputable def radialWeightedCurvature
    (n R V b : ℝ) : ℝ :=
  b * n * (n-1) * R * V / (n+2)

/-- Explicit nonconstant radial polynomial test of the linearized
gravitational Green identity. No first law assumed. -/
theorem radial_polynomial_flat_green_identity
    (n R V A a b : ℝ)
    (hR : R ≠ 0) (hn : n + 2 ≠ 0)
    (hAV : A = n * V / R) :
    radialAreaVariation n A a -
        ((n-1)/R) * radialVolumeVariation n R V a b =
      -(1/2 : ℝ) * radialWeightedCurvature n R V b := by
  unfold radialAreaVariation radialVolumeVariation radialWeightedCurvature
  rw [hAV]
  field_simp
  ring

/-- The homogeneous flat mode is just the b=0 special case. -/
theorem radial_polynomial_homogeneous_limit
    (n R V A a : ℝ) (hR : R ≠ 0)
    (hn : n + 2 ≠ 0) (hAV : A = n*V/R) :
    radialAreaVariation n A a =
      ((n-1)/R) * radialVolumeVariation n R V a 0 := by
  have h := radial_polynomial_flat_green_identity
    n R V A a 0 hR hn hAV
  simpa [radialWeightedCurvature] using h

end RadialPolynomial

section LinearizedGreenFirstLaw

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The smooth linearized Green identity plus Einstein's flat-slice
Hamiltonian constraint imply the causal-diamond first law, instead
of assuming that *first-law conclusion* outright. -/
theorem einstein_diamond_first_law_from_green
    (dA dV dCurvature dMatter : E →ₗ[ℝ] ℝ)
    (k G : ℝ)
    (hGreen : ∀ x, dCurvature x = 2*k*dV x - 2*dA x)
    (hEinstein : ∀ x, dCurvature x =
      (16 * Real.pi * G) * dMatter x)
    (delta : E) :
    dA delta - k*dV delta =
      -(8*Real.pi*G)*dMatter delta := by
  have hg := hGreen delta
  have he := hEinstein delta
  rw [he] at hg
  linarith

/-- If the matter entropy response has the thermal modular
coefficient beta=8πG eta and the geometric entropy is eta dA,
the full entropy variation is exactly eta k dV. -/
theorem generalized_entropy_work_from_green
    (dA dV dCurvature dMatter : E →ₗ[ℝ] ℝ)
    (k G eta beta : ℝ)
    (hGreen : ∀ x, dCurvature x = 2*k*dV x - 2*dA x)
    (hEinstein : ∀ x, dCurvature x =
      (16 * Real.pi * G) * dMatter x)
    (hBeta : beta = 8*Real.pi*G*eta)
    (delta : E) :
    eta * dA delta + beta * dMatter delta =
      eta*k*dV delta := by
  have h := einstein_diamond_first_law_from_green
    dA dV dCurvature dMatter k G hGreen hEinstein delta
  have hm := congrArg (fun z : ℝ => eta * z) h
  rw [hBeta]
  nlinarith [hm]

/-- For a finite nondegenerate diamond, generalized entropy
stationarity is equivalent to fixed proper volume under the
precisely stated Einstein + Green + modular hypotheses. -/
theorem entropy_stationary_iff_fixed_volume_from_green
    (dA dV dCurvature dMatter : E →ₗ[ℝ] ℝ)
    (k G eta beta : ℝ)
    (hk : k ≠ 0) (heta : eta ≠ 0)
    (hGreen : ∀ x, dCurvature x = 2*k*dV x - 2*dA x)
    (hEinstein : ∀ x, dCurvature x =
      (16 * Real.pi * G) * dMatter x)
    (hBeta : beta = 8*Real.pi*G*eta)
    (delta : E) :
    eta * dA delta + beta * dMatter delta = 0 ↔
      dV delta = 0 := by
  rw [generalized_entropy_work_from_green
    dA dV dCurvature dMatter k G eta beta
    hGreen hEinstein hBeta delta]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero heta hk)
  · intro h
    simp [h]

end LinearizedGreenFirstLaw

end GppDiamondFlatFirstLaw

#print axioms GppDiamondFlatFirstLaw.radial_polynomial_flat_green_identity
#print axioms GppDiamondFlatFirstLaw.einstein_diamond_first_law_from_green
#print axioms GppDiamondFlatFirstLaw.generalized_entropy_work_from_green
#print axioms GppDiamondFlatFirstLaw.entropy_stationary_iff_fixed_volume_from_green
