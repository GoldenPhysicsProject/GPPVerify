import GppVerify.RiemannHypothesis.EulerFactorLogDeriv

/-!
# Finite prime powers as an exact massive Green amplitude

This is the next bridge after `EulerFactorLogDeriv.lean`.  The nonzero Fourier modes of
`Wp` have coefficient and frequency

`log(p) p^{-m/2}` and `m log(p)`.

Those same numbers define the positive prime-power boundary distribution in the arithmetic
principal-series heat/resolvent program.  For the one-dimensional massive Green kernel

`R_r(0,x) = exp(-r|x|)/(2r)`,

this file proves, for every finite cutoff, the exact identity

`Σ log(p)p^{-m/2} R_r(0,m log p)
   = (1/(2r)) Σ log(p)p^{-m(1/2+r)}`.

Thus the local Euler/Poisson modes are not merely analogous to the boundary resolvent
atoms: they are exactly the same weights and logarithmic locations.  The finite amplitude
is nonnegative for `r>0`.

The final polarization lemma records the doubled-sector mechanism

`⟪a,b⟫ = (‖a+b‖²-‖a-b‖²)/4`.

It explains how a prime cross term can be extracted from even/odd (or matter/reflected)
boundary states.  It does **not** construct the completed Archimedean boundary condition,
prove that physical cohomology is even, or establish global Weil positivity/RH.
-/

namespace GppPrimeGreen

open Real Finset
open scoped InnerProductSpace

/-- The positive mass of the prime-power boundary atom `(p,m)`. -/
noncomputable def primePowerBoundaryWeight (p : ℝ) (m : ℕ) : ℝ :=
  Real.log p * p ^ (-(m : ℝ) / 2)

/-- The logarithmic position of the prime-power boundary atom `(p,m)`. -/
noncomputable def primePowerBoundaryLocation (p : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log p

/-- The massive one-dimensional Green kernel evaluated against a source at the origin. -/
noncomputable def massiveGreenAtZero (r x : ℝ) : ℝ :=
  Real.exp (-r * |x|) / (2 * r)

theorem primePowerBoundaryWeight_pos {p : ℝ} (hp : 1 < p) {m : ℕ} :
    0 < primePowerBoundaryWeight p m := by
  unfold primePowerBoundaryWeight
  exact mul_pos (Real.log_pos hp)
    (Real.rpow_pos_of_pos (lt_trans one_pos hp) _)

theorem primePowerBoundaryLocation_pos {p : ℝ} (hp : 1 < p) {m : ℕ} (hm : 0 < m) :
    0 < primePowerBoundaryLocation p m := by
  unfold primePowerBoundaryLocation
  exact mul_pos (by exact_mod_cast hm) (Real.log_pos hp)

/-- The boundary atom's mass is exactly the positive-frequency coefficient already found
in the two-sided `Wp` expansion. -/
theorem primePowerBoundaryWeight_eq_coeff {p : ℝ} (hp0 : 0 ≤ p) (m : ℕ) :
    primePowerBoundaryWeight p m =
      GppCutkoskyWeil.primePowerCoeff p (Int.ofNat m) := by
  rw [GppCutkoskyWeil.primePowerCoeff_eq hp0]
  norm_num [primePowerBoundaryWeight]

/-- The boundary atom's position is exactly the positive-frequency mode of `Wp`. -/
theorem primePowerBoundaryLocation_eq_frequency (p : ℝ) (m : ℕ) :
    primePowerBoundaryLocation p m =
      GppCutkoskyWeil.primePowerFrequency p (Int.ofNat m) := by
  unfold primePowerBoundaryLocation GppCutkoskyWeil.primePowerFrequency
  norm_cast

theorem massiveGreenAtZero_pos {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 < massiveGreenAtZero r x := by
  unfold massiveGreenAtZero
  exact div_pos (Real.exp_pos _) (by positivity)

/-- A single prime-power boundary atom propagated by the Green kernel equals its shifted
Dirichlet monomial exactly. -/
theorem boundaryWeight_mul_green_eq {p r : ℝ} (hp : 1 < p)
    {m : ℕ} (hm : 0 < m) :
    primePowerBoundaryWeight p m * massiveGreenAtZero r (primePowerBoundaryLocation p m) =
      (1 / (2 * r)) *
        (Real.log p * p ^ (-(m : ℝ) * (1 / 2 + r))) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hloc : 0 ≤ primePowerBoundaryLocation p m :=
    (primePowerBoundaryLocation_pos hp hm).le
  have hexp :
      Real.exp (Real.log p * (-(m : ℝ) / 2)) *
          Real.exp (-r * ((m : ℝ) * Real.log p)) =
        Real.exp (Real.log p * (-(m : ℝ) * (1 / 2 + r))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold primePowerBoundaryWeight massiveGreenAtZero
  rw [abs_of_nonneg hloc]
  unfold primePowerBoundaryLocation
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0]
  calc
    Real.log p * Real.exp (Real.log p * (-(m : ℝ) / 2)) *
          (Real.exp (-r * ((m : ℝ) * Real.log p)) / (2 * r)) =
        (1 / (2 * r)) *
          (Real.log p *
            (Real.exp (Real.log p * (-(m : ℝ) / 2)) *
              Real.exp (-r * ((m : ℝ) * Real.log p)))) := by ring
    _ = (1 / (2 * r)) *
          (Real.log p * Real.exp (Real.log p * (-(m : ℝ) * (1 / 2 + r)))) := by
      rw [hexp]

/-- The Green amplitude of an arbitrary finite family of prime powers. -/
noncomputable def finitePrimeGreenAmplitude {ι : Type*} (C : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ C, primePowerBoundaryWeight (p i) (m i) *
    massiveGreenAtZero r (primePowerBoundaryLocation (p i) (m i))

/-- The same finite family written as its shifted Dirichlet sum. -/
noncomputable def finitePrimeDirichletAmplitude {ι : Type*} (C : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ) (r : ℝ) : ℝ :=
  (1 / (2 * r)) *
    ∑ i ∈ C, Real.log (p i) * (p i) ^ (-(m i : ℝ) * (1 / 2 + r))

/-- **Exact finite prime Green amplitude.** -/
theorem finitePrimeGreenAmplitude_eq {ι : Type*} (C : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ) (r : ℝ)
    (hp : ∀ i ∈ C, 1 < p i) (hm : ∀ i ∈ C, 0 < m i) :
    finitePrimeGreenAmplitude C p m r = finitePrimeDirichletAmplitude C p m r := by
  unfold finitePrimeGreenAmplitude finitePrimeDirichletAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact boundaryWeight_mul_green_eq (hp i hi) (hm i hi)

/-- Positivity of the finite Green amplitude before the global Archimedean subtraction. -/
theorem finitePrimeGreenAmplitude_nonneg {ι : Type*} (C : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ) {r : ℝ} (hr : 0 < r)
    (hp : ∀ i ∈ C, 1 < p i) :
    0 ≤ finitePrimeGreenAmplitude C p m r := by
  unfold finitePrimeGreenAmplitude
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (primePowerBoundaryWeight_pos (hp i hi)).le
    (massiveGreenAtZero_pos hr _).le

/-- Positivity of the equivalent finite shifted Dirichlet amplitude. -/
theorem finitePrimeDirichletAmplitude_nonneg {ι : Type*} (C : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ) {r : ℝ} (hr : 0 < r)
    (hp : ∀ i ∈ C, 1 < p i) (hm : ∀ i ∈ C, 0 < m i) :
    0 ≤ finitePrimeDirichletAmplitude C p m r := by
  rw [← finitePrimeGreenAmplitude_eq C p m r hp hm]
  exact finitePrimeGreenAmplitude_nonneg C p m hr hp

/-- The exact doubled-sector polarization formula used to isolate a cross amplitude from
the symmetric and antisymmetric boundary states. -/
theorem crossTerm_eq_doubled_norm_difference {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) :
    ⟪a, b⟫_ℝ =
      (1 / 4 : ℝ) * (‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

end GppPrimeGreen
