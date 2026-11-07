import GppVerify.RiemannHypothesis.ArchimedeanTateParity

open MeasureTheory Complex FourierTransform LocalTate.Archimedean

-- The odd test vector and sign character must give the shifted Gaussian moment.
example {s : ℂ} (hs : 0 < (s + 1).re) :
    (∫ x : ℝ, ((x : ℂ) * (gaussian x : ℂ)) * (Real.sign x : ℂ) *
      ((|x| : ℝ) : ℂ) ^ (s - 1)) = Gammaℝ (s + 1) := by
  simpa [parityZeta, testVector, archFactor] using
    parityZeta_testVector (s := s) (1 : Fin 2) (by simpa using hs)

example (a : Fin 2) : Integrable (testVector a) := integrable_testVector a

-- The even case is exactly the existing #499 API, for every totalized parameter.
example (s : ℂ) : parityZeta 0 (testVector 0) s = localZeta s := by
  simpa using parityZeta_testVector_eq_localZeta 0 s

example {s : ℂ} (hs : 0 < s.re) : parityZeta 0 (testVector 0) s = Gammaℝ s := by
  simpa [archFactor] using parityZeta_testVector (s := s) 0 (by simpa using hs)

-- Fix the measure normalization and show the odd eigenvector is not zero.
example : parityZeta 0 (testVector 0) 1 = 1 := by
  simpa [archFactor] using parityZeta_testVector (s := 1) 0 (by norm_num)
example : testVector 1 1 ≠ 0 := by
  simp [testVector, gaussian]

-- The sign character compensates the negative x in the odd vector.
example : testVector 1 (-1) * (Real.sign (-1) : ℂ) = (gaussian (-1) : ℂ) := by
  rw [Real.sign_of_neg (by norm_num : (-1 : ℝ) < 0)]
  norm_num [testVector]

-- Odd s=0 is convergent even though the two pointwise integrands differ at zero.
example : parityZeta 1 (testVector 1) 0 = 1 := by
  simpa [archFactor] using parityZeta_testVector (s := 0) 1 (by norm_num)

example : testVector 1 0 * (Real.sign 0 : ℂ) * (0 : ℂ) ^ (-1 : ℂ) ≠
    (gaussian 0 : ℂ) * (0 : ℂ) ^ (0 : ℂ) := by
  norm_num [testVector, gaussian]

-- The odd convergence half-plane is Re s > -1, not merely Re s > 0.
example : parityZeta 1 (testVector 1) (-1 / 2) = Gammaℝ (1 / 2) := by
  have h := parityZeta_testVector (s := -1 / 2) 1 (by norm_num)
  norm_num [archFactor] at h ⊢
  exact h

example : Integrable (fun x : ℝ => testVector 1 x * (Real.sign x : ℂ) *
    ((|x| : ℝ) : ℂ) ^ ((-1 / 2 : ℂ) - 1)) := by
  simpa using integrable_parityZeta_testVector (s := -1 / 2) 1 (by norm_num)

example (a : Fin 2) {s : ℂ} (hs : 0 < (s + (a.val : ℂ)).re) :
    archFactor a s ≠ 0 := archFactor_ne_zero a hs

example (a : Fin 2) {s : ℂ} (hs : 0 < (s + (a.val : ℂ)).re) :
    Integrable (fun x : ℝ => testVector a x * (Real.sign x : ℂ) ^ a.val *
      ((|x| : ℝ) : ℂ) ^ (s - 1)) := integrable_parityZeta_testVector a hs

example : archPhase 0 = 1 := by norm_num [archPhase]
example : archPhase 1 = -I := by norm_num [archPhase]
example : archPhase 1 ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num [archPhase] at this
example (a : Fin 2) : ‖archPhase a‖ = 1 := norm_archPhase a

example (x : ℝ) : 𝓕 (testVector 0) x = testVector 0 x := by
  simpa [archPhase] using congrFun (fourier_testVector 0) x
example (x : ℝ) : 𝓕 (testVector 1) x = -I * testVector 1 x := by
  simpa [archPhase] using congrFun (fourier_testVector 1) x

example (a : Fin 2) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    archFactor a s * parityZeta a (𝓕 (testVector a)) (1 - s) =
      archPhase a * archFactor a (1 - s) * parityZeta a (testVector a) s :=
  localFE_testVector a h0 h1

-- Exact negative control: GammaR(2)=1/pi, GammaR(-1)=-2*pi.
-- The factor is NOT invariant under s -> 1-s; no decimals enter this test.
example : archFactor 0 2 ≠ archFactor 0 (1 - 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    norm_num [Gammaℝ_def, Complex.cpow_neg_one]
  have hneg : Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
    have hrec := Gammaℝ_add_two (s := (-1 : ℂ)) (by norm_num)
    norm_num only [show (-1 : ℂ) + 2 = 1 by ring, Gammaℝ_one] at hrec
    field_simp [hpi] at hrec
    linear_combination hrec
  norm_num only [archFactor, Fin.val_zero, Nat.cast_zero, add_zero,
    show (1 : ℂ) - 2 = -1 by ring]
  rw [htwo, hneg]
  intro h
  have hr : Real.pi⁻¹ = -2 * Real.pi := by exact_mod_cast h
  have hp : 0 < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
  linarith [Real.pi_pos]

#print axioms LocalTate.Archimedean.parityZeta_testVector
#print axioms LocalTate.Archimedean.integrable_parityZeta_testVector
#print axioms LocalTate.Archimedean.integrable_testVector
#print axioms LocalTate.Archimedean.fourier_testVector
#print axioms LocalTate.Archimedean.localFE_testVector

#print axioms LocalTate.Archimedean.archFactor_ne_zero
#print axioms LocalTate.Archimedean.norm_archPhase
