import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The signed local Weil multiplier is an Euler radial score

For one prime p > 1, set

D_p(sigma,t) = 1 - 2 exp(-sigma log p) cos(t log p) + exp(-2 sigma log p).

This is |1-p^(-sigma-it)|^2, so -log D_p is the logarithm of the squared
modulus of the local Euler factor. The main theorem proves directly in real
calculus that at the half-density point

d/dsigma [-log D_p(sigma,t)] |_(sigma=1/2) = -Wp(p,t),

where -Wp is exactly the signed local prime multiplier occurring in the
classical explicit-formula normalization already formalized in
EulerFactorLogDeriv.lean.

This is a zero-free identity. It gives the precise mathematical content of
the radial-score interpretation of the local Euler channel; it does not
assert positivity of the global Weil form or RH.
-/

open Real

namespace GppEulerRadialScore

open GppCutkoskyWeil

/-- The Euler radius p^(-sigma), written in a form convenient for real differentiation. -/
noncomputable def radius (p sigma : ℝ) : ℝ :=
  Real.exp (-sigma * Real.log p)

/-- The positive local Euler denominator
|1-p^(-sigma-it)|^2 = 1 - 2 q cos(t log p) + q^2, with q = p^(-sigma). -/
noncomputable def eulerDen (p sigma t : ℝ) : ℝ :=
  1 - 2 * radius p sigma * Real.cos (t * Real.log p) + (radius p sigma) ^ 2

/-- Logarithm of the local Euler intensity |zeta_p(sigma+it)|^2. -/
noncomputable def logEulerIntensity (p sigma t : ℝ) : ℝ :=
  -Real.log (eulerDen p sigma t)

/-- The radius has the expected radial derivative. -/
theorem hasDerivAt_radius (p sigma : ℝ) :
    HasDerivAt (radius p) (-(Real.log p) * radius p sigma) sigma := by
  unfold radius
  have hlin : HasDerivAt (fun x : ℝ => -x * Real.log p) (-Real.log p) sigma := by
    simpa using (hasDerivAt_id sigma).neg.mul_const (Real.log p)
  have h := hlin.exp
  convert h using 1 <;> ring

/-- At positive sigma and p>1 the Euler denominator is strictly positive. -/
theorem eulerDen_pos {p sigma t : ℝ} (hp : 1 < p) (hsigma : 0 < sigma) :
    0 < eulerDen p sigma t := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hq0 : 0 < radius p sigma := by
    unfold radius
    exact Real.exp_pos _
  have hq1 : radius p sigma < 1 := by
    unfold radius
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hcos : Real.cos (t * Real.log p) <= 1 := Real.cos_le_one _
  have h1 : 0 < (1 - radius p sigma) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq1)
  unfold eulerDen
  nlinarith

/-- Closed derivative formula for the local Euler radial score. -/
theorem hasDerivAt_logEulerIntensity {p sigma t : ℝ} (hp : 1 < p) (hsigma : 0 < sigma) :
    HasDerivAt (fun x : ℝ => logEulerIntensity p x t)
      (2 * Real.log p * radius p sigma *
        (radius p sigma - Real.cos (t * Real.log p)) / eulerDen p sigma t) sigma := by
  have hq := hasDerivAt_radius p sigma
  have hq2 := hq.pow 2
  have hD : HasDerivAt (fun x : ℝ => eulerDen p x t)
      (-2 * (-(Real.log p) * radius p sigma) * Real.cos (t * Real.log p) +
        2 * radius p sigma * (-(Real.log p) * radius p sigma)) sigma := by
    unfold eulerDen
    convert ((hq.const_mul (-2 * Real.cos (t * Real.log p))).const_add 1).add hq2 using 1 <;>
      ring
  have hD0 : eulerDen p sigma t != 0 := (eulerDen_pos hp hsigma).ne'
  have hlog := hD.log hD0
  unfold logEulerIntensity
  have hneg := hlog.neg
  convert hneg using 1
  field_simp
  ring

/-- At sigma=1/2, the real-exponential radius is exactly the project radius p^(-1/2). -/
theorem radius_half {p : ℝ} (hp : 1 < p) :
    radius p (1 / 2 : ℝ) = p ^ (-(1 / 2 : ℝ)) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  unfold radius
  rw [GppCutkoskyWeil.rpow_neg_half_eq_exp hp0]
  congr 1
  ring

/-- The denominator at half-density is the denominator used in Kp. -/
theorem eulerDen_half {p t : ℝ} (hp : 1 < p) :
    eulerDen p (1 / 2 : ℝ) t =
      1 - 2 * p ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p) + p⁻¹ := by
  have hp0 : 0 < p := lt_trans one_pos hp
  rw [eulerDen, radius_half hp]
  have hsq : (p ^ (-(1 / 2 : ℝ))) ^ 2 = p⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hsq]

/-- Local radial-score identity.
The signed prime multiplier is exactly the radial derivative of the log local Euler
intensity at the half-density point. -/
theorem hasDerivAt_logEulerIntensity_half {p t : ℝ} (hp : 1 < p) :
    HasDerivAt (fun sigma : ℝ => logEulerIntensity p sigma t)
      (weilPrimeMultiplier p t) (1 / 2 : ℝ) := by
  have h := hasDerivAt_logEulerIntensity (p := p) (sigma := (1 / 2 : ℝ)) (t := t) hp (by norm_num)
  refine h.congr_deriv ?_
  have hp0 : 0 < p := lt_trans one_pos hp
  have hdenpos : 0 <
      1 - 2 * p ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p) + p⁻¹ := by
    simpa [eulerDen_half hp] using
      eulerDen_pos (p := p) (sigma := (1/2:ℝ)) (t := t) hp (by norm_num)
  have hden : 1 - 2 * p ^ (-(1 / 2 : ℝ)) * Real.cos (t * Real.log p) + p⁻¹ != 0 :=
    hdenpos.ne'
  rw [radius_half hp, eulerDen_half hp]
  unfold weilPrimeMultiplier Wp Kp
  have hsq : (p ^ (-(1 / 2 : ℝ))) ^ 2 = p⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  field_simp
  nlinarith [hsq]

/-- Ordinary derivative form of the radial-score identity. -/
theorem deriv_logEulerIntensity_half {p t : ℝ} (hp : 1 < p) :
    deriv (fun sigma : ℝ => logEulerIntensity p sigma t) (1 / 2 : ℝ) =
      weilPrimeMultiplier p t :=
  (hasDerivAt_logEulerIntensity_half hp).deriv

end GppEulerRadialScore
