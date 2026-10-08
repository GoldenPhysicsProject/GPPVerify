import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `SU(1,1)` covariance of the weight-`k` Hardy kernels

This is the representation-theoretic content behind the `k = 1/2` matching in `CayleyHardyKernel`:
the kernels `(1 − u v̄)^{-2k}` on the unit disc are *covariant* under the disc automorphisms
`φ_a(u) = (u − a)/(1 − ā u)`, `‖a‖ < 1`, with the multiplier `φ_a'(u)^k`. In other words they are the
reproducing kernels of the lowest-weight (holomorphic) representations of `SU(1,1)` — the boundary
(`AdS₂`) side of a one-dimensional conformal theory.

* `one_sub_aut_mul_conj_aut`: `1 − φ(u) conj φ(v) = (1 − |a|²)(1 − u v̄)/((1 − ā u)(1 − a v̄))`;
* `hasDerivAt_aut`: `φ_a'(u) = (1 − |a|²)/(1 − ā u)²`;
* `szego_covariance` (`k = 1/2`): with the multiplier `m(u) = √(1 − |a|²)/(1 − ā u)`
  (so `m² = φ'`), `m(u) · conj m(v) · (1 − φ(u) conj φ(v))⁻¹ = (1 − u v̄)⁻¹`;
* `bergman_covariance` (`k = 1`): `φ'(u) conj φ'(v) (1 − φ(u) conj φ(v))⁻² = (1 − u v̄)⁻²`.

## Checks and scope

These are exact identities, valid for `‖a‖ < 1` and `‖u‖, ‖v‖ < 1`. They say that the Szegő and
Bergman kernels are `SU(1,1)`-covariant of weights `1/2` and `1`; they do **not** say anything about the
arithmetic kernel `ζ(1 + z + w̄)`, which is covariant only at leading order near the boundary pole.
Not formalized: the group law/cocycle for compositions of automorphisms, the Hilbert-space completion
and unitarity of the resulting representation, and general `k` (non-integer `2k` needs a choice of
branch for `(1 − u v̄)^{-2k}`). No RH claim.
-/

open ComplexConjugate

namespace GppSU11Covariance

/-- The disc automorphism `φ_a(u) = (u − a)/(1 − ā u)`. -/
noncomputable def aut (a u : ℂ) : ℂ := (u - a) / (1 - conj a * u)

theorem one_sub_conj_mul_ne_zero (a u : ℂ) (ha : ‖a‖ < 1) (hu : ‖u‖ < 1) : 1 - conj a * u ≠ 0 := by
  intro h
  have h' : conj a * u = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖conj a * u‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact ha
  rw [h', norm_one] at hn
  exact lt_irrefl _ hn

/-- `conj (φ_a v) = (v̄ − ā)/(1 − a v̄)`. -/
theorem conj_aut (a v : ℂ) : conj (aut a v) = (conj v - conj a) / (1 - a * conj v) := by
  unfold aut
  simp [map_div₀, map_sub, map_mul]

/-- The pure-algebra core of the kernel identity (with `b = ā`, `w = v̄`). -/
theorem kernel_alg (a b u w : ℂ) (h1 : 1 - b * u ≠ 0) (h2 : 1 - a * w ≠ 0) :
    1 - (u - a) / (1 - b * u) * ((w - b) / (1 - a * w)) =
      (1 - a * b) * (1 - u * w) / ((1 - b * u) * (1 - a * w)) := by
  have h1' : 1 - u * b ≠ 0 := by rwa [mul_comm]
  have h2' : 1 - w * a ≠ 0 := by rwa [mul_comm]
  rw [eq_div_iff (mul_ne_zero h1 h2)]
  field_simp
  ring

/-- **The kernel identity.** -/
theorem one_sub_aut_mul_conj_aut (a u v : ℂ) (hu : 1 - conj a * u ≠ 0) (hv : 1 - conj a * v ≠ 0) :
    1 - aut a u * conj (aut a v) =
      (1 - (Complex.normSq a : ℂ)) * (1 - u * conj v) / ((1 - conj a * u) * (1 - a * conj v)) := by
  have hv' : 1 - a * conj v ≠ 0 := by
    intro h; apply hv
    have := congrArg (starRingEnd ℂ) h
    simpa [map_sub, map_mul, mul_comm] using this
  rw [conj_aut, ← Complex.mul_conj a]
  unfold aut
  rw [kernel_alg a (conj a) u (conj v) hu hv', mul_comm a (conj a)]

theorem hasDerivAt_aut (a u : ℂ) (hu : 1 - conj a * u ≠ 0) :
    HasDerivAt (aut a) ((1 - (Complex.normSq a : ℂ)) / (1 - conj a * u) ^ 2) u := by
  have h1 : HasDerivAt (fun x : ℂ => x - a) 1 u := (hasDerivAt_id u).sub_const a
  have h2 : HasDerivAt (fun x : ℂ => 1 - conj a * x) (-conj a) u := by
    simpa using ((hasDerivAt_id u).const_mul (conj a)).const_sub 1
  refine (h1.div h2 hu).congr_deriv ?_
  rw [← Complex.mul_conj a]
  field_simp
  ring

/-- The weight-`1/2` multiplier `m(u) = s/(1 − ā u)` with `s = √(1 − |a|²)`. -/
noncomputable def szegoMultiplier (a u : ℂ) : ℂ :=
  (Real.sqrt (1 - Complex.normSq a) : ℂ) / (1 - conj a * u)

/-- `m² = φ'`: the multiplier is a square root of the derivative. -/
theorem szegoMultiplier_sq (a u : ℂ) (ha : ‖a‖ < 1) :
    szegoMultiplier a u ^ 2 = (1 - (Complex.normSq a : ℂ)) / (1 - conj a * u) ^ 2 := by
  have h0 : 0 ≤ 1 - Complex.normSq a := by
    have : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
    nlinarith [norm_nonneg a]
  unfold szegoMultiplier
  rw [div_pow]
  congr 1
  have := Real.sq_sqrt h0
  exact_mod_cast this

/-- **`k = 1/2` (Szegő) covariance.** -/
theorem szego_covariance (a u v : ℂ) (ha : ‖a‖ < 1) (hu : 1 - conj a * u ≠ 0)
    (hv : 1 - conj a * v ≠ 0) (huv : 1 - u * conj v ≠ 0) :
    szegoMultiplier a u * conj (szegoMultiplier a v) * (1 - aut a u * conj (aut a v))⁻¹ =
      (1 - u * conj v)⁻¹ := by
  have hv' : 1 - a * conj v ≠ 0 := by
    intro h; apply hv
    have := congrArg (starRingEnd ℂ) h
    simpa [map_sub, map_mul, mul_comm] using this
  have h0 : 0 ≤ 1 - Complex.normSq a := by
    have : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
    nlinarith [norm_nonneg a]
  have hs2 : ((Real.sqrt (1 - Complex.normSq a) : ℝ) : ℂ) * ((Real.sqrt (1 - Complex.normSq a) : ℝ) : ℂ) =
      1 - (Complex.normSq a : ℂ) := by
    have := Real.mul_self_sqrt h0
    exact_mod_cast this
  have hden : 1 - (Complex.normSq a : ℂ) ≠ 0 := by
    have : 0 < 1 - Complex.normSq a := by
      have : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
      nlinarith [norm_nonneg a]
    exact_mod_cast this.ne'
  unfold szegoMultiplier
  rw [map_div₀, Complex.conj_ofReal, map_sub, map_one, map_mul, Complex.conj_conj,
    one_sub_aut_mul_conj_aut a u v hu hv]
  set s : ℂ := ((Real.sqrt (1 - Complex.normSq a) : ℝ) : ℂ)
  field_simp
  rw [← hs2]
  ring

/-- **`k = 1` (Bergman) covariance.** -/
theorem bergman_covariance (a u v : ℂ) (ha : ‖a‖ < 1) (hu : 1 - conj a * u ≠ 0)
    (hv : 1 - conj a * v ≠ 0) (huv : 1 - u * conj v ≠ 0) :
    ((1 - (Complex.normSq a : ℂ)) / (1 - conj a * u) ^ 2) *
        conj ((1 - (Complex.normSq a : ℂ)) / (1 - conj a * v) ^ 2) *
        ((1 - aut a u * conj (aut a v)) ^ 2)⁻¹ = ((1 - u * conj v) ^ 2)⁻¹ := by
  have hv' : 1 - a * conj v ≠ 0 := by
    intro h; apply hv
    have := congrArg (starRingEnd ℂ) h
    simpa [map_sub, map_mul, mul_comm] using this
  have hden : 1 - (Complex.normSq a : ℂ) ≠ 0 := by
    have : 0 < 1 - Complex.normSq a := by
      have : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
      nlinarith [norm_nonneg a]
    exact_mod_cast this.ne'
  have hreal : conj (1 - (Complex.normSq a : ℂ)) = 1 - (Complex.normSq a : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [one_sub_aut_mul_conj_aut a u v hu hv]
  simp only [map_div₀, map_pow, map_sub, map_one, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  field_simp

end GppSU11Covariance
