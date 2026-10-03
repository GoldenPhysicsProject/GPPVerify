import GppVerify.RiemannHypothesis.SU11CharacterDefect
import GppVerify.RiemannHypothesis.WallKrylovPoisson
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The prime defect as a TFD-dressed causal delay line

Source: Codex, GPPDiscovery2 `research/2026-09-27_prime_defect_as_tfd_dressed_causal_delay.md`
§§1–4 (bridge copy through `59bf0a2`). The note's own audit paragraph confirms the dressing
identity below; it was re-checked here independently.

Fix a prime `p` and put `L = log p`, `a = p^{-1/2}`, `φ(z) = e^{iLz}` (an inner function of the
upper half-plane), `B_a(u) = (u − a)/(1 − a u)` and `f_a(u) = √(1−a²)/(1 − a u)`.

* `delay_defect`: `D_φ(z,w) := (1 − φ(z) conj φ(w))/(−i (z − w̄)) = ∫₀^L e^{itz} conj(e^{itw}) dt`:
  the bare prime is a causal delay line on `L²([0,L])`;
* `blaschke_one_sub`: for real `a`, `1 − B_a(u) conj B_a(v) = (1−a²)(1 − u v̄)/((1−au)(1−a v̄))`;
* `dressing`: with `Θ = B_a ∘ φ`, `D_Θ(z,w) = f_a(φ z) conj f_a(φ w) · D_φ(z,w)`. The TFD factor
  *multiplicatively dresses* the delay line; it is not an extra additive rank-one channel;
* `feature_gram`: `D_Θ(z,w) = ∫₀^L F_t(z) conj F_t(w) dt` with
  `F_t(z) = f_a(φ z) e^{itz}`;
* `diagonal_delay`: on the real axis `D_Θ(x,x) = L · P_a(Lx)`, where `D(x,x)` means the integral
  of `‖F_t(x)‖²` (the confluent value), and `D_φ(x,x) = L`;
* `excess_delay_series`: the free-delay-subtracted density is the prime-power current,
  `Σ_{m≥1} 2L a^m cos(m L x) = L (P_a(Lx) − 1)`.

## Scope

Pointwise algebra, one elementary integral, and a power series. The identification of the real-axis
diagonal with `d/dx arg Θ(x)` (a derivative of an argument) is not formalized here; its content on the
circle is `blaschke_boundary_delay`. No RH claim.
-/

open Complex GppSU11Prime GppSU11CharacterDefect

namespace GppHalfPlaneDelay

/-- The inner function `φ_L(z) = e^{iLz}`. -/
noncomputable def phi (L : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * L * z)

/-- The upper-half-plane defect kernel `(1 − Θ(z) conj Θ(w))/(−i (z − w̄))`. -/
noncomputable def defectH (Θ : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (1 - Θ z * (starRingEnd ℂ) (Θ w)) / (-Complex.I * (z - (starRingEnd ℂ) w))

/-- **The bare prime is a delay line.** For `z − w̄ ≠ 0`:
`D_φ(z,w) = ∫₀^L e^{itz} conj(e^{itw}) dt`. -/
theorem delay_defect (L : ℝ) (z w : ℂ) (h : z - (starRingEnd ℂ) w ≠ 0) :
    defectH (phi L) z w =
      ∫ t in (0 : ℝ)..L, Complex.exp (Complex.I * t * z) *
        (starRingEnd ℂ) (Complex.exp (Complex.I * t * w)) := by
  have hc : Complex.I * (z - (starRingEnd ℂ) w) ≠ 0 := mul_ne_zero Complex.I_ne_zero h
  have e : ∀ t : ℝ, Complex.exp (Complex.I * t * z) * (starRingEnd ℂ) (Complex.exp (Complex.I * t * w)) =
      Complex.exp ((Complex.I * (z - (starRingEnd ℂ) w)) * (t : ℂ)) := by
    intro t
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  unfold defectH phi
  rw [e L]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hz : z - (starRingEnd ℂ) w ≠ 0 := h
  field_simp
  ring

/-- **Numerator of the Blaschke defect.** For real `a` and complex `u, v` with
`1 − a u ≠ 0`, `1 − a v̄ ≠ 0`:
`1 − B_a(u) conj B_a(v) = (1 − a²)(1 − u v̄)/((1 − a u)(1 − a v̄))`. -/
theorem blaschke_one_sub (a : ℝ) (u v : ℂ) (hu : 1 - (a : ℂ) * u ≠ 0)
    (hv : 1 - (a : ℂ) * (starRingEnd ℂ) v ≠ 0) :
    1 - blaschke (a : ℂ) u * (starRingEnd ℂ) (blaschke (a : ℂ) v) =
      (1 - (a : ℂ) ^ 2) * (1 - u * (starRingEnd ℂ) v) /
        ((1 - a * u) * (1 - a * (starRingEnd ℂ) v)) := by
  rw [conj_blaschke]
  unfold blaschke
  have hY : (1 - (a : ℂ) * u) * (1 - a * (starRingEnd ℂ) v) ≠ 0 := mul_ne_zero hu hv
  have hnum : (1 - (a : ℂ) * u) * (1 - a * (starRingEnd ℂ) v) -
      (u - a) * ((starRingEnd ℂ) v - a) = (1 - (a : ℂ) ^ 2) * (1 - u * (starRingEnd ℂ) v) := by
    ring
  rw [div_mul_div_comm, one_sub_div hY, hnum]

/-- **The TFD dressing identity.** For `Θ = B_a ∘ φ` and `z − w̄ ≠ 0`:
`D_Θ(z,w) = f_a(φ z) conj f_a(φ w) · D_φ(z,w)`. -/
theorem dressing (a L : ℝ) (ha : |a| < 1) (z w : ℂ) (hzw : z - (starRingEnd ℂ) w ≠ 0)
    (hu : 1 - (a : ℂ) * phi L z ≠ 0) (hv : 1 - (a : ℂ) * (starRingEnd ℂ) (phi L w) ≠ 0) :
    defectH (fun x => blaschke (a : ℂ) (phi L x)) z w =
      tfdAmp a (phi L z) * (starRingEnd ℂ) (tfdAmp a (phi L w)) * defectH (phi L) z w := by
  have hcore := defect_blaschke_rank_one a ha (phi L z) (phi L w)
  unfold defectH
  rw [blaschke_one_sub a _ _ hu hv, ← hcore]
  have hd : (-Complex.I * (z - (starRingEnd ℂ) w)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hzw
  field_simp

/-- **Delay-line Gram representation.** For `z − w̄ ≠ 0`:
`D_Θ(z,w) = ∫₀^L F_t(z) conj F_t(w) dt` with `F_t(z) = f_a(φ z) e^{itz}`. -/
theorem feature_gram (a L : ℝ) (ha : |a| < 1) (z w : ℂ) (hzw : z - (starRingEnd ℂ) w ≠ 0)
    (hu : 1 - (a : ℂ) * phi L z ≠ 0) (hv : 1 - (a : ℂ) * (starRingEnd ℂ) (phi L w) ≠ 0) :
    defectH (fun x => blaschke (a : ℂ) (phi L x)) z w =
      ∫ t in (0 : ℝ)..L,
        (tfdAmp a (phi L z) * Complex.exp (Complex.I * t * z)) *
          (starRingEnd ℂ) (tfdAmp a (phi L w) * Complex.exp (Complex.I * t * w)) := by
  rw [dressing a L ha z w hzw hu hv, delay_defect L z w hzw,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [map_mul]
  ring

/-- **The real-axis diagonal is the Poisson delay.** For real `x`, the confluent diagonal
`∫₀^L ‖F_t(x)‖² dt` equals `L · P_a(L x)`; and the bare delay has diagonal `L`. -/
theorem diagonal_delay (a L x : ℝ) (ha : |a| < 1) :
    (∫ t in (0 : ℝ)..L, ‖tfdAmp a (phi L x) * Complex.exp (Complex.I * t * x)‖ ^ 2) =
        L * poisson a (L * x) ∧
      (∫ t in (0 : ℝ)..L, ‖Complex.exp (Complex.I * t * x)‖ ^ 2) = L := by
  have hn : ∀ t : ℝ, ‖Complex.exp (Complex.I * t * x)‖ = 1 := by
    intro t
    have : Complex.I * (t : ℂ) * (x : ℂ) = (((t * x : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hphi : phi L (x : ℂ) = Complex.exp (((L * x : ℝ) : ℂ) * Complex.I) := by
    unfold phi; congr 1; push_cast; ring
  constructor
  · have hb := tfdAmp_boundary a (L * x) ha
    simp_rw [norm_mul, hn, mul_one]
    rw [hphi, hb]
    simp
  · simp_rw [hn]
    simp

/-- **Free-delay subtraction gives the prime-power current.**
`Σ_{m≥1} 2L a^m cos(m L x) = L (P_a(Lx) − 1)`. -/
theorem excess_delay_series (a L x : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun m : ℕ => 2 * L * (a ^ (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * (L * x))))
      (L * (poisson a (L * x) - 1)) := by
  have h := GppWallKrylov.poisson_series a (L * x) ha0 ha1
  have h2 := h.mul_left L
  have e : (fun m : ℕ => 2 * L * (a ^ (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * (L * x)))) =
      fun m : ℕ => L * (2 * (a ^ (m + 1) * Real.cos (((m + 1 : ℕ) : ℝ) * (L * x)))) := by
    funext m; ring
  rw [e]
  unfold poisson
  exact h2

end GppHalfPlaneDelay
