import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Elementary entries of Astra's interval-packet Weil matrix

Exact complex-exponential integrals behind the conventions section of Astra's note
`work/2026-10-17_astra_joint_weil_packet_matrix.md`. On `[-L, L]` with carrier packets
`f_t(x) = exp(i t x) / sqrt(2L)`, with `d = t - s`:

* `packet_overlap`: `⟨f_t, f_s⟩ = sin(dL) / (dL)` for `d ≠ 0`;
* `pole_functional`: `ℓ_a(t) = ∫ f_t(x) exp(a x) dx = 2 sinh((a + it)L) / ((a + it) sqrt(2L))`;
* `pole_functional_conj`: `ℓ_{-a}(t) = conj(ℓ_a(t))` on the centred interval, which is why the pole
  term `2 Re(ℓ_a(t) ℓ_a(s))` is not a positive absolute square (the note's point).

**Scope.** Elementary integrals. The Archimedean digamma/Lerch expression, the symmetric
translation pairing `G_ts(u)`, the prime sum, the shifted-ξ discriminator and all numerics of the note
are not formalized. No claim about positivity of the full matrix, and no RH claim.
-/

namespace GppPacketEntries

open intervalIntegral

/-- `∫_{-L}^{L} exp(i d x) dx = 2 sin(dL)/d` for `d ≠ 0`, i.e. `⟨f_t, f_s⟩ = sin(dL)/(dL)`. -/
theorem packet_overlap (L d : ℝ) (hL : 0 < L) (hd : d ≠ 0) :
    (1 / (2 * (L : ℂ))) * ∫ x in (-L)..L, Complex.exp (((d : ℂ) * Complex.I) * (x : ℂ)) =
      (Real.sin (d * L) / (d * L) : ℝ) := by
  have hc : ((d : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hd) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h2 := Complex.two_sin (x := ((L : ℂ) * d))
  rw [neg_mul] at h2
  have e1 : ((d : ℂ) * Complex.I) * (L : ℂ) = (d * L : ℂ) * Complex.I := by ring
  have e2 : ((d : ℂ) * Complex.I) * ((-L : ℝ) : ℂ) = -(d * L : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2]
  push_cast
  have hdL : (d : ℂ) * (L : ℂ) ≠ 0 := mul_ne_zero hd' hL'
  field_simp
  linear_combination (-Complex.I) * h2 + (Complex.exp ((L : ℂ) * d * Complex.I) - Complex.exp (-((L : ℂ) * d * Complex.I))) * Complex.I_sq

/-- `ℓ_a(t) = (1/√(2L)) ∫_{-L}^{L} exp((a + it) x) dx = 2 sinh((a + it)L) / ((a + it)√(2L))`. -/
theorem pole_functional (L a t : ℝ) (hL : 0 < L) (hz : (a : ℂ) + t * Complex.I ≠ 0) :
    ((Real.sqrt (2 * L) : ℝ) : ℂ)⁻¹ *
        ∫ x in (-L)..L, Complex.exp (((a : ℂ) + t * Complex.I) * (x : ℂ)) =
      2 * Complex.sinh (((a : ℂ) + t * Complex.I) * L) /
        (((a : ℂ) + t * Complex.I) * ((Real.sqrt (2 * L) : ℝ) : ℂ)) := by
  rw [integral_exp_mul_complex hz]
  set z : ℂ := (a : ℂ) + t * Complex.I with hzdef
  have hs : ((Real.sqrt (2 * L) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by linarith)).ne'
  have h2 : Complex.exp (z * L) - Complex.exp (z * ((-L : ℝ) : ℂ)) = 2 * Complex.sinh (z * L) := by
    rw [Complex.sinh]; push_cast
    rw [show z * (-(L : ℂ)) = -(z * L) by ring]; ring
  rw [h2]
  field_simp

/-- On the centred interval, `ℓ_{-a}(t) = conj(ℓ_a(t))`: the pole functional is conjugation-symmetric,
so `2 Re(ℓ_a ℓ_a)` is not a positive absolute square. -/
theorem pole_functional_conj (L a t : ℝ) (hL : 0 < L) (ha : a ≠ 0) :
    2 * Complex.sinh ((((-a : ℝ) : ℂ) + t * Complex.I) * L) /
        ((((-a : ℝ) : ℂ) + t * Complex.I) * ((Real.sqrt (2 * L) : ℝ) : ℂ)) =
      (starRingEnd ℂ)
        (2 * Complex.sinh (((a : ℂ) + t * Complex.I) * L) /
          (((a : ℂ) + t * Complex.I) * ((Real.sqrt (2 * L) : ℝ) : ℂ))) := by
  have hz : (a : ℂ) - t * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha this
  have e1 : (((-a : ℝ) : ℂ) + t * Complex.I) = -((a : ℂ) - t * Complex.I) := by push_cast; ring
  have e2 : (starRingEnd ℂ) ((a : ℂ) + t * Complex.I) = (a : ℂ) - t * Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [map_div₀, map_mul, map_mul, Complex.conj_ofReal, e2, ← Complex.sinh_conj, map_mul,
    Complex.conj_ofReal, e2, map_ofNat, e1]
  have : Complex.sinh (-((a : ℂ) - t * Complex.I) * L) = -Complex.sinh (((a : ℂ) - t * Complex.I) * L) := by
    rw [neg_mul, Complex.sinh_neg]
  rw [this]
  have hs : ((Real.sqrt (2 * L) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by linarith)).ne'
  field_simp

#print axioms GppPacketEntries.packet_overlap
#print axioms GppPacketEntries.pole_functional
#print axioms GppPacketEntries.pole_functional_conj

end GppPacketEntries
