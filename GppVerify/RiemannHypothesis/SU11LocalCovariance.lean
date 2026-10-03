import GppVerify.RiemannHypothesis.SU11LightconeTail
import GppVerify.RiemannHypothesis.SU11CharacterDefect
import GppVerify.RiemannHypothesis.FourComponentRigidity
import GppVerify.RiemannHypothesis.CriticalBPYCoercivity

/-!
# Antipodal phases, the trivial-zero ladder, and the heat-trace/Plancherel match

Source: Codex, GPPDiscovery2 `research/` (bridge copy through `59bf0a2`):
* `2026-09-27_antipodal_phase_two_channel_completion.md`;
* `2026-09-27_trivial_zeros_as_k0_spectral_cancellation.md` §§1–2 (the arithmetic part);
* `2026-09-27_su11_k0_k1_two_archimedean_positivities.md` (the trace identity);
* `2026-09-27_archimedean_jacobi_same_su11_prime_module.md` (the density identity).

## Antipodal two-channel decomposition

With `P_r(θ)` the Poisson kernel and `|r| < 1`:
* `anomalous_antipodal`: `A(r) = ¼[P_r(0) − P_r(π)] = r/(1 − r²)`;
* `normal_antipodal`: `C(r) = ¼[P_r(0) + P_r(π) − 2] = r²/(1 − r²)`;
* `sinh_weight_antipodal`: `ℓ/sinh ℓ = (ℓ/2)[P_{e^{−ℓ}}(0) − P_{e^{−ℓ}}(π)]` for `ℓ > 0`, hence the
  Archimedean weight `P(λ) = πλ/sinh(πλ)` at `ℓ = πλ`;
* `antipodal_ratio`: `P_r(π)/P_r(0) = q(r)²` with `q = (1−r)/(1+r)`;
* `negativity_log`: `½ log(P_r(0)/P_r(π)) = 2 artanh r`, the pure-state logarithmic negativity.

## Trivial zeros as a ladder

`A_triv = 2K_0 + 3/2` has spectrum `2(n + ½) + 3/2 = 2n + 5/2` (`triv_spec`), and these are
exactly the points where `Γ(5/4 + z/2)` has its poles, `z = −(2n + 5/2)` (`triv_pole`).
`xi_eq_gamma` proves the note's form of the completed function
`ξ(s) = (s − 1) π^{−s/2} Γ(1 + s/2) ζ(s)` for `Re s > 0`, where `ξ(s) = s(s−1)/2 · Λ(s)`.

## Trace and density identities

* `heat_trace_plancherel`: `P(x/π)/(2x) = 1/(2 sinh x) = Tr e^{−2xK_0}`;
* `plancherel_density`: `(2/π) · P(x) = 2x/sinh(πx)`, the vacuum spectral density of
  `K_1^{tot}`.

## Checks

All identities were verified by hand against the notes; no corrections. As the notes say, the
zeta-regularized determinant statement `Γ(5/4 + z/2) ∝ det_ζ(A_triv + z)^{-1}` is not proved here
(only the pole/spectrum match is). Note also that the equality of the two Casimir values `−¼` is
a numerical coincidence of Casimir eigenvalues, not an equivalence of representations; the notes
state this.

## Scope

Closed-form real/complex identities. **Not formalized:** the Fourier transform of `sech`, the
convolution `sech * sech`, zeta-regularized determinants, the zero-counting statement
`N_0(γ_n) = n − ½`, and the resolvent-trace Gram form `𝔇_q(a,b)`. No RH claim.
-/

open GppSU11Prime

namespace GppSU11LocalCovariance

theorem anomalous_antipodal (r : ℝ) (hr : |r| < 1) :
    (1 / 4) * (poisson r 0 - poisson r Real.pi) = r / (1 - r ^ 2) := by
  have h1 := one_sub_ne r hr
  have h2 := one_add_ne r hr
  rw [poisson_zero r hr, poisson_pi r hr]
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]; field_simp; ring

theorem normal_antipodal (r : ℝ) (hr : |r| < 1) :
    (1 / 4) * (poisson r 0 + poisson r Real.pi - 2) = r ^ 2 / (1 - r ^ 2) := by
  have h1 := one_sub_ne r hr
  have h2 := one_add_ne r hr
  rw [poisson_zero r hr, poisson_pi r hr]
  have h3 : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h3]; field_simp; ring

/-- **The `sinh` weight is the antipodal difference.** -/
theorem sinh_weight_antipodal (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ℓ / Real.sinh ℓ =
      (ℓ / 2) * (poisson (Real.exp (-ℓ)) 0 - poisson (Real.exp (-ℓ)) Real.pi) := by
  have hr : |Real.exp (-ℓ)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs : 0 < Real.sinh ℓ := Real.sinh_pos_iff.mpr hℓ
  have h := anomalous_antipodal _ hr
  have e : poisson (Real.exp (-ℓ)) 0 - poisson (Real.exp (-ℓ)) Real.pi =
      4 * (Real.exp (-ℓ) / (1 - Real.exp (-ℓ) ^ 2)) := by linarith
  rw [e]
  have h4 : Real.exp (-ℓ) / (1 - Real.exp (-ℓ) ^ 2) = 1 / (2 * Real.sinh ℓ) := by
    have hu : 1 < Real.exp ℓ := Real.one_lt_exp_iff.mpr hℓ
    have hu0 : Real.exp ℓ ≠ 0 := (Real.exp_pos _).ne'
    have hu2 : Real.exp ℓ ^ 2 - 1 ≠ 0 := by nlinarith
    have hu3 : Real.exp ℓ - (Real.exp ℓ)⁻¹ ≠ 0 := by
      intro h0
      apply hu2
      field_simp at h0
      linarith
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp
  rw [h4]
  field_simp
  norm_num

theorem antipodal_ratio (r : ℝ) (hr : |r| < 1) :
    poisson r Real.pi / poisson r 0 = ((1 - r) / (1 + r)) ^ 2 := by
  have h1 := one_sub_ne r hr
  have h2 := one_add_ne r hr
  rw [poisson_zero r hr, poisson_pi r hr]
  field_simp

/-- **Pure-state logarithmic negativity.** `½ log(P_r(0)/P_r(π)) = 2 artanh r`. -/
theorem negativity_log (r : ℝ) (hr : |r| < 1) :
    (1 / 2) * Real.log (poisson r 0 / poisson r Real.pi) = 2 * Real.artanh r := by
  have hm := mem_Ioo_of_abs r hr
  have h1 : 0 < 1 - r := by linarith [hm.2]
  have h2 : 0 < 1 + r := by linarith [hm.1]
  rw [poisson_zero r hr, poisson_pi r hr, Real.artanh_eq_half_log ⟨hm.1.le, hm.2.le⟩]
  have e : (1 + r) / (1 - r) / ((1 - r) / (1 + r)) = ((1 + r) / (1 - r)) ^ 2 := by
    field_simp
  rw [e, Real.log_pow]
  push_cast
  ring

/-- `A_triv = 2 K_0 + 3/2` has spectrum `2n + 5/2`. -/
theorem triv_spec (n : ℕ) : 2 * ((n : ℝ) + 1 / 2) + 3 / 2 = 2 * n + 5 / 2 := by ring

/-- `Γ(5/4 + z/2)` has its poles exactly at `z = −(2n + 5/2)`, i.e. where `5/4 + z/2 = −n`. -/
theorem triv_pole (n : ℕ) (z : ℂ) : (5 / 4 : ℂ) + z / 2 = -(n : ℂ) ↔ z = -(2 * n + 5 / 2) := by
  constructor
  · intro h; linear_combination (2 : ℂ) * h
  · intro h; linear_combination (1 / 2 : ℂ) * h

/-- **The completed function in Γ(1 + s/2) form.** For `Re s > 0`:
`ξ(s) = (s − 1) π^{−s/2} Γ(1 + s/2) ζ(s)` with `ξ(s) = s(s−1)/2 · Λ(s)`. -/
theorem xi_eq_gamma (s : ℂ) (hs : 0 < s.re) :
    GppFourComponentRigidity.xi s =
      (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (1 + s / 2) * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  unfold GppFourComponentRigidity.xi
  rw [GppCriticalBPYCoercivity.completed_eq_Gammaℝ_mul hs, Complex.Gammaℝ_def,
    add_comm 1 (s / 2), Complex.Gamma_add_one _ hs2]
  ring

/-- **Heat trace equals the Plancherel weight.** `P(x/π)/(2x) = 1/(2 sinh x)` for `x > 0`,
where `P(λ) = πλ/sinh(πλ)`. -/
theorem heat_trace_plancherel (x : ℝ) (hx : 0 < x) :
    (Real.pi * (x / Real.pi) / Real.sinh (Real.pi * (x / Real.pi))) / (2 * x) =
      1 / (2 * Real.sinh x) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  rw [mul_div_cancel₀ _ hpi]
  field_simp

/-- **Vacuum spectral density of `K_1^{tot}`.** `(2/π) · πx/sinh(πx) = 2x/sinh(πx)`. -/
theorem plancherel_density (x : ℝ) :
    (2 / Real.pi) * (Real.pi * x / Real.sinh (Real.pi * x)) = 2 * x / Real.sinh (Real.pi * x) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end GppSU11LocalCovariance
