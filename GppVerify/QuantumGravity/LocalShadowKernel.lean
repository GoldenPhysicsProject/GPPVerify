import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Archimedean local shadow kernel `K_{∞,d}(a) = Γ(a)Γ(d-a)/Γ(d)`

From "Local-field shadow kernels, celestial unitarity, and the adelic principal series"
(Toupin, 2026), §1 and §12. `K_{∞,d}` is the closed form (Beta function) of the divergent
integral `∫₀^∞ x^(a-1)/(1+x)^d dx` on its strip of convergence `0 < Re(a) < d`, extended by
meromorphic continuation of `Γ`. This file formalizes the two structural facts stated for it
that hold unconditionally and do not depend on any claim about the Riemann Hypothesis, the
celestial/automorphic bridge, or any other part of the paper's open research program:
shadow reflection, and positivity on the principal series line `a = d/2 + it`.

Not formalized here: the integral representation itself (`∫₀^∞ x^(a-1)/(1+x)^d dx =
Γ(a)Γ(d-a)/Γ(d)`) is taken as the definition rather than derived from Mathlib's `[0,1]`-form
Beta integral via the substitution `x = t/(1-t)` — a real but separate piece of work, not
attempted this round. The `d=1` (dispersion) and `d=2` (celestial Cutkosky cut)
specializations, and the non-Archimedean analogue `K_{q,d}`, are documented in
`discovery/local_field_shadow/local_shadow_kernel_notes.md` together with the honest boundary
of what is and is not established about the local-to-global bridge to automorphic forms.
-/

namespace GppLocalShadow

open Complex ComplexConjugate Real

/-- The Archimedean shadow kernel `K_{∞,d}(a) = Γ(a)Γ(d-a)/Γ(d)`. -/
noncomputable def archKernel (d : ℝ) (a : ℂ) : ℂ :=
  Complex.Gamma a * Complex.Gamma ((d : ℂ) - a) / Complex.Gamma (d : ℂ)

/-- **Shadow reflection**: `K_{∞,d}(a) = K_{∞,d}(d-a)`. -/
theorem archKernel_reflection (d : ℝ) (a : ℂ) :
    archKernel d a = archKernel d ((d : ℂ) - a) := by
  unfold archKernel
  rw [mul_comm, show (d : ℂ) - ((d : ℂ) - a) = a from by ring]

/-- On the principal series `a = d/2 + it`, `d - a` is the complex conjugate of `a`. -/
theorem archKernel_shadow_eq_conj (d t : ℝ) :
    (d : ℂ) - ((d : ℂ) / 2 + (t : ℂ) * Complex.I)
      = conj ((d : ℂ) / 2 + (t : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.div_re, Complex.div_im] <;> ring

/-- **Principal-series positivity**: on `a = d/2 + it` (`d > 0`), `K_{∞,d}(a)` is the positive
    real number `|Γ(d/2+it)|²/Γ(d)`, cast into `ℂ`. Shadow reflection becomes Hermitian
    conjugation exactly on this line. -/
theorem archKernel_principal_series (d : ℝ) (t : ℝ) :
    archKernel d ((d : ℂ) / 2 + (t : ℂ) * Complex.I)
      = ((Complex.normSq (Complex.Gamma ((d : ℂ) / 2 + (t : ℂ) * Complex.I))
          / Real.Gamma d : ℝ) : ℂ) := by
  unfold archKernel
  rw [archKernel_shadow_eq_conj, Complex.Gamma_conj, Complex.mul_conj, Complex.Gamma_ofReal]
  push_cast
  ring

/-- Consequently `K_{∞,d}(d/2+it) > 0` as a real number, whenever `Γ(d/2+it) ≠ 0` (true for
    every `d > 0`, `t : ℝ`, since `d/2 + it` is never a nonpositive integer). -/
theorem archKernel_principal_series_pos (d : ℝ) (hd : 0 < d) (t : ℝ)
    (hne : Complex.Gamma ((d : ℂ) / 2 + (t : ℂ) * Complex.I) ≠ 0) :
    0 < (archKernel d ((d : ℂ) / 2 + (t : ℂ) * Complex.I)).re := by
  rw [archKernel_principal_series d t]
  simp only [Complex.ofReal_re]
  have hGpos : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  have hnormSq : 0 < Complex.normSq (Complex.Gamma ((d : ℂ) / 2 + (t : ℂ) * Complex.I)) :=
    Complex.normSq_pos.mpr hne
  positivity

/-! ## The `d=2` cut vs. the spherical Weyl coefficient: distinct objects, exact decomposition

From the research-front update (2026-08-22, relayed from Daniel's own follow-up work): the
naive §9 conjecture — that a single local factor `a_∞(s)` gives *both* the physical kernel
`C_∞(s) := a_∞(s)a_∞(1-s)` *and* the normalized Weyl/Gindikin–Karpelevich intertwiner
`M_∞(s) := a_∞(1-s)/a_∞(s)` — is false, and the failure is itself the informative structural
fact: the two are distinct canonical objects attached to the same rank-one principal series.
This section formalizes the exact relation the celestial `d=2` cut *does* satisfy: it
decomposes, via Legendre's duplication formula, into a product of two shadow-paired real
Archimedean Gamma factors `Γ_R`. `archWeylCoeff` is recorded for contrast only — no identity
relating it to `archKernel` is claimed or provable, and none is proved here. -/

/-- The real Archimedean Gamma factor `Γ_R(s) = π^{-s/2}Γ(s/2)`. -/
noncomputable def GammaR (s : ℂ) : ℂ := (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The complex Archimedean Gamma factor `Γ_C(s) = 2(2π)^{-s}Γ(s)`. -/
noncomputable def GammaC (s : ℂ) : ℂ := 2 * ((2 : ℂ) * (π : ℂ)) ^ (-s) * Complex.Gamma s

/-- Splits `(2π)^{-w}` into `2^{-w}·π^{-w}`: the two-numeral-cast bridge every proof below
    needs, isolated once so `mul_cpow_ofReal_nonneg` (stated for `((a:ℝ):ℂ)`-cast bases) can
    fire without leaving a `(2:ℂ)` vs `((2:ℝ):ℂ)` mismatch for later `rw`/`ring` steps. -/
private theorem two_mul_pi_cpow_split (w : ℂ) :
    ((2 : ℂ) * (π : ℂ)) ^ w = (2 : ℂ) ^ w * (π : ℂ) ^ w := by
  have h2r : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2r, Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le, ← h2r]

/-- The Archimedean spherical Weyl / Gindikin–Karpelevich coefficient
    `c_∞(s) = √π·Γ(s-1/2)/Γ(s) = Γ_R(2s-1)/Γ_R(2s)`, recorded here for contrast with
    `archKernel` only — no relation between the two is claimed. -/
noncomputable def archWeylCoeff (s : ℂ) : ℂ :=
  GammaR (2 * s - 1) / GammaR (2 * s)

/-- **Legendre duplication for the Archimedean factors**: `Γ_C(s) = Γ_R(s)·Γ_R(s+1)`. -/
theorem GammaC_eq_GammaR_mul_GammaR_succ (s : ℂ) :
    GammaC s = GammaR s * GammaR (s + 1) := by
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have hdup := Complex.Gamma_mul_Gamma_add_half (s / 2)
  rw [show s / 2 + 1 / 2 = (s + 1) / 2 from by ring,
      show (2 : ℂ) * (s / 2) = s from by ring] at hdup
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have e1 : (π : ℂ) ^ (-s / 2) * (π : ℂ) ^ (-(s + 1) / 2) * ((Real.sqrt π : ℝ) : ℂ)
      = (π : ℂ) ^ (-s) := by
    rw [hsqrt, ← Complex.cpow_add _ _ hpi_ne, ← Complex.cpow_add _ _ hpi_ne]
    congr 1
    ring
  have e3 : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [show (1 : ℂ) - s = 1 + -s from by ring, Complex.cpow_add _ _ h2_ne, Complex.cpow_one]
  have hRHS : GammaR s * GammaR (s + 1)
      = ((π:ℂ)^(-s/2) * (π:ℂ)^(-(s+1)/2) * ((Real.sqrt π:ℝ):ℂ)) * (Complex.Gamma s * (2:ℂ)^(1-s)) := by
    unfold GammaR
    rw [show (π:ℂ)^(-s/2) * Complex.Gamma (s/2) * ((π:ℂ)^(-(s+1)/2) * Complex.Gamma ((s+1)/2))
        = ((π:ℂ)^(-s/2) * (π:ℂ)^(-(s+1)/2)) * (Complex.Gamma (s/2) * Complex.Gamma ((s+1)/2))
        from by ring, hdup]
    ring
  rw [hRHS, e1, ← e3]
  unfold GammaC
  rw [two_mul_pi_cpow_split]
  ring

/-- **The celestial `d=2` cut is a product of two `Γ_C` factors**: `K_{∞,2}(Δ) = π²·Γ_C(Δ)Γ_C(2-Δ)`.
    Pure algebra from `Γ_C`'s definition; no duplication formula needed for this step. -/
theorem archKernel_two_eq_GammaC_product (Δ : ℂ) :
    archKernel 2 Δ = (π : ℂ) ^ (2:ℕ) * GammaC Δ * GammaC (2 - Δ) := by
  have hΔ : ((2:ℝ):ℂ) - Δ = 2 - Δ := by push_cast; ring
  have h2pi_ne : ((2:ℂ) * (π:ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓ2 : Complex.Gamma ((2:ℝ):ℂ) = 1 := by
    rw [Complex.Gamma_ofReal, Real.Gamma_two]; norm_num
  have hcomb : ((2:ℂ)*(π:ℂ))^(-Δ) * ((2:ℂ)*(π:ℂ))^(-(2-Δ)) = ((2:ℂ)*(π:ℂ))^(-2:ℂ) := by
    rw [← Complex.cpow_add _ _ h2pi_ne]; congr 1; ring
  have hsplit2 : ((2:ℂ)*(π:ℂ))^(-2:ℂ) = ((2:ℂ)^(2:ℕ))⁻¹ * ((π:ℂ)^(2:ℕ))⁻¹ := by
    rw [two_mul_pi_cpow_split,
        show ((2:ℂ))^(-2:ℂ) = ((2:ℂ)^(2:ℕ))⁻¹ from by
          rw [← Complex.cpow_natCast, ← Complex.cpow_neg]; norm_num,
        show ((π:ℂ))^(-2:ℂ) = ((π:ℂ)^(2:ℕ))⁻¹ from by
          rw [← Complex.cpow_natCast, ← Complex.cpow_neg]; norm_num]
  unfold archKernel GammaC
  rw [hΔ, hΓ2]
  rw [show (π:ℂ)^(2:ℕ) * (2 * ((2:ℂ)*(π:ℂ))^(-Δ) * Complex.Gamma Δ)
        * (2 * ((2:ℂ)*(π:ℂ))^(-(2-Δ)) * Complex.Gamma (2-Δ))
      = (4 * (π:ℂ)^(2:ℕ) * Complex.Gamma Δ * Complex.Gamma (2-Δ))
        * (((2:ℂ)*(π:ℂ))^(-Δ) * ((2:ℂ)*(π:ℂ))^(-(2-Δ)))
      from by ring, hcomb, hsplit2]
  have hpi_ne2 : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi_ne2]
  ring

/-- **The celestial `d=2` cut decomposes into two shadow-paired real Archimedean sectors**:
    `K_{∞,2}(Δ) = π²·Γ_R(Δ)Γ_R(Δ+1)·Γ_R(2-Δ)Γ_R(3-Δ)` — the pair `(Γ_R(Δ), Γ_R(2-Δ))` and its
    shift `(Γ_R(Δ+1), Γ_R(3-Δ))` are the "two interlaced real Archimedean Gamma sectors". -/
theorem archKernel_two_eq_GammaR_sectors (Δ : ℂ) :
    archKernel 2 Δ
      = (π : ℂ) ^ (2:ℕ) * (GammaR Δ * GammaR (Δ + 1)) * (GammaR (2 - Δ) * GammaR (3 - Δ)) := by
  rw [archKernel_two_eq_GammaC_product, GammaC_eq_GammaR_mul_GammaR_succ,
      GammaC_eq_GammaR_mul_GammaR_succ, show (2:ℂ) - Δ + 1 = 3 - Δ from by ring]

end GppLocalShadow
