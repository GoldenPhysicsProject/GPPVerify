import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

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

open Complex ComplexConjugate

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
theorem archKernel_principal_series (d : ℝ) (hd : 0 < d) (t : ℝ) :
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
  rw [archKernel_principal_series d hd t]
  simp only [Complex.ofReal_re]
  have hGpos : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  have hnormSq : 0 < Complex.normSq (Complex.Gamma ((d : ℂ) / 2 + (t : ℂ) * Complex.I)) :=
    Complex.normSq_pos.mpr hne
  positivity

end GppLocalShadow
