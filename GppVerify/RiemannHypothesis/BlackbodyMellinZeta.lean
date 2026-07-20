import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex

/-!
# The Mellin transform of the Planck/Bose–Einstein kernel is `Γ(s)·ζ(s)`

Prompted by a re-read of the Golden Physics Project's black-body-radiation paper
(`blackbody_law_qg_dtoupin_v1.tex`), which states that "the Riemann zeta function is
[a] full Mellin transform" of a thermal partition-function kernel, and asks whether
this Mellin/zeta identification is genuinely real. It is: this is the classical route
(going back to Riemann's own 1859 paper, via the closely related Jacobi
theta-function identity that Mathlib's `completedRiemannZeta` is built from) by which
the zeta function arises as the Mellin transform of the Bose–Einstein occupation
kernel `1/(e^t - 1)` — the same kernel that gives Planck's law of black-body
radiation once multiplied by a mode-density factor and integrated.

## What this file proves

`planckKernel t := (e^t - 1)⁻¹`, the partition function of a single harmonic
oscillator's excited-state occupation numbers (`Σ_{n≥1} e^{-nt}`, the classical
Bose–Einstein sum with the zero-point term omitted). `mellin_planckKernel_eq` proves,
for `Re s > 1`,
```
  mellin planckKernel s = Γ(s) · ζ(s).
```
This is exactly the "Mellin transform of the thermal kernel is the zeta function"
statement, in its cleanest (undecorated) form — the black-body paper's own kernel
`κ(t)` additionally restricts to odd frequencies (giving the Euler-factor-at-2-removed
variant `(1-2^{-s})Γ(s)ζ(s)`), a straightforward corollary obtained by subtracting the
even-frequency sub-series `planckKernel (2t)`, not pursued here.

The proof is a direct instance of Mathlib's already-general abstract machinery
`hasSum_mellin` (`Mathlib.NumberTheory.LSeries.MellinEqDirichlet`): given a kernel that
is a sum of decaying exponentials `Σᵢ aᵢ·e^{-pᵢt}`, its Mellin transform is `Γ(s)`
times the associated Dirichlet series `Σᵢ aᵢ/pᵢˢ`. Here `aᵢ = 1`, `pᵢ = i+1`, so the
Dirichlet series is exactly `ζ(s)` (`zeta_eq_tsum_one_div_nat_add_one_cpow`).

## Physics connection (not formalized further here)

Planck's law itself is `mellin` applied with an extra factor of `t^{d-1}` for the
mode-density measure in `d` spatial dimensions; the black-body paper's
Stefan–Boltzmann-law slice `∫ t^3 n_B(t) dt = Γ(4)ζ(4) = π^4/15` (already formalized
in this repo, Thread P) is the `d=4`, `s=4` instance of exactly the same
`mellin`/Dirichlet-series correspondence proved here in general.
-/

namespace GppRH

open Complex

/-- The Bose–Einstein / Planck thermal-occupation kernel `1/(e^t - 1)` (the partition
function, with the zero-point energy convention omitted), as a complex-valued function
of `t : ℝ`. -/
noncomputable def planckKernel (t : ℝ) : ℂ := ((Real.exp t - 1 : ℝ) : ℂ)⁻¹

/-- For `t > 0`, the Planck kernel is the sum over excited states of a single harmonic
oscillator, `Σ_{n≥0} e^{-(n+1)t}`. -/
theorem hasSum_exp_planckKernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => ((Real.exp (-(↑n + 1) * t) : ℝ) : ℂ)) (planckKernel t) := by
  set r : ℝ := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hterm : ∀ n : ℕ, ((Real.exp (-(↑n + 1) * t) : ℝ) : ℂ) = (r : ℂ) * (r : ℂ) ^ n := by
    intro n
    have hpow : Real.exp (-(↑n + 1) * t) = r ^ (n + 1) := by
      have heq : -(↑n + 1) * t = (↑(n + 1) : ℝ) * (-t) := by push_cast; ring
      rw [hr, heq, Real.exp_nat_mul]
    rw [hpow]
    push_cast
    rw [pow_succ']
  simp_rw [hterm]
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact hr1
  have hgeom := hasSum_geometric_of_norm_lt_one hnorm
  have hmul := hgeom.mul_left (r : ℂ)
  have he0 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have he1 : Real.exp t - 1 ≠ 0 := by
    have : (1 : ℝ) < Real.exp t := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr ht
    linarith
  have hreal : r * (1 - r)⁻¹ = (Real.exp t - 1)⁻¹ := by
    rw [hr, Real.exp_neg]
    field_simp
  have halg : (r : ℂ) * (1 - (r : ℂ))⁻¹ = planckKernel t := by
    rw [planckKernel]
    exact_mod_cast hreal
  rwa [halg] at hmul

/-- **The Mellin transform of the Planck kernel is `Γ(s)·ζ(s)`.** -/
theorem mellin_planckKernel_eq {s : ℂ} (hs : 1 < s.re) :
    mellin planckKernel s = Complex.Gamma s * riemannZeta s := by
  have hp : ∀ n : ℕ, (1 : ℂ) = 0 ∨ 0 < (↑n + 1 : ℝ) := fun n => Or.inr (by positivity)
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (1 : ℂ) * ((Real.exp (-(↑n + 1) * t) : ℝ) : ℂ)) (planckKernel t) := by
    intro t ht
    simpa using hasSum_exp_planckKernel ht
  have h_sum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / (↑n + 1 : ℝ) ^ s.re := by
    have h0 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s.re :=
      Real.summable_one_div_nat_rpow.mpr hs
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s.re) 1).mpr h0
    simpa using h1
  have key := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun n : ℕ => (n : ℝ) + 1)
    (F := planckKernel) (s := s) hp hs0 hF h_sum
  have hcsummable : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    have h0 : Summable fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) 1).mpr h0
    simpa using h1
  have hzeta : HasSum (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    have hts := hcsummable.hasSum
    rwa [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hts
  have hzeta' := hzeta.mul_left (Complex.Gamma s)
  have heq : (fun n : ℕ => Complex.Gamma s * (1 : ℂ) / (↑n + 1 : ℝ) ^ s) =
      (fun n : ℕ => Complex.Gamma s * ((1 : ℂ) / ((n : ℂ) + 1) ^ s)) := by
    funext n
    push_cast
    ring
  rw [heq] at key
  exact key.unique hzeta'

end GppRH
