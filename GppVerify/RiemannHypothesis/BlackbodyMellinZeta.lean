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
statement, in its cleanest (undecorated) form. `mellin_oddPlanckKernel_eq` proves the
black-body paper's own kernel `κ(t) := Σ_{k≥0} e^{-(2k+1)t}` (restricting to odd
frequencies only) has Mellin transform `(1-2^{-s})Γ(s)ζ(s)` — the Euler-factor-at-2
exactly removed, matching the paper's stated identity precisely — via an even/odd
split of the geometric series (`HasSum.even_add_odd`) applied twice: once to the
kernel itself (`oddPlanckKernel t = planckKernel t - planckKernel (2t)`), once to the
Dirichlet series (`Σ_{n odd} 1/n^s = ζ(s) - 2^{-s}ζ(s)`).

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

/-- The odd-frequency Bose–Einstein kernel `κ(t) := Σ_{k≥0} e^{-(2k+1)t}`, matching the
black-body paper's own kernel exactly (the Planck kernel restricted to odd
frequencies only, i.e. with the even-frequency sub-series subtracted off). -/
noncomputable def oddPlanckKernel (t : ℝ) : ℂ := planckKernel t - planckKernel (2 * t)

/-- For `t > 0`, the odd-frequency kernel is the sum `Σ_{k≥0} e^{-(2k+1)t}`. -/
theorem hasSum_exp_oddPlanckKernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ((Real.exp (-(2 * (k : ℝ) + 1) * t) : ℝ) : ℂ)) (oddPlanckKernel t) := by
  set f : ℕ → ℂ := fun n => ((Real.exp (-(↑n + 1) * t) : ℝ) : ℂ) with hf
  have h1 : HasSum f (planckKernel t) := hasSum_exp_planckKernel ht
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    simp only at h
    omega
  have hsummable_even : Summable (fun k : ℕ => f (2 * k)) := h1.summable.comp_injective hinj
  obtain ⟨A, he⟩ := hsummable_even
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have h2 : HasSum (fun n : ℕ => ((Real.exp (-(↑n + 1) * (2 * t)) : ℝ) : ℂ)) (planckKernel (2 * t)) :=
    hasSum_exp_planckKernel h2t
  have hodd_eq : ∀ k : ℕ, f (2 * k + 1) = ((Real.exp (-(↑k + 1) * (2 * t)) : ℝ) : ℂ) := by
    intro k
    simp only [hf]
    congr 1
    push_cast
    ring_nf
  have ho : HasSum (fun k : ℕ => f (2 * k + 1)) (planckKernel (2 * t)) := by
    simpa only [hodd_eq] using h2
  have hcombined := HasSum.even_add_odd he ho
  have hAeq : A + planckKernel (2 * t) = planckKernel t := hcombined.unique h1
  have hAval : A = oddPlanckKernel t := by
    rw [oddPlanckKernel, eq_sub_iff_add_eq]
    exact hAeq
  have heven_eq : ∀ k : ℕ, f (2 * k) = ((Real.exp (-(2 * (k : ℝ) + 1) * t) : ℝ) : ℂ) := by
    intro k
    simp only [hf]
    congr 1
    push_cast
    ring_nf
  rw [← hAval]
  simpa only [heven_eq] using he

/-- **The Mellin transform of the odd-frequency kernel is `(1-2^{-s})·Γ(s)·ζ(s)`,**
matching the black-body paper's own stated identity exactly. -/
theorem mellin_oddPlanckKernel_eq {s : ℂ} (hs : 1 < s.re) :
    mellin oddPlanckKernel s = (1 - (2 : ℂ) ^ (-s)) * Complex.Gamma s * riemannZeta s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  -- The odd-indexed Dirichlet series `Σ_{k} 1/(2k+1)^s`, via the same even/odd split
  -- applied to `g n := 1/(n+1)^s`, whose full sum is `ζ(s)` (as in `mellin_planckKernel_eq`).
  set g : ℕ → ℂ := fun n => (1 : ℂ) / ((n : ℂ) + 1) ^ s with hg
  have hcsummable : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    have h0 : Summable fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) 1).mpr h0
    simpa using h1
  have hzeta : HasSum g (riemannZeta s) := by
    have hts := hcsummable.hasSum
    rwa [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at hts
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    simp only at h
    omega
  have hsummable_even : Summable (fun k : ℕ => g (2 * k)) := hzeta.summable.comp_injective hinj
  obtain ⟨B, heg⟩ := hsummable_even
  have hodd_eq : ∀ k : ℕ, g (2 * k + 1) = (2 : ℂ) ^ (-s) * g k := by
    intro k
    simp only [hg]
    have hcast : (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast,
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
      Complex.cpow_neg]
    push_cast
    field_simp
  have hog : HasSum (fun k : ℕ => g (2 * k + 1)) ((2 : ℂ) ^ (-s) * riemannZeta s) := by
    simpa only [hodd_eq] using hzeta.mul_left ((2 : ℂ) ^ (-s))
  have hcombined := HasSum.even_add_odd heg hog
  have hBeq : B + (2 : ℂ) ^ (-s) * riemannZeta s = riemannZeta s := hcombined.unique hzeta
  have hBval : B = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
    have : B = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
      rw [eq_sub_iff_add_eq]; exact hBeq
    rw [this]; ring
  have heven_eq : ∀ k : ℕ, g (2 * k) = (1 : ℂ) / (2 * (k : ℝ) + 1) ^ s := by
    intro k
    simp only [hg]
    congr 2
    push_cast
    ring
  have hoddDirichlet : HasSum (fun k : ℕ => (1 : ℂ) / (2 * (k : ℝ) + 1) ^ s)
      ((1 - (2 : ℂ) ^ (-s)) * riemannZeta s) := by
    rw [← hBval]
    simpa only [heven_eq] using heg
  have hp : ∀ k : ℕ, (1 : ℂ) = 0 ∨ 0 < (2 * (k : ℝ) + 1) := fun k => Or.inr (by positivity)
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum
      (fun k : ℕ => (1 : ℂ) * ((Real.exp (-(2 * (k : ℝ) + 1) * t) : ℝ) : ℂ)) (oddPlanckKernel t) := by
    intro t ht
    simpa using hasSum_exp_oddPlanckKernel ht
  have h_sum : Summable fun k : ℕ => ‖(1 : ℂ)‖ / (2 * (k : ℝ) + 1) ^ s.re := by
    simp only [norm_one]
    have hcomp : Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ s.re := by
      have h0 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s.re :=
        Real.summable_one_div_nat_rpow.mpr hs
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s.re) 1).mpr h0
      simpa using h1
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hcomp
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact Real.rpow_le_rpow (by positivity) (by linarith) hs0.le
  have key0 := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun k : ℕ => 2 * (k : ℝ) + 1)
    (F := oddPlanckKernel) (s := s) hp hs0 hF h_sum
  have hzeta'' := hoddDirichlet.mul_left (Complex.Gamma s)
  have key : HasSum (fun k : ℕ => Complex.Gamma s * ((1 : ℂ) / (2 * (k : ℝ) + 1) ^ s))
      (mellin oddPlanckKernel s) := by
    have heq2 : (fun i : ℕ => Complex.Gamma s * (fun _ : ℕ => (1 : ℂ)) i /
        ↑((fun k : ℕ => 2 * (k : ℝ) + 1) i) ^ s) =
        (fun k : ℕ => Complex.Gamma s * ((1 : ℂ) / (2 * (k : ℝ) + 1) ^ s)) := by
      funext k; push_cast; ring
    rwa [heq2] at key0
  have := key.unique hzeta''
  rw [this]; ring

end GppRH
