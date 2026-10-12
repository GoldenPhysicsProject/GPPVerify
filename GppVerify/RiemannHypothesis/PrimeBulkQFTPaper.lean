import GppVerify.RiemannHypothesis.PrimeBulkFreeField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The arithmetic free bulk QFT paper: remaining exact theorems

Source: Codex / Daniel Toupin, "An exact arithmetic free quantum field theory: prime Fock
sectors, a mass gap, and bulk–boundary reconstruction" (draft, 2026-10-11, six pages), together
with GPP-bridge `work/codex/2026-10-11_arithmetic_prime_bulk_boundary_qft_mass_gap.md`.
`GppPrimeBulkFreeField` already certifies the one-particle gap, the Gibbs Cauchy–Schwarz split,
the boundary-to-bulk ratio, the scale no-gap theorem, gaplessness of the orientation generator
near `0⁺`, and the Theorem 10.21 correction. `GppNoGo.TwirlNotCollapse` certifies the §8
Haar-twirl counterexample.

This file adds the following.

* `energy_eq_log` (Thm 2.1): for `n ≥ 1`, `Σ_p v_p(n)·log p = log n`. The prime-Fock
  occupation numbers `r_p = v_p(n)` have second-quantized energy exactly `log n`.
* `sum_hamiltonian_gap` and `sum_gap_attained` (Thm 6.1): `H_sum|n,m⟩ = log(nm)|n,m⟩`
  is `≥ log 2` off the vacuum `(1,1)`, with equality at `(2,1)`.
* `orientation_spectrum_dense` (Thm 6.1): the eigenvalues `log(n/m)` of
  `K = H₀⊗1 − 1⊗H₀` are dense in `ℝ`. So `spec K = ℝ`, being the closure of the eigenvalues
  of a diagonal self-adjoint operator.
* `green_ode`, `green_neumann_zero` and `green_neumann_L` (§4): for `x > y` the Neumann Green
  function `G(x,y) = cosh(κy) cosh(κ(L−x))/(κ sinh κL)` satisfies `−∂ₓ²G + κ²G = 0` and
  `∂ₓG = 0` at `x = L`. The mirror statement holds at `x = 0` for `x < y`.
* `uv_scaling` (Thm 5.1, UV half): for `a > 1/2` and `L > 0`, the boundary spectral function
  `Ĉ_B(ν) = Σ_p p^{−2a} coth(Lκ_p)/κ_p` satisfies `ν·Ĉ_B(ν) → Σ_p p^{−2a}` as `ν → ∞`, summed
  over **all** primes. The proof is dominated convergence, with the bound
  `coth y ≤ 1 + 1/y`.

Not formalized here: the IR limit of Thm 5.1 (dominated convergence over all primes **and**
modes), the trace-class/KMS statement of Prop. 2.3, and the Gaussian Wick/OS structure. All
were audited and are correct. Scope: this is a **free** theory. Its gap `log 2` is the lightest
prime mass. It is not a Yang–Mills mass gap, not a CFT (no Ward identities or OPE), and makes
no RH claim.
-/

namespace GppPrimeBulkQFTPaper

open Real

/-- **Prime-Fock energy.** The occupation numbers `v_p(n)` carry energy `Σ_p v_p(n) log p = log n`. -/
theorem energy_eq_log {n : ℕ} (hn : n ≠ 0) :
    (n.factorization.sum fun p r => (r : ℝ) * Real.log p) = Real.log n := by
  have hprod : ((n.factorization.prod fun p k => p ^ k : ℕ) : ℝ) = n := by
    rw [Nat.prod_factorization_pow_eq_self hn]
  rw [← hprod, Nat.cast_finsuppProd, Finsupp.prod, Real.log_prod, Finsupp.sum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    rw [Nat.support_factorization] at hp
    exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- **Doubled sum Hamiltonian gap.** For `n, m ≥ 1` not both `1`, `log(nm) ≥ log 2`. -/
theorem sum_hamiltonian_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : ¬(n = 1 ∧ m = 1)) :
    Real.log 2 ≤ Real.log ((n : ℝ) * m) := by
  apply Real.log_le_log (by norm_num)
  have h2 : 2 ≤ n * m := by
    by_contra h
    have : n * m = 1 := by
      have : 1 ≤ n * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    exact hnm ⟨Nat.dvd_one.mp ⟨m, this.symm⟩, Nat.dvd_one.mp ⟨n, by rw [mul_comm]; exact this.symm⟩⟩
  exact_mod_cast h2

theorem sum_gap_attained : Real.log ((2 : ℕ) * (1 : ℕ) : ℝ) = Real.log 2 := by norm_num

/-- **The orientation spectrum is dense in `ℝ`.** For every `r` and `ε > 0` there are
`n, m ≥ 1` with `|log(n/m) − r| < ε`. -/
theorem orientation_spectrum_dense (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ |Real.log ((n : ℝ) / m) - r| < ε := by
  -- `log` is continuous at `exp r`; approximate `exp r` by a positive rational `n/m`
  have hcont : ContinuousAt Real.log (Real.exp r) :=
    Real.continuousAt_log (Real.exp_pos r).ne'
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont ε hε
  set δ' := min δ (Real.exp r / 2)
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.exp r - δ' < Real.exp r + δ' by linarith)
  have hqpos : (0 : ℝ) < q := by
    have : δ' ≤ Real.exp r / 2 := min_le_right _ _
    linarith [Real.exp_pos r]
  have hq0 : 0 < q := by exact_mod_cast hqpos
  refine ⟨q.num.natAbs, q.den, ?_, q.den_pos, ?_⟩
  · have := Rat.num_pos.mpr hq0; omega
  · have hnum : ((q.num.natAbs : ℕ) : ℝ) = (q.num : ℝ) := by
      have := Rat.num_pos.mpr hq0
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast this)]
    have hq : ((q.num.natAbs : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      rw [hnum, Rat.cast_def]
    rw [hq, ← Real.log_exp r]
    have hdist : dist (q : ℝ) (Real.exp r) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left δ (Real.exp r / 2)]
    have := hball hdist
    rw [Real.dist_eq] at this
    exact this

/-- The Neumann Green function on the branch `x > y` (as a function of `x`). -/
noncomputable def greenR (κ L y x : ℝ) : ℝ :=
  Real.cosh (κ * y) * Real.cosh (κ * (L - x)) / (κ * Real.sinh (κ * L))

lemma hasDerivAt_greenR (κ L y x : ℝ) :
    HasDerivAt (greenR κ L y)
      (-(κ * (Real.cosh (κ * y) * Real.sinh (κ * (L - x))) / (κ * Real.sinh (κ * L)))) x := by
  have h1 : HasDerivAt (fun x => κ * (L - x)) (-κ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).const_mul κ
  have h2 := (Real.hasDerivAt_cosh (κ * (L - x))).comp x h1
  have h3 := (h2.const_mul (Real.cosh (κ * y))).div_const (κ * Real.sinh (κ * L))
  simp only [Function.comp_def] at h3
  exact h3.congr_deriv (by ring)

lemma hasDerivAt_greenR' (κ L y x : ℝ) :
    HasDerivAt (fun x => -(κ * (Real.cosh (κ * y) * Real.sinh (κ * (L - x))) /
        (κ * Real.sinh (κ * L))))
      (κ ^ 2 * greenR κ L y x) x := by
  have h1 : HasDerivAt (fun x => κ * (L - x)) (-κ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).const_mul κ
  have h2 := (Real.hasDerivAt_sinh (κ * (L - x))).comp x h1
  have h3 := (((h2.const_mul (Real.cosh (κ * y))).const_mul κ).div_const
    (κ * Real.sinh (κ * L))).neg
  simp only [Function.comp_def] at h3
  exact h3.congr_deriv (by unfold greenR; ring)

/-- **Field equation.** On `x > y`, `−∂ₓ²G + κ²G = 0`. -/
theorem green_ode (κ L y x : ℝ) :
    -deriv (deriv (greenR κ L y)) x + κ ^ 2 * greenR κ L y x = 0 := by
  have hd : deriv (greenR κ L y) = fun x =>
      -(κ * (Real.cosh (κ * y) * Real.sinh (κ * (L - x))) / (κ * Real.sinh (κ * L))) :=
    funext fun x => (hasDerivAt_greenR κ L y x).deriv
  rw [hd, (hasDerivAt_greenR' κ L y x).deriv]
  ring

/-- **Neumann condition at `x = L`.** -/
theorem green_neumann_L (κ L y : ℝ) : deriv (greenR κ L y) L = 0 := by
  rw [(hasDerivAt_greenR κ L y L).deriv]
  simp

/-- The Neumann Green function on the branch `x < y` (as a function of `x`). -/
noncomputable def greenL (κ L y x : ℝ) : ℝ :=
  Real.cosh (κ * x) * Real.cosh (κ * (L - y)) / (κ * Real.sinh (κ * L))

/-- **Neumann condition at `x = 0`.** -/
theorem green_neumann_zero (κ L y : ℝ) : deriv (greenL κ L y) 0 = 0 := by
  have h : HasDerivAt (greenL κ L y)
      (Real.sinh (κ * 0) * κ * Real.cosh (κ * (L - y)) / (κ * Real.sinh (κ * L))) 0 := by
    unfold greenL
    have h1 := ((Real.hasDerivAt_cosh (κ * 0)).comp 0 ((hasDerivAt_id 0).const_mul κ))
    have h2 := (h1.mul_const (Real.cosh (κ * (L - y)))).div_const (κ * Real.sinh (κ * L))
    simp only [Function.comp_def] at h2
    exact h2.congr_deriv (by ring)
  rw [h.deriv]
  simp

/-! ### The UV boundary scaling law (§5) -/

open Filter Topology

/-- `coth y = cosh y / sinh y`. -/
noncomputable def coth (y : ℝ) : ℝ := Real.cosh y / Real.sinh y

lemma coth_eq {y : ℝ} (hy : 0 < y) : coth y = 1 + 2 / (Real.exp (2 * y) - 1) := by
  have he : 1 < Real.exp (2 * y) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (2 * y) = Real.exp y ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hy' : 0 < Real.exp y := Real.exp_pos y
  have hs : Real.exp y - Real.exp (-y) ≠ 0 := by
    have : Real.exp (-y) < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
    linarith
  unfold coth
  rw [Real.cosh_eq, Real.sinh_eq, h2, Real.exp_neg]
  have h3 : Real.exp y ^ 2 - 1 ≠ 0 := by rw [← h2]; linarith
  field_simp
  ring

lemma coth_le {y : ℝ} (hy : 0 < y) : coth y ≤ 1 + 1 / y := by
  rw [coth_eq hy]
  have he : 2 * y ≤ Real.exp (2 * y) - 1 := by linarith [Real.add_one_le_exp (2 * y)]
  have : 2 / (Real.exp (2 * y) - 1) ≤ 1 / y := by
    rw [div_le_div_iff₀ (by linarith) hy]; linarith
  linarith

lemma coth_pos {y : ℝ} (hy : 0 < y) : 0 < coth y := by
  rw [coth_eq hy]
  have : 0 < Real.exp (2 * y) - 1 := by
    have : 1 < Real.exp (2 * y) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  positivity

lemma tendsto_coth : Tendsto coth atTop (𝓝 1) := by
  have hexp : Tendsto (fun y : ℝ => Real.exp (2 * y) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have h0 : Tendsto (fun y : ℝ => 2 / (Real.exp (2 * y) - 1)) atTop (𝓝 0) := by
    have := hexp.inv_tendsto_atTop.const_mul (2 : ℝ)
    rw [mul_zero] at this
    refine this.congr fun y => ?_
    simp [div_eq_mul_inv]
  have h : Tendsto (fun y : ℝ => 1 + 2 / (Real.exp (2 * y) - 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  exact (coth_eq hy).symm

/-- `κ_p(ν) = √(ν² + m²)`. -/
noncomputable def kap (m ν : ℝ) : ℝ := Real.sqrt (ν ^ 2 + m ^ 2)

lemma le_kap (m : ℝ) {ν : ℝ} (hν : 0 ≤ ν) : ν ≤ kap m ν := by
  unfold kap
  calc ν = Real.sqrt (ν ^ 2) := (Real.sqrt_sq hν).symm
    _ ≤ Real.sqrt (ν ^ 2 + m ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m])

lemma kap_le (m : ℝ) {ν : ℝ} (hν : 0 ≤ ν) : kap m ν ≤ ν + |m| := by
  unfold kap
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs m, abs_nonneg m]

lemma tendsto_div_kap (m : ℝ) : Tendsto (fun ν => ν / kap m ν) atTop (𝓝 1) := by
  have hlow : Tendsto (fun ν : ℝ => ν / (ν + |m|)) atTop (𝓝 1) := by
    have h : Tendsto (fun ν : ℝ => 1 - |m| / (ν + |m|)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub ((tendsto_atTop_add_const_right _ _ tendsto_id).const_div_atTop _
        |>.congr fun _ => rfl)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ν hν
    have : ν + |m| ≠ 0 := by positivity
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with ν hν
    have hk : 0 < kap m ν := lt_of_lt_of_le hν (le_kap m hν.le)
    exact div_le_div_of_nonneg_left hν.le hk (kap_le m hν.le)
  · filter_upwards [eventually_gt_atTop 0] with ν hν
    have hk : 0 < kap m ν := lt_of_lt_of_le hν (le_kap m hν.le)
    rw [div_le_one hk]; exact le_kap m hν.le

/-- The boundary spectral function `Ĉ_B(ν) = Σ_p p^{−2a} coth(Lκ_p)/κ_p`. -/
noncomputable def CB (a L ν : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 * a) * coth (L * kap (Real.log p) ν) / kap (Real.log p) ν

/-- **UV boundary scaling law.** For `a > 1/2` and `L > 0`,
`ν · Ĉ_B(ν) → Σ_p p^{−2a}` as `ν → ∞`. -/
theorem uv_scaling {a L : ℝ} (ha : 1 / 2 < a) (hL : 0 < L) :
    Tendsto (fun ν => ν * CB a L ν) atTop (𝓝 (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 * a))) := by
  have hsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 * a)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hrw : (fun ν => ν * CB a L ν) = fun ν => ∑' p : Nat.Primes,
      ν * (((p : ℕ) : ℝ) ^ (-2 * a) * coth (L * kap (Real.log p) ν) / kap (Real.log p) ν) := by
    funext ν; unfold CB; rw [tsum_mul_left]
  rw [hrw]
  refine tendsto_tsum_of_dominated_convergence (bound := fun p : Nat.Primes =>
    ((p : ℕ) : ℝ) ^ (-2 * a) * (1 + 1 / L)) (hsum.mul_right _) (fun p => ?_) ?_
  · -- per-prime limit
    set m := Real.log ((p : ℕ) : ℝ)
    have hk : Tendsto (fun ν => kap m ν) atTop atTop :=
      tendsto_atTop_mono' atTop (eventually_ge_atTop 0 |>.mono fun ν hν => le_kap m hν)
        tendsto_id
    have hc : Tendsto (fun ν => coth (L * kap m ν)) atTop (𝓝 1) :=
      tendsto_coth.comp (hk.const_mul_atTop hL)
    have h := ((tendsto_div_kap m).mul hc).const_mul (((p : ℕ) : ℝ) ^ (-2 * a))
    rw [mul_one, mul_one] at h
    refine h.congr' ?_
    filter_upwards with ν
    ring
  · -- uniform bound for ν ≥ 1
    filter_upwards [eventually_ge_atTop 1] with ν hν p
    set m := Real.log ((p : ℕ) : ℝ)
    have hν0 : 0 < ν := by linarith
    have hk : 0 < kap m ν := lt_of_lt_of_le hν0 (le_kap m hν0.le)
    have hkν : ν ≤ kap m ν := le_kap m hν0.le
    have hp : 0 < ((p : ℕ) : ℝ) ^ (-2 * a) := Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
    have hLk : 0 < L * kap m ν := mul_pos hL hk
    have hcoth := coth_le hLk
    have hcpos := coth_pos hLk
    have h1 : 1 / (L * kap m ν) ≤ 1 / L := by
      rw [div_le_div_iff₀ hLk hL]; nlinarith
    have hratio : ν / kap m ν ≤ 1 := by rw [div_le_one hk]; exact hkν
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ν * (((p : ℕ) : ℝ) ^ (-2 * a) * coth (L * kap m ν) / kap m ν)
        = ((p : ℕ) : ℝ) ^ (-2 * a) * ((ν / kap m ν) * coth (L * kap m ν)) := by ring
      _ ≤ ((p : ℕ) : ℝ) ^ (-2 * a) * (1 * (1 + 1 / L)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hratio (by linarith) hcpos.le zero_le_one) hp.le
      _ = ((p : ℕ) : ℝ) ^ (-2 * a) * (1 + 1 / L) := by ring

end GppPrimeBulkQFTPaper
