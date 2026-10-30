import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Local Euler factors on the critical line: unitarity, density sign, mirror overlap

Source: Grok ("Heart of the Cosmos"), `GPPDiscovery5/derivation/ARP.md` §G.6 items 3, 4 and 6
(Lean asks for Claude Code / Codex), with the mirror overlap and Kakutani-type dichotomy due to
Astra (PR #11, Oct 26). Daniel Toupin / Golden Physics Project, with AI assistance from Grok
(statements), Astra (mirror overlap) and Claude Code (formalization).

* `norm_one_sub_cpow_conj`: `‖1 − p^{−(a+it)}‖ = ‖1 − p^{−(a−it)}‖` for `p > 0`, real `a, t`.
* `local_gamma_unitary`: at `s = ½ + it`, `|1 − p^{−s}| = |1 − p^{−(1−s)}|`, i.e. the local
  gamma factor `γ_p(s) = L_p(1−s)/L_p(s)` has modulus `1`.
* `twisted_gamma_pair_unitary`: for real `θ ≠ ±½` the product of the two twisted factors
  `γ_p^{(θ)}(s) γ_p^{(−θ)}(s)` has modulus `1` on `Re s = ½`.
* `re_div_one_sub`, `local_density_sign_pos`, `local_density_sign_neg`:
  `Re[z/(1−z)] = (Re z − |z|²)/|1−z|²`, taking both signs on `|z| = r`, `0 < r < 1`.
* `mirror_overlap_sq`: `1 − R² = (a−b)²/(1−ab)²` for `R² = (1−a²)(1−b²)/(1−ab)²`.
* `mirror_product_tendsto_zero`: for `0 < m < ½`, the partial products over primes
  `∏_{p<N} R_p²` with `a = p^{−m}`, `b = p^{−(1−m)}` tend to `0` (Kakutani-type dichotomy; uses
  `Σ_p 1/p = ∞`). `mirror_product_tendsto_zero_sigma` states it for every `σ ∈ (0,1)`, `σ ≠ ½`.

**Scope.** Finite local identities and the divergence of the mirror product only. The twisted
factor `γ_p^{(θ)}` itself being non-unimodular "in general" is not formalized (only the
pair product). The global statement that the infinite product vanishes is the limit of partial
products here; no measure-theoretic Kakutani equivalence is claimed. No claim about RH.
-/

set_option autoImplicit false

open Complex Finset Filter Topology

namespace GppARPLocalFactors

/-- Conjugation of a complex power with positive real base. -/
lemma cpow_conj_real {p : ℝ} (hp : 0 < p) (w : ℂ) :
    (starRingEnd ℂ) ((p : ℂ) ^ w) = (p : ℂ) ^ ((starRingEnd ℂ) w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  rw [← Complex.exp_conj, map_mul]
  congr 2
  rw [← Complex.ofReal_log hp.le]
  simp

/-- `‖1 − p^{−(a+it)}‖ = ‖1 − p^{−(a−it)}‖`. -/
theorem norm_one_sub_cpow_conj {p : ℝ} (hp : 0 < p) (a t : ℝ) :
    ‖1 - (p : ℂ) ^ (-((a : ℂ) + t * I))‖ = ‖1 - (p : ℂ) ^ (-((a : ℂ) - t * I))‖ := by
  have h : (1 : ℂ) - (p : ℂ) ^ (-((a : ℂ) - t * I))
      = (starRingEnd ℂ) (1 - (p : ℂ) ^ (-((a : ℂ) + t * I))) := by
    rw [map_sub, map_one, cpow_conj_real hp]
    congr 3
    simp
    ring
  rw [h, Complex.norm_conj]

/-- Local gamma factor unitary: `|1 − p^{−(½+it)}| = |1 − p^{−(½−it)}|`, so
`|γ_p(½+it)| = |1 − p^{−s}|/|1 − p^{−(1−s)}| = 1`. -/
theorem local_gamma_unitary {p : ℝ} (hp : 0 < p) (t : ℝ) :
    ‖1 - (p : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = ‖1 - (p : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + t * I)))‖ := by
  have := norm_one_sub_cpow_conj hp (1 / 2) t
  have e : (1 : ℂ) - ((1 / 2 : ℂ) + t * I) = (1 / 2 : ℝ) - t * I := by
    push_cast; ring
  rw [e]
  simpa using this

/-- Local factor `L_p(s) = (1 − p^{−s})⁻¹`. -/
noncomputable def L (p : ℝ) (s : ℂ) : ℂ := (1 - (p : ℂ) ^ (-s))⁻¹

/-- Twisted gamma factor `γ_p^{(θ)}(s) = L_p(1−s−θ)/L_p(s+θ)`. -/
noncomputable def gammaTw (p θ : ℝ) (s : ℂ) : ℂ := L p (1 - s - θ) / L p (s + θ)

/-- On `Re s = ½` the product of the `θ` and `−θ` twisted factors is unimodular, for real
`θ ≠ ±½` (so no denominator vanishes). -/
theorem twisted_gamma_pair_unitary {p : ℝ} (hp : 1 < p) (θ t : ℝ)
    (h1 : θ ≠ 1 / 2) (h2 : θ ≠ -(1 / 2)) :
    ‖gammaTw p θ (1 / 2 + t * I) * gammaTw p (-θ) (1 / 2 + t * I)‖ = 1 := by
  have hp0 : 0 < p := by linarith
  -- nonvanishing of `1 − p^{−w}` when `Re w ≠ 0`
  have nz : ∀ w : ℂ, w.re ≠ 0 → (1 : ℂ) - (p : ℂ) ^ (-w) ≠ 0 := by
    intro w hw h
    have h' : (p : ℂ) ^ (-w) = 1 := by linear_combination -h
    have h3 := congrArg (fun z : ℂ => ‖z‖) h'
    simp only [Complex.norm_cpow_eq_rpow_re_of_pos hp0, norm_one, Complex.neg_re] at h3
    rcases lt_or_gt_of_ne hw with h4 | h4
    · have : 1 < p ^ (-w.re) := Real.one_lt_rpow hp (by linarith)
      linarith
    · have : p ^ (-w.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
      linarith
  have e1 : (1 / 2 : ℂ) + t * I + θ = (((1 / 2 + θ : ℝ)) : ℂ) + t * I := by push_cast; ring
  have e2 : 1 - ((1 / 2 : ℂ) + t * I) - θ = (((1 / 2 - θ : ℝ)) : ℂ) - t * I := by push_cast; ring
  have e3 : (1 / 2 : ℂ) + t * I + (-θ : ℝ) = (((1 / 2 - θ : ℝ)) : ℂ) + t * I := by push_cast; ring
  have e4 : 1 - ((1 / 2 : ℂ) + t * I) - (-θ : ℝ) = (((1 / 2 + θ : ℝ)) : ℂ) - t * I := by push_cast; ring
  have n2 : ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 - θ : ℝ) : ℂ) - t * I))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply nz
    simp
    intro h; apply h1; linarith
  have n4 : ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 + θ : ℝ) : ℂ) - t * I))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply nz
    simp
    intro h; apply h2; linarith
  have c1 := norm_one_sub_cpow_conj hp0 (1 / 2 + θ) t
  have c3 := norm_one_sub_cpow_conj hp0 (1 / 2 - θ) t
  simp only [gammaTw, L, e1, e2, e3, e4, norm_mul, norm_div, norm_inv]
  rw [c1, c3]
  generalize ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 - θ : ℝ) : ℂ) - t * I))‖ = x at n2 ⊢
  generalize ‖(1 : ℂ) - (p : ℂ) ^ (-(((1 / 2 + θ : ℝ) : ℂ) - t * I))‖ = y at n4 ⊢
  field_simp

/-- `Re[z/(1−z)] = (Re z − |z|²)/|1−z|²`. -/
theorem re_div_one_sub (z : ℂ) :
    (z / (1 - z)).re = (z.re - Complex.normSq z) / Complex.normSq (1 - z) := by
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.normSq_apply]
  by_cases h : (1 - z.re) * (1 - z.re) + z.im * z.im = 0
  · simp [h]
  · field_simp
    ring

/-- On the circle `|z| = r` (`0 < r < 1`) the density `Re[z/(1−z)]` is positive at `z = r`. -/
theorem local_density_sign_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ z : ℂ, ‖z‖ = r ∧ 0 < (z / (1 - z)).re := by
  refine ⟨(r : ℂ), by simp [abs_of_pos hr0], ?_⟩
  have : ((r : ℂ) / (1 - (r : ℂ))) = ((r / (1 - r) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]
  exact div_pos hr0 (by linarith)

/-- ... and negative at `z = −r`. -/
theorem local_density_sign_neg {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ z : ℂ, ‖z‖ = r ∧ (z / (1 - z)).re < 0 := by
  refine ⟨(-(r : ℂ)), by simp [abs_of_pos hr0], ?_⟩
  have : (-(r : ℂ) / (1 - -(r : ℂ))) = ((-r / (1 + r) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The mirror overlap squared `R² = (1−a²)(1−b²)/(1−ab)²`. -/
noncomputable def Rsq (a b : ℝ) : ℝ := (1 - a ^ 2) * (1 - b ^ 2) / (1 - a * b) ^ 2

/-- `1 − R² = (a−b)²/(1−ab)²`. -/
theorem mirror_overlap_sq (a b : ℝ) (h : a * b ≠ 1) :
    1 - Rsq a b = (a - b) ^ 2 / (1 - a * b) ^ 2 := by
  have : (1 - a * b) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h))
  unfold Rsq
  field_simp
  ring

theorem Rsq_comm (a b : ℝ) : Rsq a b = Rsq b a := by unfold Rsq; ring

/-- Partial mirror product over primes `< N` with `a = p^{−m}`, `b = p^{−(1−m)}`. -/
noncomputable def mirrorProd (m : ℝ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range N).filter Nat.Prime, Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m)))

/-- Per-prime lower bound `1 − R_p² ≥ c / p` with `c = (1 − 2^{−(1−2m)})²`. -/
lemma defect_lower {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1 / 2) {p : ℕ} (hp : p.Prime) :
    (1 - 2 ^ (-(1 - 2 * m))) ^ 2 * (1 / (p : ℝ)) ≤
      1 - Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set a : ℝ := (p : ℝ) ^ (-m) with ha
  set b : ℝ := (p : ℝ) ^ (-(1 - m)) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hp0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hp0 _
  have hab : a * b = 1 / (p : ℝ) := by
    rw [ha, hb, ← Real.rpow_add hp0]
    have : -m + -(1 - m) = (-1 : ℝ) := by ring
    rw [this, Real.rpow_neg_one, one_div]
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hab1 : a * b < 1 := by
    rw [hab]; exact (div_lt_one hp0).mpr hp1
  have hbq : b = a * (p : ℝ) ^ (-(1 - 2 * m)) := by
    rw [ha, hb, ← Real.rpow_add hp0]; congr 1; ring
  set q : ℝ := (2 : ℝ) ^ (-(1 - 2 * m)) with hq
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpq : (p : ℝ) ^ (-(1 - 2 * m)) ≤ q :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have hba : b ≤ a * q := by
    rw [hbq]; exact mul_le_mul_of_nonneg_left hpq ha0.le
  have hdiff : a * (1 - q) ≤ a - b := by nlinarith
  have hdiff0 : 0 ≤ a * (1 - q) := mul_nonneg ha0.le (by linarith)
  have hsq : (a * (1 - q)) ^ 2 ≤ (a - b) ^ 2 := pow_le_pow_left₀ hdiff0 hdiff 2
  have ha2 : 1 / (p : ℝ) ≤ a ^ 2 := by
    have : a ^ 2 = (p : ℝ) ^ (-(2 * m)) := by
      rw [ha, sq, ← Real.rpow_add hp0]; congr 1; ring
    rw [this, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  rw [mirror_overlap_sq a b hab1.ne]
  have hden : (1 - a * b) ^ 2 ≤ 1 := by nlinarith
  have hden0 : 0 < (1 - a * b) ^ 2 := by
    have : 0 < 1 - a * b := by linarith
    positivity
  have hnum : (1 - q) ^ 2 * (1 / (p : ℝ)) ≤ (a - b) ^ 2 := by
    calc (1 - q) ^ 2 * (1 / (p : ℝ)) ≤ (1 - q) ^ 2 * a ^ 2 :=
          mul_le_mul_of_nonneg_left ha2 (by positivity)
      _ = (a * (1 - q)) ^ 2 := by ring
      _ ≤ (a - b) ^ 2 := hsq
  calc (1 - q) ^ 2 * (1 / (p : ℝ)) ≤ (a - b) ^ 2 := hnum
    _ ≤ (a - b) ^ 2 / (1 - a * b) ^ 2 := by
        rw [le_div_iff₀ hden0]; nlinarith [sq_nonneg (a - b)]

/-- Each factor is nonnegative. -/
lemma Rsq_nonneg {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1 / 2) {p : ℕ} (hp : p.Prime) :
    0 ≤ Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ha : ((p : ℝ) ^ (-m)) ^ 2 < 1 := by
    have : (p : ℝ) ^ (-m) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h0 : 0 < (p : ℝ) ^ (-m) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  have hb : ((p : ℝ) ^ (-(1 - m))) ^ 2 < 1 := by
    have : (p : ℝ) ^ (-(1 - m)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h0 : 0 < (p : ℝ) ^ (-(1 - m)) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  unfold Rsq
  apply div_nonneg
  · exact mul_nonneg (by linarith) (by linarith)
  · positivity

/-- Kakutani-type dichotomy, partial products: for `0 < m < ½` the product of the mirror
overlaps over primes `< N` tends to `0`. -/
theorem mirror_product_tendsto_zero {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1 / 2) :
    Tendsto (mirrorProd m) atTop (𝓝 0) := by
  set c : ℝ := (1 - 2 ^ (-(1 - 2 * m))) ^ 2 with hc
  have hq1 : (2 : ℝ) ^ (-(1 - 2 * m)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hcpos : 0 < c := by rw [hc]; have : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * m)) := by linarith
                           positivity
  -- divergence of the prime reciprocal partial sums
  have hdiv : Tendsto (fun N : ℕ => ∑ n ∈ (Finset.range N).filter Nat.Prime, (1 / (n : ℝ)))
      atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (f := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n))
      (fun n => Set.indicator_nonneg (fun k _ => by positivity) n)).mp
      not_summable_one_div_on_primes
    refine h.congr (fun N => ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : n.Prime <;> simp [Set.indicator, hn]
  set S : ℕ → ℝ := fun N => ∑ p ∈ (Finset.range N).filter Nat.Prime,
    (1 - Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m)))) with hS
  have hSlow : ∀ N, c * ∑ n ∈ (Finset.range N).filter Nat.Prime, (1 / (n : ℝ)) ≤ S N := by
    intro N
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p hp => defect_lower hm0 hm1 (Finset.mem_filter.mp hp).2)
  have hSt : Tendsto S atTop atTop :=
    tendsto_atTop_mono hSlow (hdiv.const_mul_atTop hcpos)
  have hexp : Tendsto (fun N => Real.exp (-S N)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hSt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp ?_ ?_
  · intro N
    exact Finset.prod_nonneg (fun p hp => Rsq_nonneg hm0 hm1 (Finset.mem_filter.mp hp).2)
  · intro N
    have hle : ∏ p ∈ (Finset.range N).filter Nat.Prime,
        Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m))) ≤
        ∏ p ∈ (Finset.range N).filter Nat.Prime,
          Real.exp (-(1 - Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m))))) := by
      refine Finset.prod_le_prod (fun p hp => Rsq_nonneg hm0 hm1 (Finset.mem_filter.mp hp).2)
        (fun p hp => ?_)
      have := Real.add_one_le_exp (-(1 - Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m)))))
      linarith
    have heq : ∏ p ∈ (Finset.range N).filter Nat.Prime,
          Real.exp (-(1 - Rsq ((p : ℝ) ^ (-m)) ((p : ℝ) ^ (-(1 - m))))) = Real.exp (-S N) := by
      rw [← Real.exp_sum, hS]
      simp only [Finset.sum_neg_distrib]
    exact hle.trans heq.le

/-- The same for every `σ ∈ (0,1)`, `σ ≠ ½`, by the symmetry `R(a,b) = R(b,a)`. -/
theorem mirror_product_tendsto_zero_sigma {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (hne : σ ≠ 1 / 2) :
    Tendsto (fun N : ℕ => ∏ p ∈ (Finset.range N).filter Nat.Prime,
      Rsq ((p : ℝ) ^ (-σ)) ((p : ℝ) ^ (-(1 - σ)))) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact mirror_product_tendsto_zero h0 h
  · have := mirror_product_tendsto_zero (m := 1 - σ) (by linarith) (by linarith)
    refine this.congr (fun N => ?_)
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [Rsq_comm, sub_sub_cancel]

end GppARPLocalFactors
