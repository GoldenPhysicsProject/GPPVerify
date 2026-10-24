import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The critical prime thermofield state: exact finite identities

Sources: Codex, GPP-bridge PR #11 comments 6376282990, 6376325034, 6376349113 and 6376360639
(2026-10-23), with private derivations in
`work/codex/2026-10-23_critical_prime_tfd_gns_fidelity_spectral_completion.md` and
`work/codex/2026-10-23_critical_prime_tfd_dickman_vs_gibbs_clock_disjointness.md`. Audited on
PR #11 by Claude Code (comments 6376291691, 6376333230, 6376357997). Daniel Toupin / Golden
Physics Project, with AI assistance from Codex (statements) and Claude Code (formalization).

For a prime `p` and `β > 0` the local thermofield amplitudes are `a_β(k) = √(1 − q) q^{k/2}`, with
`q = p^{−β}`.

* `local_overlap`: for `0 ≤ q₁ < 1` and `q₂ < 1`,
  `∑_k √(1−q₁) q₁^{k/2} · √(1−q₂) q₂^{k/2} = √((1−q₁)(1−q₂)) / (1 − √(q₁q₂))`. This is the
  per-prime factor of Codex's fidelity `ζ((β+β′)/2)/√(ζ(β)ζ(β′))`.
* `sum_clock_coeff`: `(1 − q) ∑_k q^k e^{ikθ} = (1 − q)/(1 − q e^{iθ})` for `0 ≤ q < 1`. With
  `q = 1/p` and `θ = 2t log p` this is the sum-clock matrix coefficient
  `(1 − p^{−1})/(1 − p^{−1+2it})`.
* `phase_eq_one_of_overlap`: a linear isometry `U` with `U Ω = Ω` and `U w = c w` forces `c = 1`
  whenever `⟨Ω, w⟩ ≠ 0`. This is Codex's one-prime obstruction: with `⟨Ω_p, V_pΩ_p⟩ = p^{−β/2} ≠ 0`,
  no such unitary assigns the phase `p^{it} ≠ 1` to `V_pΩ_p`.
* `lcm_div_gcd_factorization`, `lcm_div_gcd_mul_gcd_sq`: `v_p(lcm/gcd) = max − min` of the two
  valuations, and `(lcm/gcd)·gcd² = mn`. So `∏_p p^{|v_p m − v_p n|} = mn/gcd(m,n)²`, the
  valuation step behind `⟨V_mΩ_β, V_nΩ_β⟩ = (gcd²/(mn))^{β/2}` at every `β > 0`, including the
  critical `β = 1`.
* `gibbs_ratio_tendsto`: `ζ(1 + (1+a)δ)/ζ(1 + δ) → 1/(1+a)` as `δ → 0⁺`, the Exp(1) Laplace law of
  `δ log n` under the normalized Gibbs state.
* `fidelity_sq_tendsto`: `ζ(1 + (1+a)δ/2)² / (ζ(1+δ) ζ(1+aδ)) → 4a/(1+a)²`, the square of Codex's
  critical fidelity limit `2√a/(1+a)`.

**Scope.** The infinite tensor product, its GNS representation, disjointness, the Dickman limit
(which needs a PNT-level Mertens theorem) and the operator constructions are not formalized. No
claim about RH.
-/

open Filter Topology Complex

namespace GppCriticalPrimeTFD

/-- **Local thermofield overlap.** -/
theorem local_overlap {q₁ q₂ : ℝ} (h₁ : 0 ≤ q₁) (h₁' : q₁ < 1) (h₂' : q₂ < 1) :
    HasSum (fun k : ℕ => (Real.sqrt (1 - q₁) * Real.sqrt q₁ ^ k) *
      (Real.sqrt (1 - q₂) * Real.sqrt q₂ ^ k))
      (Real.sqrt ((1 - q₁) * (1 - q₂)) / (1 - Real.sqrt (q₁ * q₂))) := by
  have hr0 : 0 ≤ Real.sqrt (q₁ * q₂) := Real.sqrt_nonneg _
  have hr1 : Real.sqrt (q₁ * q₂) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    nlinarith
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.sqrt ((1 - q₁) * (1 - q₂)))
  rw [div_eq_mul_inv]
  refine h.congr_fun fun k => ?_
  rw [Real.sqrt_mul (by linarith), Real.sqrt_mul h₁, mul_pow]
  ring

/-- **The sum-clock coefficient.** -/
theorem sum_clock_coeff {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => ((1 - q : ℝ) : ℂ) * ((q : ℂ) ^ k * exp (k * θ * I)))
      (((1 - q : ℝ) : ℂ) / (1 - q * exp (θ * I))) := by
  have hn : ‖(q : ℂ) * exp (θ * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h0]
    exact h1
  have h := (hasSum_geometric_of_norm_lt_one hn).mul_left (((1 - q : ℝ) : ℂ))
  rw [div_eq_mul_inv]
  refine h.congr_fun fun k => ?_
  rw [mul_pow, ← Complex.exp_nat_mul]
  ring_nf

/-- **The one-prime unitary-time obstruction.** -/
theorem phase_eq_one_of_overlap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →ₗᵢ[ℂ] E) {Ω w : E} {c : ℂ} (hΩ : U Ω = Ω) (hw : U w = c • w)
    (hov : @inner ℂ E _ Ω w ≠ 0) : c = 1 := by
  have h := U.inner_map_map Ω w
  rw [hΩ, hw, inner_smul_right] at h
  have : (c - 1) * @inner ℂ E _ Ω w = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hov

/-- **Valuation of `lcm/gcd`**: `v_p(lcm(m,n)/gcd(m,n)) = max − min`. -/
lemma gcd_dvd_lcm (m n : ℕ) : Nat.gcd m n ∣ Nat.lcm m n :=
  (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)

theorem lcm_div_gcd_factorization {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (p : ℕ) :
    (Nat.lcm m n / Nat.gcd m n).factorization p =
      max (m.factorization p) (n.factorization p) -
        min (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_div (gcd_dvd_lcm m n), Finsupp.tsub_apply, Nat.factorization_lcm hm hn,
    Nat.factorization_gcd hm hn]
  rfl

/-- **`(lcm/gcd)·gcd² = mn`**, so `lcm/gcd = mn/gcd²`. -/
theorem lcm_div_gcd_mul_gcd_sq (m n : ℕ) :
    Nat.lcm m n / Nat.gcd m n * Nat.gcd m n ^ 2 = m * n := by
  rcases Nat.eq_zero_or_pos (Nat.gcd m n) with h | h
  · rw [h]; simp [Nat.gcd_eq_zero_iff.mp h]
  · rw [sq, ← mul_assoc, Nat.div_mul_cancel (gcd_dvd_lcm m n), mul_comm (Nat.lcm m n),
      Nat.gcd_mul_lcm]

lemma tendsto_residue_comp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => ((c * δ : ℝ) : ℂ) * riemannZeta (1 + (c * δ : ℝ))) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun δ : ℝ => (1 : ℂ) + ((c * δ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous fun δ : ℝ => (1 : ℂ) + ((c * δ : ℝ) : ℂ) :=
        continuous_const.add (continuous_ofReal.comp (continuous_const.mul continuous_id))
      have : Tendsto (fun δ : ℝ => (1 : ℂ) + ((c * δ : ℝ) : ℂ)) (𝓝 0)
          (𝓝 (1 + ((c * 0 : ℝ) : ℂ))) := hcont.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      rw [Set.mem_compl_singleton_iff]
      intro h
      have h0 : ((c * δ : ℝ) : ℂ) = 0 := by linear_combination h
      exact (mul_pos hc hδ).ne' (by exact_mod_cast h0)
  have := riemannZeta_residue_one.comp hmap
  refine this.congr fun δ => ?_
  simp

lemma zeta_ne_zero_of_pos {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    riemannZeta (1 + ((c * δ : ℝ) : ℂ)) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [add_re, one_re, ofReal_re]
  linarith [mul_pos hc hδ]

/-- **The Gibbs (temperature) clock is Exp(1)**: `ζ(1+(1+a)δ)/ζ(1+δ) → 1/(1+a)`. -/
theorem gibbs_ratio_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => riemannZeta (1 + ((1 + a) * δ : ℝ)) / riemannZeta (1 + ((1 : ℝ) * δ : ℝ)))
      (𝓝[>] 0) (𝓝 (1 / (1 + a))) := by
  have hb : (0 : ℝ) < 1 + a := by linarith
  have h1 := tendsto_residue_comp hb
  have h2 := tendsto_residue_comp (c := 1) one_pos
  have hq := (h1.div h2 one_ne_zero).const_mul (1 / ((1 + a : ℝ) : ℂ))
  have h1a : ((1 + a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [div_one, mul_one, show (1 : ℂ) / ((1 + a : ℝ) : ℂ) = 1 / (1 + a) by push_cast; rfl] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have hδc : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hz1 := zeta_ne_zero_of_pos hb hδ
  have hz2 := zeta_ne_zero_of_pos one_pos hδ
  simp only [Pi.div_apply]
  push_cast at hz1 hz2 h1a ⊢
  field_simp

/-- **The critical fidelity limit (squared)**:
`ζ(1 + (1+a)δ/2)² / (ζ(1+δ) ζ(1+aδ)) → 4a/(1+a)²`. -/
theorem fidelity_sq_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => riemannZeta (1 + ((1 + a) / 2 * δ : ℝ)) ^ 2 /
      (riemannZeta (1 + ((1 : ℝ) * δ : ℝ)) * riemannZeta (1 + (a * δ : ℝ))))
      (𝓝[>] 0) (𝓝 (4 * a / (1 + a) ^ 2)) := by
  have hb : 0 < (1 + a) / 2 := by linarith
  have h1 := tendsto_residue_comp hb
  have h2 := tendsto_residue_comp (c := 1) one_pos
  have h3 := tendsto_residue_comp ha
  have hq := ((h1.pow 2).div (h2.mul h3) (by norm_num)).const_mul
    (4 * (a : ℂ) / ((1 + a : ℝ) : ℂ) ^ 2)
  have hlim : 4 * (a : ℂ) / ((1 + a : ℝ) : ℂ) ^ 2 * (1 ^ 2 / (1 * 1)) = 4 * a / (1 + a) ^ 2 := by
    push_cast; ring
  rw [hlim] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have hδc : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h1a : ((1 + a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + a : ℝ) ≠ 0)
  have hz1 := zeta_ne_zero_of_pos hb hδ
  have hz2 := zeta_ne_zero_of_pos one_pos hδ
  have hz3 := zeta_ne_zero_of_pos ha hδ
  simp only [Pi.div_apply]
  push_cast at hz1 hz2 hz3 h1a ⊢
  field_simp
  ring

end GppCriticalPrimeTFD
