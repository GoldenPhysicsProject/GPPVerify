import GppVerify.RiemannHypothesis.PrimeOccupationTail

/-!
# Finite swap-invariant prime blocks discriminate centered from shifted occupation, for any joining

Source: Codex, GPP-bridge `work/codex/2026-10-13_finite_even_prime_clock_discriminators.md` and
`…_bost_connes_prime_clock_fixed_algebra_haar_bridge.md` (PR #11 comment 6154692348).

This upgrades `PrimeOccupationTail` (a tail event) to **finite, bounded** observables. For a finite
block `B` of prime modes, `A_B` = "some mode in `B` is occupied" on one sheet, and
`E_B = A_B × A_B` = "both sheets have an occupied mode in `B`". `E_B` is invariant under the sheet
swap (`EB_swap`). Results:
* `vacuum_prob`: `μ_β(A_Bᶜ) = ∏_{i∈B} (1 − p_i^{−β})`.
* `centered_lower`: for **any** joining `ν` of two copies of `μ₁` (no independence between
  sheets), `ν(E_B) ≥ 1 − 2∏_{i∈B}(1 − 1/p_i)`.
* `shifted_upper`: for any `ν` whose first or second marginal is `μ_c`,
  `ν(E_B) ≤ Σ_{i∈B} p_i^{−c}`.
* `block_discriminator`: for `0 < θ < ½` and every `ε > 0` there is a finite block `B` with
  `ν₀(E_B) ≥ 1 − ε` for **every** joining of `μ₁, μ₁`, and `ν(E_B) ≤ ε` for every joining of
  `μ_{1+2θ}, μ_{1−2θ}` and for its swap. So the centered and shifted states are at norm distance
  `2` on the swap-invariant finite-block observables. The proof uses Euler's `Σ 1/p = ∞` against
  the convergent `Σ p^{−1−2θ}`.

Codex's Bost–Connes reading (`P_n = μ_nμ_n*`, `ω_β(P_n) = n^{−β}`, the Gauss-sum operator `B_χ`
with `B_χ*B_χ = 5/16(1 − P₅)`, and the completed `L(s,χ)` Mellin period) was audited
numerically and by hand but is **not formalized here**. Whether these projections live in a
completed Tate/Weil observable algebra is open. **No RH claim.**
-/

namespace GppPrimeBlockDiscriminator

open MeasureTheory ProbabilityTheory Filter GppPrimeOccupationTail
open scoped ENNReal NNReal

/-- Some mode in the finite block `B` is occupied. -/
def A (B : Finset ℕ) : Set (ℕ → ℕ) := ⋃ i ∈ B, occ i

/-- Both sheets have an occupied mode in `B`. -/
def EB (B : Finset ℕ) : Set ((ℕ → ℕ) × (ℕ → ℕ)) := A B ×ˢ A B

theorem EB_swap (B : Finset ℕ) : Prod.swap ⁻¹' EB B = EB B := by
  ext ⟨ω, ω'⟩; simp [EB]

theorem measurableSet_A (B : Finset ℕ) : MeasurableSet (A B) :=
  Finset.measurableSet_biUnion _ fun i _ => measurableSet_occ i

theorem compl_A (B : Finset ℕ) : (A B)ᶜ = Set.pi (B : Set ℕ) (fun _ => ({0} : Set ℕ)) := by
  ext ω; simp [A, occ, Nat.pos_iff_ne_zero]

theorem law_zero {β : ℝ} (hβ : 0 < β) (i : ℕ) :
    law β hβ.le i {0} = ENNReal.ofReal (1 - q β i) := by
  have h := occ_prob hβ i
  have hset : {n : ℕ | 0 < n} = ({0} : Set ℕ)ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
  rw [hset, measure_compl (MeasurableSet.singleton 0) (measure_ne_top _ _), measure_univ] at h
  have h0 : law β hβ.le i {0} ≠ ∞ := measure_ne_top _ _
  have h1 : law β hβ.le i {0} ≤ 1 := prob_le_one
  rw [← ENNReal.ofReal_toReal h0]
  congr 1
  have := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (q_nonneg β i)] at this
  linarith

/-- **Vacuum probability of a block**: `μ_β(A_Bᶜ) = ∏_{i∈B}(1 − p_i^{−β})`. -/
theorem vacuum_prob {β : ℝ} (hβ : 0 < β) (B : Finset ℕ) :
    Measure.infinitePi (law β hβ.le) (A B)ᶜ = ENNReal.ofReal (∏ i ∈ B, (1 - q β i)) := by
  rw [compl_A, Measure.infinitePi_pi (X := fun _ => ℕ) (μ := law β hβ.le)
    (fun _ _ => MeasurableSet.singleton 0)]
  simp_rw [law_zero hβ]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => by linarith [q_le_one hβ.le i]]

/-- **Centered lower bound, any joining**: `ν(E_B) ≥ 1 − 2∏(1 − 1/p_i)`. -/
theorem centered_lower (ν : Measure ((ℕ → ℕ) × (ℕ → ℕ))) [IsProbabilityMeasure ν]
    (h1 : ν.map Prod.fst = Measure.infinitePi (law 1 zero_le_one))
    (h2 : ν.map Prod.snd = Measure.infinitePi (law 1 zero_le_one)) (B : Finset ℕ) :
    1 - 2 * ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) ≤ ν (EB B) := by
  have hA := measurableSet_A B
  have hsub : (EB B)ᶜ ⊆ Prod.fst ⁻¹' (A B)ᶜ ∪ Prod.snd ⁻¹' (A B)ᶜ := by
    intro x hx; simp only [EB, Set.mem_compl_iff, Set.mem_prod, not_and_or] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hfst : ν (Prod.fst ⁻¹' (A B)ᶜ) = ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) := by
    rw [← Measure.map_apply measurable_fst hA.compl, h1, vacuum_prob one_pos]
  have hsnd : ν (Prod.snd ⁻¹' (A B)ᶜ) = ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) := by
    rw [← Measure.map_apply measurable_snd hA.compl, h2, vacuum_prob one_pos]
  have hc : ν (EB B)ᶜ ≤ 2 * ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) := by
    calc ν (EB B)ᶜ ≤ ν (Prod.fst ⁻¹' (A B)ᶜ ∪ Prod.snd ⁻¹' (A B)ᶜ) := measure_mono hsub
      _ ≤ ν (Prod.fst ⁻¹' (A B)ᶜ) + ν (Prod.snd ⁻¹' (A B)ᶜ) := measure_union_le _ _
      _ = 2 * ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) := by rw [hfst, hsnd, two_mul]
  have hmeas : MeasurableSet (EB B) := hA.prod hA
  calc 1 - 2 * ENNReal.ofReal (∏ i ∈ B, (1 - q 1 i)) ≤ 1 - ν (EB B)ᶜ := tsub_le_tsub_left hc 1
    _ = ν (EB B) := by rw [prob_compl_eq_one_sub hmeas, ENNReal.sub_sub_cancel ENNReal.one_ne_top
        prob_le_one]

theorem occupied_upper {c : ℝ} (hc : 0 < c) (B : Finset ℕ) :
    Measure.infinitePi (law c hc.le) (A B) ≤ ENNReal.ofReal (∑ i ∈ B, q c i) := by
  calc Measure.infinitePi (law c hc.le) (A B) ≤ ∑ i ∈ B, Measure.infinitePi (law c hc.le) (occ i) :=
        measure_biUnion_finset_le _ _
    _ = ∑ i ∈ B, ENNReal.ofReal (q c i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [infinitePi_occ, occ_prob hc]
    _ = ENNReal.ofReal (∑ i ∈ B, q c i) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => q_nonneg c i).symm

/-- **Shifted upper bound**: if either marginal is `μ_c`, `ν(E_B) ≤ Σ_{i∈B} p_i^{−c}`. -/
theorem shifted_upper {c : ℝ} (hc : 0 < c) (ν : Measure ((ℕ → ℕ) × (ℕ → ℕ)))
    (h : ν.map Prod.fst = Measure.infinitePi (law c hc.le) ∨
      ν.map Prod.snd = Measure.infinitePi (law c hc.le)) (B : Finset ℕ) :
    ν (EB B) ≤ ENNReal.ofReal (∑ i ∈ B, q c i) := by
  have hA := measurableSet_A B
  rcases h with h | h
  · calc ν (EB B) ≤ ν (Prod.fst ⁻¹' A B) := measure_mono fun x hx => hx.1
      _ = _ := by rw [← Measure.map_apply measurable_fst hA, h]
      _ ≤ _ := occupied_upper hc B
  · calc ν (EB B) ≤ ν (Prod.snd ⁻¹' A B) := measure_mono fun x hx => hx.2
      _ = _ := by rw [← Measure.map_apply measurable_snd hA, h]
      _ ≤ _ := occupied_upper hc B

theorem summable_q_iff {β : ℝ} : Summable (q β) ↔ 1 < β := by
  have hq : q β = (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-β)) ∘ (Denumerable.eqv Nat.Primes).symm :=
    rfl
  rw [hq, Equiv.summable_iff, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

theorem prod_one_sub_le_exp (B : Finset ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∏ i ∈ B, (1 - q β i) ≤ Real.exp (-∑ i ∈ B, q β i) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => by linarith [q_le_one hβ i]) fun i _ => ?_
  linarith [Real.add_one_le_exp (-q β i)]

/-- **Finite-block discriminator**: for `0 < θ < ½` and `ε > 0` there is a finite block `B` with
`ν(E_B) ≥ 1 − ε` for every joining of `μ₁, μ₁`, and `ν(E_B) ≤ ε` for every measure with a
`μ_{1+2θ}` marginal (covering both orderings, hence the swap-symmetrized shifted state). -/
theorem block_discriminator {θ : ℝ} (h0 : 0 < θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Finset ℕ,
      (∀ (ν : Measure ((ℕ → ℕ) × (ℕ → ℕ))) [IsProbabilityMeasure ν],
        ν.map Prod.fst = Measure.infinitePi (law 1 zero_le_one) →
        ν.map Prod.snd = Measure.infinitePi (law 1 zero_le_one) →
        1 - ENNReal.ofReal ε ≤ ν (EB B)) ∧
      (∀ ν : Measure ((ℕ → ℕ) × (ℕ → ℕ)),
        (ν.map Prod.fst = Measure.infinitePi (law (1 + 2 * θ) (by linarith)) ∨
          ν.map Prod.snd = Measure.infinitePi (law (1 + 2 * θ) (by linarith))) →
        ν (EB B) ≤ ENNReal.ofReal ε) := by
  set c := 1 + 2 * θ with hcdef
  have hc : 0 < c := by linarith
  -- tail of the convergent supercritical series
  have hsc : Summable (q c) := summable_q_iff.mpr (by linarith)
  have htail := (tendsto_sum_nat_add (q c))
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  -- divergent critical series: partial sums from N exceed log(2/ε)
  have hdiv : ¬ Summable (fun k => q 1 (k + N)) := by
    rw [summable_nat_add_iff]; rw [summable_q_iff]; simp
  obtain ⟨K, hK⟩ : ∃ K, Real.log (2 / ε) < ∑ k ∈ Finset.range K, q 1 (k + N) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact hdiv (summable_of_sum_range_le (fun k => q_nonneg 1 _) hcon)
  refine ⟨(Finset.range K).map (addRightEmbedding N), ?_, ?_⟩
  · intro ν _ h1 h2
    refine le_trans ?_ (centered_lower ν h1 h2 _)
    have hsum : ∑ i ∈ (Finset.range K).map (addRightEmbedding N), q 1 i =
        ∑ k ∈ Finset.range K, q 1 (k + N) := by simp
    have hprod := prod_one_sub_le_exp ((Finset.range K).map (addRightEmbedding N)) 1 zero_le_one
    rw [hsum] at hprod
    have hexp : Real.exp (-∑ k ∈ Finset.range K, q 1 (k + N)) < ε / 2 := by
      have := Real.exp_lt_exp.mpr (neg_lt_neg hK)
      rwa [Real.exp_neg (Real.log _), Real.exp_log (by positivity), inv_div] at this
    have hP : 2 * ENNReal.ofReal (∏ i ∈ (Finset.range K).map (addRightEmbedding N), (1 - q 1 i))
        ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact tsub_le_tsub_left hP 1
  · intro ν hν
    refine (shifted_upper hc ν hν _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsum : ∑ i ∈ (Finset.range K).map (addRightEmbedding N), q c i =
        ∑ k ∈ Finset.range K, q c (k + N) := by simp
    rw [hsum]
    have hle : ∑ k ∈ Finset.range K, q c (k + N) ≤ ∑' k, q c (k + N) :=
      ((summable_nat_add_iff N).mpr hsc).sum_le_tsum _ fun k _ => q_nonneg c _
    linarith [hN N le_rfl]

/-- The swap-symmetrized shifted state inherits the bound: an equal mixture of two measures
each with `ν(E) ≤ x` satisfies the same bound. -/
theorem mixture_le {ν₁ ν₂ : Measure ((ℕ → ℕ) × (ℕ → ℕ))} {S : Set ((ℕ → ℕ) × (ℕ → ℕ))}
    {x : ℝ≥0∞} (h₁ : ν₁ S ≤ x) (h₂ : ν₂ S ≤ x) : ((1 / 2 : ℝ≥0∞) • ν₁ + (1 / 2 : ℝ≥0∞) • ν₂) S ≤ x := by
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  calc 1 / 2 * ν₁ S + 1 / 2 * ν₂ S ≤ 1 / 2 * x + 1 / 2 * x := add_le_add (by gcongr) (by gcongr)
    _ = x := by rw [← add_mul, ENNReal.add_halves, one_mul]

end GppPrimeBlockDiscriminator
