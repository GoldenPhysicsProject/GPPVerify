import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Geometric
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Logic.Denumerable

/-!
# The unlabeled all-prime tail event separates the centered and shifted occupation laws

Source: Codex, GPP-bridge PR #11 (comment 6152772620, 2026-10-13) and private bridge note
`work/codex/2026-10-13_all_prime_kakutani_fisher_critical_temperature_boundary.md`.

Let `μ_β = ⊗_p Geom(p^{−β})` be the all-prime occupation law: mode `p` is occupied with
probability `p^{−β}`. This file proves:
* `infinitely_occupied_dichotomy`: for any infinite product of probability measures on `ℕ`, the event
  "infinitely many modes are occupied" has probability `1` if `Σ_i P(occupied_i) = ∞` and `0`
  otherwise. This is the first and second Borel–Cantelli lemmas, with independence of coordinates
  under `Measure.infinitePi`.
* `occ_prob`: in the prime law the occupation probability of mode `p` is exactly `p^{−β}`.
* `tail_one_iff` (with `tail_zero_iff`): `μ_β(infinitely many primes occupied) = 1` for `β ≤ 1` and
  `= 0` for `β > 1`. The proof goes through Mathlib's `Σ_p p^r < ∞ ⟺ r < −1`.
* `pair_event_swap`: the event `E = {both sheets infinitely occupied}` is invariant under the sheet
  swap `R`.
* `centered_pair_E`, `shifted_pair_E`: `ν₀(E) = 1` for `ν₀ = μ₁ ⊗ μ₁`, and `ν_θ(E) = 0` for the
  `R`-symmetrized `ν_θ = ½(μ_{1+2θ} ⊗ μ_{1−2θ} + μ_{1−2θ} ⊗ μ_{1+2θ})`, `0 < θ < ½`.
  So the two measures are mutually singular already on the swap-invariant tail.

Codex's caveat stands. `E` is a tail event, not a bounded quasi-local observable. Whether a completed
Tate/Poisson observable algebra contains it, and whether it couples to the `ξ` spectral data, is
open. **No RH claim.**
-/

namespace GppPrimeOccupationTail

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

section General

variable (μ : ℕ → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]

/-- Mode `i` is occupied. -/
def occ (i : ℕ) : Set (ℕ → ℕ) := {ω | 0 < ω i}

theorem measurableSet_occ (i : ℕ) : MeasurableSet (occ i) :=
  measurable_pi_apply i (MeasurableSet.of_discrete (s := {n : ℕ | 0 < n}))

theorem iIndepSet_occ : iIndepSet occ (Measure.infinitePi μ) := by
  rw [iIndepSet_iff_meas_biInter measurableSet_occ]
  intro s
  have hpi : (⋂ i ∈ s, occ i) = Set.pi (s : Set ℕ) (fun _ => {n : ℕ | 0 < n}) := by
    ext ω; simp [occ]
  have hone : ∀ i, Measure.infinitePi μ (occ i) = μ i {n : ℕ | 0 < n} := by
    intro i
    have : occ i = Set.pi ({i} : Finset ℕ) (fun _ => {n : ℕ | 0 < n}) := by ext ω; simp [occ]
    rw [this, Measure.infinitePi_pi (X := fun _ => ℕ) (μ := μ) (fun _ _ => MeasurableSet.of_discrete)]
    simp
  rw [hpi, Measure.infinitePi_pi (X := fun _ => ℕ) (μ := μ) (fun _ _ => MeasurableSet.of_discrete)]
  simp_rw [hone]

theorem infinitePi_occ (i : ℕ) : Measure.infinitePi μ (occ i) = μ i {n : ℕ | 0 < n} := by
  have : occ i = Set.pi ({i} : Finset ℕ) (fun _ => {n : ℕ | 0 < n}) := by ext ω; simp [occ]
  rw [this, Measure.infinitePi_pi (X := fun _ => ℕ) (μ := μ) (fun _ _ => MeasurableSet.of_discrete)]
  simp

/-- **Borel–Cantelli dichotomy** for infinitely many occupied modes. -/
theorem infinitely_occupied_dichotomy :
    (∑' i, μ i {n : ℕ | 0 < n} = ∞ → Measure.infinitePi μ (limsup occ atTop) = 1) ∧
    (∑' i, μ i {n : ℕ | 0 < n} ≠ ∞ → Measure.infinitePi μ (limsup occ atTop) = 0) := by
  constructor
  · intro h
    refine measure_limsup_eq_one measurableSet_occ (iIndepSet_occ μ) ?_
    simpa [infinitePi_occ] using h
  · intro h
    refine measure_limsup_atTop_eq_zero ?_
    simpa [infinitePi_occ] using h

end General

section Primes

instance : Encodable Nat.Primes := inferInstanceAs (Encodable {p : ℕ // p.Prime})

instance : Denumerable Nat.Primes := Denumerable.ofEncodableOfInfinite Nat.Primes

/-- An enumeration of the primes. -/
def prime (i : ℕ) : Nat.Primes := (Denumerable.eqv Nat.Primes).symm i

/-- Occupation probability `p^{−β}` of the prime mode, as an element of `[0,1]` for `β ≥ 0`. -/
noncomputable def q (β : ℝ) (i : ℕ) : ℝ := (((prime i : ℕ) : ℝ)) ^ (-β)

theorem q_nonneg (β : ℝ) (i : ℕ) : 0 ≤ q β i := by unfold q; positivity

theorem q_le_one {β : ℝ} (hβ : 0 ≤ β) (i : ℕ) : q β i ≤ 1 := by
  unfold q
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (prime i).prop.one_lt.le)
    (by linarith)

/-- Success probability `1 − p^{−β}` of the geometric law. -/
noncomputable def succ (β : ℝ) (hβ : 0 ≤ β) (i : ℕ) : unitInterval :=
  ⟨1 - q β i, by constructor <;> linarith [q_nonneg β i, q_le_one hβ i]⟩

/-- The prime occupation law at mode `i`: `P(N = n) = (1 − p^{−β}) p^{−βn}`. -/
noncomputable def law (β : ℝ) (hβ : 0 ≤ β) (i : ℕ) : Measure ℕ := geometricMeasure (succ β hβ i)

instance (β : ℝ) (hβ : 0 ≤ β) (i : ℕ) : IsProbabilityMeasure (law β hβ i) := by
  unfold law; infer_instance

theorem q_lt_one {β : ℝ} (hβ : 0 < β) (i : ℕ) : q β i < 1 := by
  unfold q
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (prime i).prop.one_lt) (by linarith)

/-- **Occupation probability**: `P(N_p > 0) = p^{−β}`. -/
theorem occ_prob {β : ℝ} (hβ : 0 < β) (i : ℕ) :
    law β hβ.le i {n : ℕ | 0 < n} = ENNReal.ofReal (q β i) := by
  have hne : succ β hβ.le i ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp [succ] at this
    linarith [q_lt_one hβ i]
  have hset : {n : ℕ | 0 < n} = ({0} : Set ℕ)ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
  rw [hset, measure_compl (MeasurableSet.singleton 0) (measure_ne_top _ _), measure_univ]
  unfold law
  rw [geometricMeasure_singleton hne]
  simp only [pow_zero, one_mul, succ]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith [q_nonneg β i, q_le_one hβ.le i])]
  congr 1; ring

theorem tsum_occ_eq_top_iff {β : ℝ} (hβ : 0 < β) :
    (∑' i, law β hβ.le i {n : ℕ | 0 < n}) = ∞ ↔ β ≤ 1 := by
  simp_rw [occ_prob hβ]
  simp only [ENNReal.ofReal]
  rw [← not_iff_not, ← ne_eq, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp only [Real.coe_toNNReal _ (q_nonneg β _)]
  have hq : q β = (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-β)) ∘ (Denumerable.eqv Nat.Primes).symm :=
    rfl
  rw [hq, Equiv.summable_iff, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **The all-prime tail dichotomy**: almost surely infinitely many primes occupied iff `β ≤ 1`. -/
theorem tail_one_iff {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Measure.infinitePi (law β hβ.le) (limsup occ atTop) = 1 :=
  (infinitely_occupied_dichotomy (law β hβ.le)).1 ((tsum_occ_eq_top_iff hβ).2 hβ1)

theorem tail_zero_iff {β : ℝ} (hβ : 1 < β) :
    Measure.infinitePi (law β (by linarith)) (limsup occ atTop) = 0 :=
  (infinitely_occupied_dichotomy (law β (by linarith))).2 (fun h =>
    absurd ((tsum_occ_eq_top_iff (by linarith)).1 h) (by linarith))

/-- The unlabeled pair event: both sheets infinitely occupied. -/
def E : Set ((ℕ → ℕ) × (ℕ → ℕ)) := limsup occ atTop ×ˢ limsup occ atTop

/-- `E` is invariant under the sheet swap `R`. -/
theorem pair_event_swap : Prod.swap ⁻¹' E = E := by
  ext ⟨ω, ω'⟩; simp [E]

/-- **Centered pair**: `ν₀(E) = 1`. -/
theorem centered_pair_E :
    ((Measure.infinitePi (law 1 zero_le_one)).prod (Measure.infinitePi (law 1 zero_le_one))) E
      = 1 := by
  rw [E, Measure.prod_prod, tail_one_iff one_pos le_rfl, one_mul]

/-- **Shifted symmetrized pair**: `ν_θ(E) = 0` for `0 < θ < ½`. -/
theorem shifted_pair_E {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1 / 2) :
    ((1 / 2 : ℝ≥0∞) • ((Measure.infinitePi (law (1 + 2 * θ) (by linarith))).prod
        (Measure.infinitePi (law (1 - 2 * θ) (by linarith))) +
      (Measure.infinitePi (law (1 - 2 * θ) (by linarith))).prod
        (Measure.infinitePi (law (1 + 2 * θ) (by linarith))))) E = 0 := by
  rw [Measure.smul_apply, Measure.add_apply, E, Measure.prod_prod, Measure.prod_prod,
    tail_zero_iff (by linarith)]
  simp

end Primes

end GppPrimeOccupationTail
