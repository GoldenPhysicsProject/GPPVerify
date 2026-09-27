import GppVerify.RiemannHypothesis.DirichletLogGaugeIdentity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Half-density zeta synthesis on a divisor-closed set

Source: Codex, GPPDiscovery2 `discovery/rh/RH_HALFDENSITY_ZETA_GAUGE_STABILITY_2026-09-24.md`,
§§1–2 (formalized here 2026-09-27).

Let `S ⊂ ℕ` be finite, divisor-closed and not containing `0`. On functions `f : ℕ → ℝ` define,
for `n ∈ S`,

  (Z f)(n)  = Σ_{d ∈ S, d ∣ n} √(d/n) f(d)              (half-density zeta synthesis)
  (M f)(n)  = Σ_{d ∈ S, d ∣ n} μ(n/d) √(d/n) f(d)       (half-density Möbius)
  (L_Λ f)(n) = Σ_{d ∈ S, d ∣ n} Λ(n/d) √(d/n) f(d)      (half-density von Mangoldt)
  (D f)(n)  = log n · f(n).

Proved here, for every `n ∈ S`:

* `halfMobius_halfZeta` and `halfZeta_halfMobius`: `M Z = Z M = I` (note eq. (3));
* `half_density_gauge`: `M D Z - D = L_Λ` (note eq. (4)), the half-density form of
  `GppDirichletLogGaugeIdentity.mobius_gauge_connection`.

The mechanism is that conjugation by `√n` turns `Z`, `M`, `L_Λ` into Dirichlet convolution with
`ζ`, `μ`, `Λ`, and divisor-closedness makes `{d ∈ S | d ∣ n} = n.divisors`.

## Not formalized here

The note's §3–4 Schur-test bounds `‖Z‖, ‖M‖ ≤ √(τ_max(X)(1 + log X))` and the subexponential
growth of `τ_max` are not formalized in this file. These are exact identities only; they do
not control the completed scalar Weil pullback and have no bearing on RH by themselves.
-/

namespace GppHalfDensityZetaGauge

open Finset ArithmeticFunction GppDirichletLogGaugeIdentity
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- A finite set of positive integers closed under taking divisors. -/
structure DivisorClosed (S : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ S
  dvd_mem : ∀ n ∈ S, ∀ d, d ∣ n → d ∈ S

/-- Half-density zeta synthesis `(Z f)(n) = Σ_{d ∈ S, d ∣ n} √(d/n) f(d)`. -/
noncomputable def halfZeta (S : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ S.filter (· ∣ n), Real.sqrt (d / n) * f d

/-- Half-density Möbius operator `(M f)(n) = Σ_{d ∈ S, d ∣ n} μ(n/d) √(d/n) f(d)`. -/
noncomputable def halfMobius (S : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ S.filter (· ∣ n), (μ (n / d) : ℝ) * Real.sqrt (d / n) * f d

/-- Half-density von Mangoldt operator `(L_Λ f)(n) = Σ_{d ∈ S, d ∣ n} Λ(n/d) √(d/n) f(d)`. -/
noncomputable def halfVonMangoldt (S : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ S.filter (· ∣ n), Λ (n / d) * Real.sqrt (d / n) * f d

/-- Logarithmic length `(D f)(n) = log n · f(n)`. -/
noncomputable def logMul (f : ℕ → ℝ) (n : ℕ) : ℝ := Real.log n * f n

/-- The half-density lift `n ↦ √n f(n)` as an arithmetic function. -/
noncomputable def lift (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.sqrt n * f n, by simp⟩

@[simp] lemma lift_apply (f : ℕ → ℝ) (n : ℕ) : lift f n = Real.sqrt n * f n := rfl

section

variable {S : Finset ℕ} (hS : DivisorClosed S)
include hS

lemma filter_dvd_eq {n : ℕ} (hn : n ∈ S) : S.filter (· ∣ n) = n.divisors := by
  have hn0 : n ≠ 0 := fun h => hS.zero_not_mem (h ▸ hn)
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.2, hn0⟩, fun h => ⟨hS.dvd_mem n hn d h.1, h.1⟩⟩

omit hS in
/-- Convolution against a divisor sum, in the `μ(n/d) G(d)` orientation. -/
lemma conv_apply (a G : ArithmeticFunction ℝ) (n : ℕ) :
    (a * G) n = ∑ d ∈ n.divisors, a (n / d) * G d := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal' (fun x y => a x * G y)

/-- Conjugation formula: an operator `Σ_{d ∈ S, d ∣ n} a(n/d) √(d/n) f(d)` is
`(√n)⁻¹ (a * lift f)(n)` on `S`. -/
lemma halfConv_eq (a : ArithmeticFunction ℝ) (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    ∑ d ∈ S.filter (· ∣ n), a (n / d) * Real.sqrt (d / n) * f d =
      (Real.sqrt n)⁻¹ * (a * lift f) n := by
  rw [filter_dvd_eq hS hn, conv_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [lift_apply, Real.sqrt_div (Nat.cast_nonneg d)]
  ring

lemma halfZeta_eq (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfZeta S f n = (Real.sqrt n)⁻¹ * ((ζ : ArithmeticFunction ℝ) * lift f) n := by
  rw [← halfConv_eq hS _ f hn, halfZeta]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdn : d ∣ n := (mem_filter.mp hd).2
  have hn0 : n ≠ 0 := fun h => hS.zero_not_mem (h ▸ hn)
  have hq : n / d ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)
      (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0))
    omega
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq]

lemma halfMobius_eq (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfMobius S f n = (Real.sqrt n)⁻¹ * ((μ : ArithmeticFunction ℝ) * lift f) n := by
  rw [← halfConv_eq hS _ f hn, halfMobius]
  simp [ArithmeticFunction.intCoe_apply]

lemma halfVonMangoldt_eq (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfVonMangoldt S f n = (Real.sqrt n)⁻¹ * (Λ * lift f) n := by
  rw [← halfConv_eq hS _ f hn, halfVonMangoldt]

/-- Convolution only sees the values of `lift g` on divisors of `n`, which lie in `S`. -/
lemma conv_lift_congr (a H : ArithmeticFunction ℝ) (g : ℕ → ℝ) {n : ℕ} (hn : n ∈ S)
    (hg : ∀ d ∈ S, lift g d = H d) :
    (a * lift g) n = (a * H) n := by
  rw [conv_apply, conv_apply]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [hg d (hS.dvd_mem n hn d (Nat.dvd_of_mem_divisors hd))]

lemma lift_halfZeta (f : ℕ → ℝ) :
    ∀ d ∈ S, lift (halfZeta S f) d = ((ζ : ArithmeticFunction ℝ) * lift f) d := by
  intro d hd
  have hd0 : (0 : ℝ) < Real.sqrt d := by
    have : d ≠ 0 := fun h => hS.zero_not_mem (h ▸ hd)
    exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero this)
  rw [lift_apply, halfZeta_eq hS f hd, ← mul_assoc, mul_inv_cancel₀ hd0.ne', one_mul]

lemma lift_halfMobius (f : ℕ → ℝ) :
    ∀ d ∈ S, lift (halfMobius S f) d = ((μ : ArithmeticFunction ℝ) * lift f) d := by
  intro d hd
  have hd0 : (0 : ℝ) < Real.sqrt d := by
    have : d ≠ 0 := fun h => hS.zero_not_mem (h ▸ hd)
    exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero this)
  rw [lift_apply, halfMobius_eq hS f hd, ← mul_assoc, mul_inv_cancel₀ hd0.ne', one_mul]

lemma inv_sqrt_mul_lift (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    (Real.sqrt n)⁻¹ * lift f n = f n := by
  have hn0 : n ≠ 0 := fun h => hS.zero_not_mem (h ▸ hn)
  have : (0 : ℝ) < Real.sqrt n :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  rw [lift_apply, ← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]

/-- **`M Z = I`** on a divisor-closed set (note eq. (3)). -/
theorem halfMobius_halfZeta (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfMobius S (halfZeta S f) n = f n := by
  rw [halfMobius_eq hS _ hn, conv_lift_congr hS _ _ _ hn (lift_halfZeta hS f), ← mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul, inv_sqrt_mul_lift hS f hn]

/-- **`Z M = I`** on a divisor-closed set (note eq. (3)). -/
theorem halfZeta_halfMobius (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfZeta S (halfMobius S f) n = f n := by
  rw [halfZeta_eq hS _ hn, conv_lift_congr hS _ _ _ hn (lift_halfMobius hS f), ← mul_assoc,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul, inv_sqrt_mul_lift hS f hn]

/-- **Half-density logarithmic gauge identity** `M D Z - D = L_Λ` (note eq. (4)). -/
theorem half_density_gauge (f : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    halfMobius S (logMul (halfZeta S f)) n - logMul f n = halfVonMangoldt S f n := by
  have hlift : ∀ d ∈ S, lift (logMul (halfZeta S f)) d =
      lengthDeriv ((ζ : ArithmeticFunction ℝ) * lift f) d := by
    intro d hd
    rw [lengthDeriv_apply, ← lift_halfZeta hS f d hd, lift_apply, lift_apply, logMul]
    ring
  rw [halfMobius_eq hS _ hn, conv_lift_congr hS _ _ _ hn hlift, mobius_lengthDeriv_zeta_mul,
    ArithmeticFunction.add_apply, lengthDeriv_apply, halfVonMangoldt_eq hS f hn, logMul,
    mul_add, ← inv_sqrt_mul_lift hS f hn, lift_apply]
  ring

end

end GppHalfDensityZetaGauge
