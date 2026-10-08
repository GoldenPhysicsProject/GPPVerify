import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The arithmetic fermion sector: squarefree Fock space, traces, and the supersymmetric pairing

For a finite set `P` of primes, the *fermionic* Fock space is the Boolean cube on `P`: a state is an
occupation set `S ⊆ P`, of energy `Σ_{p ∈ S} log p`; it corresponds to the squarefree integer
`n_S = ∏_{p ∈ S} p` (`prodPrimes_injective`, `squarefree_prodPrimes`), and `(-1)^{|S|} = μ(n_S)`
(`moebius_prodPrimes`). With `x_p = p^{-s}`:

* `fermi_trace`: `Σ_{S ⊆ P} ∏_{p∈S} x_p = ∏_{p∈P} (1 + x_p)` — the **ordinary fermionic trace**;
* `fermi_supertrace`: `Σ_{S ⊆ P} (-1)^{|S|} ∏_{p∈S} x_p = ∏_{p∈P} (1 − x_p)` — the **supertrace** weighted by
  `(-1)^F`;
* `fermi_trace_eq` : `1 + x = (1 − x²)/(1 − x)` per prime, which is the finite form of the global
  `ζ(s)/ζ(2s)`; `boson_mul_supertrace`: `∏(1−x_p)⁻¹ · ∏(1−x_p) = 1`;
* `fermi_global_trace`, `fermi_global_supertrace`: for `Re s > 1`, `∏_p (1 + p^{-s}) = ζ(s)/ζ(2s)` and
  `∏_p (1 − p^{-s}) = 1/ζ(s)` (as `HasProd`), alongside Mathlib's bosonic `∏_p (1 − p^{-s})⁻¹ = ζ(s)`;
  `moebius_lseries_eq_inv_zeta`: `Σ μ(n) n^{-s} = 1/ζ(s)`.

The pairing is made explicit for one prime. On `ψ : ℕ × Bool → ℂ` (boson occupation `k`, fermion
occupation `b`) let `Q` send `|k, 1⟩ ↦ √(k+1) |k+1, 0⟩` and `Q† |k+1, 0⟩ = √(k+1) |k, 1⟩`:

* `Q_sq`: `Q² = 0`; `anticomm`: `{Q, Q†} = N_b + N_f`, the (unscaled) Hamiltonian;
* `telescope`: for `0 ≤ x < 1`, `Σ_k (x^k − x^{k+1}) = 1` — the supertrace of the paired spectrum is carried
  entirely by the unpaired vacuum `|0, 0⟩` (Witten index `1`).

## Checks and scope (with the corrections that apply)

* The bosonic factor `(1 − p^{-s})⁻¹` multiplies to `ζ(s)`; the ordinary fermionic trace multiplies to
  `ζ(s)/ζ(2s)`, **not** to `1/ζ(s)`; `1/ζ(s)` is the *supertrace*. These are different objects.
* The identities hold where the products converge (`Re s > 1`). At a nontrivial zero of `ζ` the pole of
  `1/ζ` belongs to the meromorphic continuation of the supertrace; it is not a convergent thermal trace
  diverging.
* "Witten index `1`" is stated only for the single-prime pairing constructed here. For several primes the
  supercharges need Klein factors to anticommute across primes; that is not formalized, and no global
  supersymmetry is claimed.
* The Mertens bound `M(x) = O(x^{1/2+ε})` (equivalent to RH) is a statement about cancellation between
  signed counts; it carries no annihilation dynamics, and none is modelled here.
* "Reflection-fixed" is the precise status of a zero on the critical line; "Majorana" and "horizon" are
  interpretations to investigate, not statements proved here.

No RH claim.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace GppFermionSector

/-! ### Traces over the Boolean cube -/

theorem fermi_trace {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℂ) :
    ∑ S ∈ P.powerset, ∏ i ∈ S, x i = ∏ i ∈ P, (1 + x i) := by
  rw [Finset.prod_one_add]

theorem fermi_supertrace {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℂ) :
    ∑ S ∈ P.powerset, (-1 : ℂ) ^ S.card * ∏ i ∈ S, x i = ∏ i ∈ P, (1 - x i) := by
  have h := Finset.prod_one_add (s := P) (f := fun i => -x i)
  rw [show ∏ i ∈ P, (1 - x i) = ∏ i ∈ P, (1 + -x i) from
    Finset.prod_congr rfl fun i _ => by ring, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_neg]

/-- Per prime: the ordinary fermionic factor is the ratio of bosonic factors at `s` and `2s`. -/
theorem fermi_trace_eq (x : ℂ) (hx : 1 - x ≠ 0) : 1 + x = (1 - x ^ 2) / (1 - x) := by
  field_simp
  ring

theorem boson_mul_supertrace {ι : Type*} (P : Finset ι) (x : ι → ℂ) (hx : ∀ i, 1 - x i ≠ 0) :
    (∏ i ∈ P, (1 - x i)⁻¹) * ∏ i ∈ P, (1 - x i) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (hx i)

/-- The global supertrace: `Σ μ(n) n^{-s} = 1/ζ(s)` for `Re s > 1`. -/
theorem moebius_lseries_eq_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have h := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at h
  exact eq_inv_of_mul_eq_one_right h

/-! ### The correspondence with squarefree integers -/

theorem prodPrimes_injective {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (h : ∏ p ∈ P, p = ∏ p ∈ Q, p) : P = Q := by
  rw [← Nat.primeFactors_prod hP, ← Nat.primeFactors_prod hQ, h]

theorem moebius_prodPrimes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    (μ (∏ p ∈ P, p) : ℤ) = (-1) ^ P.card := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert a P ha ih =>
    have haP : a.Prime := hP a (Finset.mem_insert_self a P)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ P, p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes haP (hP' q hq)).mpr (fun h => ha (h ▸ hq))
    rw [Finset.prod_insert ha, isMultiplicative_moebius.map_mul_of_coprime hcop,
      moebius_apply_prime haP, ih hP', Finset.card_insert_of_notMem ha, pow_succ]
    ring

/-! ### The explicit supersymmetric pairing for one prime -/

/-- Basis states `(k, b)`: boson occupation `k`, fermion occupation `b`. -/
abbrev St := ℕ × Bool

/-- The supercharge `Q |k, 1⟩ = √(k+1) |k+1, 0⟩`, `Q |·, 0⟩`-source states annihilated. As a map on
coefficient functions: `(Qψ)(k+1, 0) = √(k+1) ψ(k, 1)`, and `Qψ = 0` elsewhere. -/
noncomputable def Q (ψ : St → ℂ) : St → ℂ
  | (k, b) => if b = false ∧ k ≠ 0 then (Real.sqrt k : ℂ) * ψ (k - 1, true) else 0

/-- Its adjoint: `(Q†ψ)(k, 1) = √(k+1) ψ(k+1, 0)`, and `Q†ψ = 0` elsewhere. -/
noncomputable def Qd (ψ : St → ℂ) : St → ℂ
  | (k, b) => if b = true then (Real.sqrt (k + 1) : ℂ) * ψ (k + 1, false) else 0

/-- The number operator `N_b + N_f`. -/
def N (ψ : St → ℂ) : St → ℂ
  | (k, b) => ((k + (if b then 1 else 0) : ℕ) : ℂ) * ψ (k, b)

theorem Q_sq (ψ : St → ℂ) : Q (Q ψ) = 0 := by
  funext ⟨k, b⟩
  cases b <;> simp [Q]

theorem Qd_sq (ψ : St → ℂ) : Qd (Qd ψ) = 0 := by
  funext ⟨k, b⟩
  cases b <;> simp [Qd]

/-- **`{Q, Q†} = N_b + N_f`.** -/
theorem anticomm (ψ : St → ℂ) : (fun s => Q (Qd ψ) s + Qd (Q ψ) s) = N ψ := by
  funext ⟨k, b⟩
  cases b
  · by_cases hk : k = 0
    · subst hk; simp [Q, Qd, N]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have h : ((Real.sqrt ((j : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((j : ℝ) + 1) : ℝ) : ℂ) =
          (j : ℂ) + 1 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
      simp [Q, Qd, N]
      rw [← mul_assoc, h]
  · have h : ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) =
        (k : ℂ) + 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    simp [Q, Qd, N]
    rw [← mul_assoc, h]

/-- **The supertrace of the paired spectrum is `1`** (the unpaired vacuum): the terms
`x^k` (fermion off) and `x^{k+1}` (fermion on, paired with `|k+1, 0⟩`) telescope. -/
theorem telescope (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun k : ℕ => x ^ k - x ^ (k + 1)) 1 := by
  have hg := hasSum_geometric_of_lt_one h0 h1
  have h2 := hg.mul_left x
  have h3 := hg.sub h2
  have e : (fun k : ℕ => x ^ k - x ^ (k + 1)) = fun k : ℕ => x ^ k - x * x ^ k := by
    funext k; ring
  rw [e]
  have hne : (1 - x) ≠ 0 := by linarith
  have v : (1 - x)⁻¹ - x * (1 - x)⁻¹ = 1 := by field_simp
  rwa [v] at h3

/-! ### The global trace dictionary (Re `s > 1`) -/

theorem norm_prime_cpow_lt_one {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by simp; linarith)

open Filter Topology in
/-- **Ordinary fermionic trace**: `∏_p (1 + p^{-s}) = ζ(s)/ζ(2s)`. -/
theorem fermi_global_trace {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 + (p : ℂ) ^ (-s)) (riemannZeta s / riemannZeta (2 * s)) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have h2 := riemannZeta_eulerProduct_hasProd hs2
  have hne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  unfold HasProd at h1 h2 ⊢
  refine (h1.div h2 hne).congr fun T => ?_
  simp only [Pi.div_apply]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx := norm_prime_cpow_lt_one hs p
  have h1x : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hx; exact lt_irrefl _ hx
  have e : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [← Complex.cpow_nat_mul]; push_cast; congr 1; ring
  rw [e]
  have h1x2 : 1 - ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
    intro h
    have : ((p : ℂ) ^ (-s)) ^ 2 = 1 := (sub_eq_zero.mp h).symm
    have hn : ‖((p : ℂ) ^ (-s)) ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg ((p : ℂ) ^ (-s))]
    rw [this, norm_one] at hn; exact lt_irrefl _ hn
  field_simp
  ring

open Filter Topology in
/-- **Fermionic supertrace**: `∏_p (1 − p^{-s}) = 1/ζ(s)`. -/
theorem fermi_global_supertrace {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 - (p : ℂ) ^ (-s)) (riemannZeta s)⁻¹ := by
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  unfold HasProd at h1 ⊢
  refine (h1.inv₀ hne).congr fun T => ?_
  rw [Finset.prod_inv_distrib]
  simp

end GppFermionSector
