import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import GppVerify.QuantumFieldTheory.ArithmeticFock

/-!
# Gibbs layer for the arithmetic Fock space — Track 1, T5

Analytic layer atop the algebraic Fock core (`ArithmeticFock`):
Bargmann (factorial-weighted) inner product, adjointness of
creation/annihilation on basis vectors, Gibbs-trace reindexing,
and the partition-function identity `Z₀(β) = ζ(β)` for `β > 1`.

Epistemic label: **LEAN-CHECKED** (kernel, zero `sorry`, standard axioms only).
-/

namespace FockGibbs

open ArithmeticFock
open Finsupp

variable {ι : Type*} [DecidableEq ι]

/-! ## Bargmann inner product (factorial-weighted) -/

/-- Factorial weight of a configuration: `∏_i (c i)!`, as a complex number.
    This is the Bargmann weight making `create`/`annihilate` adjoints. -/
noncomputable def configWeight (c : Config ι) : ℂ :=
  c.prod fun _ r => ((Nat.factorial r : ℕ) : ℂ)

/-- The Bargmann inner product: `⟪f, g⟫ = Σ_c conj(f c) * g c * weight(c)`.
    Finite sum since `f` is finitely supported. -/
noncomputable def bargmannInner (f g : Fock ι) : ℂ :=
  f.sum fun c z => (star z) * (g c * configWeight c)

/-- Orthonormality (weighted): basis vectors are orthogonal, with norm-squared
    equal to the factorial weight. -/
theorem bargmannInner_single_single (c d : Config ι) :
    bargmannInner (Finsupp.single c 1) (Finsupp.single d 1)
      = if c = d then configWeight c else 0 := by
  unfold bargmannInner
  rw [Finsupp.sum, Finsupp.support_single c (by norm_num : (1:ℂ) ≠ 0),
    Finset.sum_singleton]
  simp only [Finsupp.single_apply, if_true, star_one, one_mul]
  by_cases h : d = c
  · have h' : c = d := h.symm
    rw [if_pos h, if_pos h', one_mul]
  · rw [if_neg h]
    have h' : ¬ (c = d) := fun he => h he.symm
    rw [if_neg h', zero_mul]

/-- The inner product with zero on the right vanishes. -/
theorem bargmannInner_single_zero (c : Config ι) :
    bargmannInner (Finsupp.single c 1) 0 = 0 := by
  unfold bargmannInner
  rw [Finsupp.sum, Finsupp.support_single c (by norm_num : (1:ℂ) ≠ 0),
    Finset.sum_singleton]
  simp

/-- Key weight relation: adding a quantum multiplies the weight by `(c i + 1)`. -/
theorem configWeight_add_unitOcc (i : ι) (c : Config ι) :
    configWeight (c + unitOcc i) = ((c i + 1 : ℕ) : ℂ) * configWeight c := by
  unfold configWeight
  have hsupp : (c + unitOcc i).support = insert i c.support := by
    ext j
    simp only [Finsupp.mem_support_iff, Finset.mem_insert, Finsupp.add_apply,
      unitOcc_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact iff_of_true (Nat.succ_ne_zero _) (Or.inl rfl)
    · rw [if_neg (Ne.symm h), add_zero]
      constructor
      · intro hj; exact Or.inr hj
      · rintro (he | hj)
        · exact absurd he.symm h
        · exact hj
  have hi : (c + unitOcc i) i = c i + 1 := by
    rw [Finsupp.add_apply, unitOcc_apply, if_pos rfl]
  have hprod_erase : ∏ j ∈ c.support.erase i, ((((c + unitOcc i) j).factorial : ℕ):ℂ)
      = ∏ j ∈ c.support.erase i, ((((c j).factorial : ℕ)):ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h1 : (c + unitOcc i) j = c j := by
      rw [Finsupp.add_apply, unitOcc_apply, if_neg hji, add_zero]
    rw [h1]
  have lhs_eq : (c + unitOcc i).prod (fun _ r => ((Nat.factorial r : ℕ):ℂ))
      = (((c i + 1).factorial : ℕ):ℂ) * ∏ j ∈ c.support.erase i, ((((c j).factorial : ℕ)):ℂ) := by
    have hins : insert i c.support = insert i (c.support.erase i) := by
      apply Finset.ext; intro j
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [show (c + unitOcc i).prod (fun _ r => ((Nat.factorial r : ℕ):ℂ))
        = ∏ j ∈ (c + unitOcc i).support, ((((c + unitOcc i) j).factorial : ℕ):ℂ) from rfl,
      hsupp, hins, Finset.prod_insert (Finset.notMem_erase i _), hi, hprod_erase]
  have rhs_eq : c.prod (fun _ r => ((Nat.factorial r : ℕ):ℂ))
      = ∏ j ∈ c.support, ((((c j).factorial : ℕ)):ℂ) := rfl
  rw [lhs_eq, rhs_eq]
  have hfact : (((c i + 1).factorial : ℕ):ℂ) = ((c i + 1 : ℕ):ℂ) * ((((c i).factorial : ℕ)):ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  by_cases hi_mem : i ∈ c.support
  · rw [← Finset.mul_prod_erase _ _ hi_mem]
    ring
  · have herase : c.support.erase i = c.support := Finset.erase_eq_of_notMem hi_mem
    rw [herase]
    have hci : c i = 0 := Finsupp.notMem_support_iff.mp hi_mem
    rw [hci]
    simp

/-! ## Adjointness of creation/annihilation (Task 2) -/

/-- Adjointness on basis vectors: `⟪a†_i c, d⟫ = ⟪c, a_i d⟫`
    for the Bargmann (factorial-weighted) inner product. -/
theorem adjoint_create_annihilate_single (i : ι) (c d : Config ι) :
    bargmannInner (create i (Finsupp.single c 1)) (Finsupp.single d 1)
      = bargmannInner (Finsupp.single c 1) (annihilate i (Finsupp.single d 1)) := by
  rw [ArithmeticFock.create_single_one, ArithmeticFock.annihilate_single_one,
    bargmannInner_single_single]
  by_cases hdi : d i = 0
  · rw [if_pos hdi, bargmannInner_single_zero]
    -- LHS: if (c + unitOcc i = d) then weight(d) else 0 = 0
    -- Since d i = 0 but (c + unitOcc i) i = c i + 1 ≠ 0, they can't be equal
    have hne : c + unitOcc i ≠ d := by
      intro he
      have e1 : (c + unitOcc i) i = c i + 1 := by
        rw [Finsupp.add_apply, unitOcc_apply, if_pos rfl]
      rw [he] at e1
      rw [hdi] at e1
      exact Nat.succ_ne_zero (c i) e1.symm
    rw [if_neg hne]
  · rw [if_neg hdi]
    -- Linearity in second argument for basis vectors
    have hsmul : bargmannInner (Finsupp.single c 1)
        ((d i : ℂ) • Finsupp.single (predOcc i d) 1)
        = (d i : ℂ) * bargmannInner (Finsupp.single c 1)
            (Finsupp.single (predOcc i d) 1) := by
      unfold bargmannInner
      rw [Finsupp.sum, Finsupp.support_single c (by norm_num : (1:ℂ) ≠ 0),
        Finset.sum_singleton, Finsupp.sum, Finsupp.support_single c (by norm_num : (1:ℂ) ≠ 0),
        Finset.sum_singleton]
      simp only [Finsupp.single_apply, if_true, star_one, one_mul, Finsupp.smul_apply,
        smul_eq_mul]
      ring
    rw [hsmul, bargmannInner_single_single]
    by_cases heq : c + unitOcc i = d
    · rw [if_pos heq]
      have hcd : c = predOcc i d := by
        have e := congrArg (predOcc i) heq
        rw [predOcc_add_unitOcc] at e
        exact e
      rw [if_pos hcd, configWeight_add_unitOcc]
      have hdi : d i = c i + 1 := by
        rw [← heq, Finsupp.add_apply, unitOcc_apply, if_pos rfl]
      rw [hdi]
    · rw [if_neg heq]
      by_cases hcp : c = predOcc i d
      · exfalso
        have hd_eq : d = c + unitOcc i := by
          rw [hcp]
          exact (unitOcc_add_predOcc hdi).symm
        exact heq hd_eq.symm
      · rw [if_neg hcp, mul_zero]

/-! ## Gibbs trace and partition function (Tasks 3 & 4) -/

/-- Gibbs weight of a configuration: `exp(-β * log(toNat c)) = (toNat c)^{-β}`. -/
noncomputable def gibbsWeight (β : ℝ) (c : Config PrimeIdx) : ℝ :=
  Real.exp (-β * Real.log (toNat c))

/-- The Gibbs weight equals `(toNat c)^{-β}` as a real power. -/
theorem gibbsWeight_eq_rpow (β : ℝ) (c : Config PrimeIdx) :
    gibbsWeight β c = ((toNat c : ℝ) ^ (-β)) := by
  unfold gibbsWeight
  have hpos : (0:ℝ) < (toNat c : ℝ) := by
    have h := toNat_ne_zero c
    exact_mod_cast Nat.pos_of_ne_zero h
  rw [Real.rpow_def_of_pos hpos, mul_comm]

/-- Partition function: sum of Gibbs weights over all configurations. -/
noncomputable def partitionFn (β : ℝ) : ℝ :=
  ∑' c, gibbsWeight β c

/-- Equivalence between configurations and positive naturals. -/
noncomputable def configEquivPosNat : Config PrimeIdx ≃ {n : ℕ // n ≠ 0} where
  toFun c := ⟨toNat c, toNat_ne_zero c⟩
  invFun n := fromNat n.val
  left_inv c := fromNat_toNat c
  right_inv n := by
    obtain ⟨n, hn⟩ := n
    simp only
    have h := toNat_fromNat hn
    -- Goal: ⟨toNat (fromNat n), _⟩ = ⟨n, hn⟩
    apply Subtype.ext
    exact h

/-- Reindexing: the partition function equals the sum over positive naturals. -/
theorem partitionFn_eq_tsum_posNat (β : ℝ) :
    partitionFn β = ∑' (n : {n : ℕ // n ≠ 0}), ((n.val : ℝ) ^ (-β)) := by
  unfold partitionFn
  rw [← configEquivPosNat.symm.tsum_eq]
  apply tsum_congr
  intro n
  show gibbsWeight β (fromNat n.val) = ((n.val : ℝ) ^ (-β))
  rw [gibbsWeight_eq_rpow, toNat_fromNat n.property]

/-- Equivalence between ℕ and positive naturals (as subtype). -/
noncomputable def natEquivPosNat : ℕ ≃ {n : ℕ // n ≠ 0} where
  toFun m := ⟨m + 1, by simp⟩
  invFun n := n.val - 1
  left_inv m := by simp
  right_inv n := by
    obtain ⟨n, hn⟩ := n
    apply Subtype.ext
    simp only
    omega

/-! ## Task 4 (CLOSED): Z₀(β) = ζ(β) -/

/-- **Partition function = Riemann zeta.** For `β > 1`, the Gibbs partition
function of the arithmetic Fock space, cast to `ℂ`, equals `riemannZeta (β : ℂ)`.
Proof: reindex configurations to positive naturals (`partitionFn_eq_tsum_posNat`),
shift to all naturals (`natEquivPosNat`), push the cast through the sum
(`Complex.ofReal_tsum`), identify terms via `Complex.ofReal_cpow`, and finish
with Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow`. -/
theorem partitionFn_eq_riemannZeta (β : ℝ) (hβ : 1 < β) :
    (partitionFn β : ℂ) = riemannZeta (β : ℂ) := by
  have hre : 1 < Complex.re (β : ℂ) := by simpa using hβ
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, partitionFn_eq_tsum_posNat β,
    ← natEquivPosNat.tsum_eq]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro m
  have hval : ((natEquivPosNat m).val : ℝ) = (m : ℝ) + 1 := by
    simp [natEquivPosNat]
  rw [hval, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  push_cast
  rw [Complex.cpow_neg, inv_eq_one_div]

end FockGibbs
