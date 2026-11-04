import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Feynman's checkerboard: mass is the reversal amplitude

Feynman's checkerboard (Feynman–Hibbs, *Quantum Mechanics and Path Integrals*, Problem 2-6;
Jacobson–Schulman, J. Phys. A 17 (1984) 375) builds the 1+1-dimensional Dirac propagator from
paths that always move at the speed of light, one lattice step per time step, and pick up a factor
`iεm` each time they reverse direction. This file proves the exact finite combinatorics, for
Daniel Toupin's *Which Way Is Forward?* (zitter temporal-lift conjecture, falsifier F8), with AI
assistance from Claude Code.

A path is a direction sequence `p : Fin (n+1) → Bool` (`true` = right-moving). Its weight is
`∏ turn · ∏ step`: a factor `w` at each reversal and a factor `zr` / `zl` for each right / left
step (in momentum space `zr = e^{iθ}`, `zl = e^{-iθ}`).

* `pathSum_eq` (**checkerboard theorem**): the sum of the weights of all paths that start in
  direction `a` and end in direction `b` equals `step a · (Tⁿ)_{ab}`, where `T` is the one-step
  transfer matrix `T_{ab} = turn(a,b) · step(b)`. The path sum is the discrete two-component
  Dirac evolution.
* `turn_prod_eq_pow`, `step_prod_eq_pow`: the weight is `w^(number of reversals)` times
  `zr^(#right) zl^(#left)`, i.e. the reversal count and the net displacement.
* `transfer_pow_massless`: at `w = 0` (no mass) the evolution is diagonal, so only the two straight
  light-cone paths contribute: a massless particle never turns.
* `transfer_sq`, `transfer_sq_physical`: Cayley–Hamilton for `T`. With `w = iεm` and momentum `θ`,
  `T² = 2 cos θ · T − (1 + ε²m²) I`, so after the normalisation `T/√(1+ε²m²)` the eigenphases `ω`
  obey `cos ω = cos θ / √(1+ε²m²)`, the lattice dispersion whose `ε → 0` limit is `E² = p² + m²`.

Scope: exact finite algebra in 1+1 dimensions. The continuum limit, the normalisation to a unitary
step, and any 3+1-dimensional version are not formalized; the 3+1 checkerboard is a known open
problem. This supports "mass is the rate of reversals" in the checkerboard model; it does not prove
the zitter temporal-lift conjecture of the paper, which concerns a covariant 3+1 construction.
-/

open Finset

namespace GppCheckerboard

variable {R : Type*} [CommRing R]

/-- Turn factor: `1` if the direction is kept, `w` (Feynman's `iεm`) at a reversal. -/
def turn (w : R) (a b : Bool) : R := if a = b then 1 else w

/-- Step factor: `zr` for a right-moving step, `zl` for a left-moving step. -/
def step (zr zl : R) (d : Bool) : R := if d then zr else zl

/-- Weight of a path of `n+1` light-speed steps with directions `p`. -/
def weight (w zr zl : R) {n : ℕ} (p : Fin (n + 1) → Bool) : R :=
  (∏ i : Fin n, turn w (p i.castSucc) (p i.succ)) * ∏ i : Fin (n + 1), step zr zl (p i)

/-- One-step transfer matrix. -/
def transfer (w zr zl : R) : Matrix Bool Bool R := Matrix.of fun a b => turn w a b * step zr zl b

theorem weight_snoc (w zr zl : R) {n : ℕ} (q : Fin (n + 1) → Bool) (c : Bool) :
    weight w zr zl (Fin.snoc q c : Fin (n + 2) → Bool) =
      weight w zr zl q * transfer w zr zl (q (Fin.last n)) c := by
  unfold weight transfer
  rw [Matrix.of_apply]
  rw [Fin.prod_univ_castSucc (fun i : Fin (n + 1) => turn w _ _),
    Fin.prod_univ_castSucc (fun i : Fin (n + 2) => step zr zl _)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc]
  ring

/-- **Checkerboard theorem.** Summing the weights of all light-speed zigzag paths that start in
direction `a` and end in direction `b` gives the `(a,b)` entry of the transfer-matrix power. -/
theorem pathSum_eq (w zr zl : R) (n : ℕ) (a b : Bool) :
    (∑ p : Fin (n + 1) → Bool,
      if p 0 = a ∧ p (Fin.last n) = b then weight w zr zl p else 0) =
      step zr zl a * (transfer w zr zl ^ n) a b := by
  induction n generalizing b with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    simp [weight, pow_zero, Matrix.one_apply]
    cases a <;> cases b <;> simp
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => Bool)).sum_comp, Fintype.sum_prod_type]
    have h0 : ∀ (q : Fin (n + 1) → Bool) (c : Bool),
        (Fin.snoc q c : Fin (n + 2) → Bool) 0 = q 0 := by
      intro q c
      exact Fin.snoc_castSucc (α := fun _ => Bool) (p := q) (x := c) (i := 0)
    have key : ∀ (c : Bool) (q : Fin (n + 1) → Bool),
        (if (Fin.snoc q c : Fin (n + 2) → Bool) 0 = a ∧
            (Fin.snoc q c : Fin (n + 2) → Bool) (Fin.last (n + 1)) = b
          then weight w zr zl (Fin.snoc q c : Fin (n + 2) → Bool) else 0) =
        if c = b then ∑ d : Bool, (if q 0 = a ∧ q (Fin.last n) = d then weight w zr zl q else 0) *
          transfer w zr zl d b else 0 := by
      intro c q
      rw [h0, Fin.snoc_last, weight_snoc, Fintype.sum_bool]
      by_cases hc : c = b
      · subst hc
        by_cases ha : q 0 = a <;> cases q (Fin.last n) <;> simp [ha]
      · simp [hc]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q _ => key c q).trans ?_
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ b), Finset.sum_comm]
    simp only [← Finset.sum_mul, ih, pow_succ, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- The turn product counts reversals: it is `w ^ (number of reversals)`. -/
theorem turn_prod_eq_pow (w : R) {n : ℕ} (p : Fin (n + 1) → Bool) :
    (∏ i : Fin n, turn w (p i.castSucc) (p i.succ)) =
      w ^ (univ.filter fun i : Fin n => p i.castSucc ≠ p i.succ).card := by
  unfold turn
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

/-- The step product records displacement: `zr ^ (#right) * zl ^ (#left)`. -/
theorem step_prod_eq_pow (zr zl : R) {n : ℕ} (p : Fin (n + 1) → Bool) :
    (∏ i : Fin (n + 1), step zr zl (p i)) =
      zr ^ (univ.filter fun i => p i = true).card * zl ^ (univ.filter fun i => ¬ p i = true).card := by
  unfold step
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]

/-- Massless case: with no reversal amplitude the transfer matrix is diagonal, so only the two
straight light-cone paths survive. -/
theorem transfer_pow_massless (zr zl : R) (n : ℕ) :
    transfer 0 zr zl ^ n = Matrix.diagonal fun d => step zr zl d ^ n := by
  have h : transfer (0 : R) zr zl = Matrix.diagonal fun d => step zr zl d := by
    ext a b; cases a <;> cases b <;> simp [transfer, turn, step]
  rw [h, Matrix.diagonal_pow]
  rfl

/-- Dispersion (Cayley–Hamilton): `T² = (zr + zl) T − zr zl (1 − w²) I`. -/
theorem transfer_sq (w zr zl : R) :
    transfer w zr zl ^ 2 = (zr + zl) • transfer w zr zl - (zr * zl * (1 - w ^ 2)) • (1 : Matrix Bool Bool R) := by
  ext a b
  cases a <;> cases b <;>
    simp [sq, Matrix.mul_apply, transfer, turn, step] <;> ring

/-- Physical form: with `zr = e^{iθ}`, `zl = e^{-iθ}` (momentum `θ` per step) and reversal amplitude
`w = i ε m`, the one-step evolution satisfies `T² = 2 cos θ · T − (1 + ε² m²) I`. -/
theorem transfer_sq_physical (θ ε m : ℝ) :
    transfer (Complex.I * (ε * m)) (Complex.exp (θ * Complex.I)) (Complex.exp (-(θ * Complex.I))) ^ 2 =
      (2 * Complex.cos θ) • transfer (Complex.I * (ε * m)) (Complex.exp (θ * Complex.I))
          (Complex.exp (-(θ * Complex.I))) -
        ((1 : ℂ) + (ε * m) ^ 2) • (1 : Matrix Bool Bool ℂ) := by
  rw [transfer_sq]
  have h1 : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) = 2 * Complex.cos θ := by
    rw [Complex.cos]; ring_nf
  rw [h1, h2]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

end GppCheckerboard
