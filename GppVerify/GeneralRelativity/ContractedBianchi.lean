import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

/-!
# The contracted Bianchi identity: `∇_μ G^μ_ν = 0`

At a point, in components over a finite index type `ι`, write `DR l a b c d` for
`∇_l R_{abcd}`, the covariant derivative of the Riemann tensor, and `gi` for the inverse
metric. We assume only

* the algebraic symmetries `R_{abcd} = -R_{bacd} = -R_{abdc} = R_{cdab}` (inherited by
  `∇_l R`, since `∇` is linear),
* the **second Bianchi identity** `∇_l R_{abcd} + ∇_a R_{blcd} + ∇_b R_{lacd} = 0`,
* `∇ g = 0` (metric compatibility), which is what lets contractions with `gi` commute with
  `∇`; it is encoded by writing `∇_l R_{bd}` and `∇_l R` as contractions of `DR`,
* `gi` symmetric and `gi * g = 1`.

From these we prove `∇^b R_{bν} = ½ ∇_ν R` (`twice_div_ricci`) and hence that the Einstein
tensor `G_{bν} = R_{bν} - ½ g_{bν} R` is divergence free, `g^{lb} ∇_l G_{bν} = 0`
(`divEinstein_eq_zero`). This is the identity that makes `G = 8πT` compatible with
`∇·T = 0`.

**Scope.** The second Bianchi identity is a hypothesis here, not derived from a connection
(Mathlib has no Levi-Civita connection on a pseudo-Riemannian manifold yet); everything
after it is proved. Valid in any dimension and any signature.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code.
-/

namespace GppContractedBianchi

open Finset

variable {ι : Type*} [Fintype ι]

/-- `∇_l R_{bd} = g^{ac} ∇_l R_{abcd}` (contraction of the 1st and 3rd slots). -/
def dRic (gi : Matrix ι ι ℝ) (DR : ι → ι → ι → ι → ι → ℝ) (l b d : ι) : ℝ :=
  ∑ a, ∑ c, gi a c * DR l a b c d

/-- `∇_l R = g^{bd} ∇_l R_{bd}`. -/
def dScal (gi : Matrix ι ι ℝ) (DR : ι → ι → ι → ι → ι → ℝ) (l : ι) : ℝ :=
  ∑ b, ∑ d, gi b d * dRic gi DR l b d

/-- The divergence `g^{lb} ∇_l G_{bν}` of the Einstein tensor. -/
noncomputable def divEinstein (g gi : Matrix ι ι ℝ) (DR : ι → ι → ι → ι → ι → ℝ) (ν : ι) : ℝ :=
  ∑ l, ∑ b, gi l b * (dRic gi DR l b ν - 1 / 2 * g b ν * dScal gi DR l)

variable {g gi : Matrix ι ι ℝ} {DR : ι → ι → ι → ι → ι → ℝ}

/-- The derivative of the Ricci tensor is symmetric. -/
lemma dRic_symm (hgi : ∀ a c, gi a c = gi c a)
    (hpair : ∀ l a b c d, DR l a b c d = DR l c d a b) (l b d : ι) :
    dRic gi DR l b d = dRic gi DR l d b := by
  unfold dRic
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hgi, hpair]

private lemma reorder (F : ι → ι → ι → ι → ℝ) :
    ∑ b, ∑ d, ∑ a, ∑ c, F b d a c = ∑ a, ∑ c, ∑ d, ∑ b, F b d a c := by
  calc ∑ b, ∑ d, ∑ a, ∑ c, F b d a c = ∑ b, ∑ a, ∑ d, ∑ c, F b d a c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ d, ∑ c, F b d a c := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, F b d a c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ b, ∑ d, F b d a c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, F b d a c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Twice-contracted second Bianchi identity:** `∇_l R = 2 g^{ac} ∇_a R_{cl}`. -/
theorem twice_div_ricci (hgi : ∀ a c, gi a c = gi c a)
    (h1 : ∀ l a b c d, DR l a b c d = -DR l b a c d)
    (h2 : ∀ l a b c d, DR l a b c d = -DR l a b d c)
    (hpair : ∀ l a b c d, DR l a b c d = DR l c d a b)
    (hB : ∀ l a b c d, DR l a b c d + DR a b l c d + DR b l a c d = 0) (l : ι) :
    dScal gi DR l = 2 * ∑ a, ∑ c, gi a c * dRic gi DR a c l := by
  have hsum : ∑ b, ∑ d, ∑ a, ∑ c,
      gi b d * (gi a c * (DR l a b c d + DR a b l c d + DR b l a c d)) = 0 := by
    simp [hB]
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  -- first term: the scalar curvature derivative
  have T1 : ∑ b, ∑ d, ∑ a, ∑ c, gi b d * (gi a c * DR l a b c d) = dScal gi DR l := by
    simp only [dScal, dRic, Finset.mul_sum]
  -- third term: `R_{lacd} = -R_{alcd}`
  have T3 : ∑ b, ∑ d, ∑ a, ∑ c, gi b d * (gi a c * DR b l a c d) =
      -∑ a, ∑ c, gi a c * dRic gi DR a c l := by
    have : ∑ b, ∑ d, ∑ a, ∑ c, gi b d * (gi a c * DR b l a c d) =
        -∑ b, ∑ d, gi b d * dRic gi DR b l d := by
      simp only [dRic, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [h1 b l a c d]
      ring
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    rw [dRic_symm hgi hpair]
  -- second term: `R_{blcd} = -R_{dcbl}`
  have T2 : ∑ b, ∑ d, ∑ a, ∑ c, gi b d * (gi a c * DR a b l c d) =
      -∑ a, ∑ c, gi a c * dRic gi DR a c l := by
    rw [reorder (fun b d a c => gi b d * (gi a c * DR a b l c d))]
    simp only [dRic, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
    have hR : DR a b l c d = -DR a d c b l := by
      rw [h1 a b l c d, hpair a l b c d, h2 a c d l b, h1 a c d b l]
      ring
    rw [hR, hgi b d]
    ring
  rw [T1, T2, T3] at hsum
  linarith

/-- **The contracted Bianchi identity.** The Einstein tensor is divergence free:
`g^{lb} ∇_l (R_{bν} - ½ g_{bν} R) = 0`. -/
theorem divEinstein_eq_zero [DecidableEq ι] (hgi : ∀ a c, gi a c = gi c a)
    (hinv : gi * g = 1)
    (h1 : ∀ l a b c d, DR l a b c d = -DR l b a c d)
    (h2 : ∀ l a b c d, DR l a b c d = -DR l a b d c)
    (hpair : ∀ l a b c d, DR l a b c d = DR l c d a b)
    (hB : ∀ l a b c d, DR l a b c d + DR a b l c d + DR b l a c d = 0) (ν : ι) :
    divEinstein g gi DR ν = 0 := by
  have hδ : ∀ l, ∑ b, gi l b * g b ν = if l = ν then 1 else 0 := fun l => by
    have := congrFun (congrFun hinv l) ν
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hsplit : divEinstein g gi DR ν =
      ∑ l, ∑ b, gi l b * dRic gi DR l b ν -
        1 / 2 * ∑ l, (∑ b, gi l b * g b ν) * dScal gi DR l := by
    simp only [divEinstein, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit]
  simp only [hδ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [twice_div_ricci hgi h1 h2 hpair hB ν]
  ring

end GppContractedBianchi
