import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Thread E: the Euler-sum capstone (`M₂ = 1/90 = ζ(4)/π⁴`)

From `haar_qg_paper_v2151.tex` base case `L = 2`: the physics paper reconstructs the
constant `M₂ = 1/90` via a route through two linear Euler sums, rather than by directly
citing the closed form of `ζ(4)`:
`Σₙ (ζ(2)−H_n⁽²⁾)/n² = π⁴/120 = (3/4)ζ(4)` and
`Σₘ (ζ(3)−H_{m−1}⁽³⁾)/m = π⁴/72 = (5/4)ζ(4)`, whose sum `2ζ(4) = π⁴/45` gives `M₂ = 1/90`.

**What this file actually formalizes.** `M₂ = ζ(4)/π⁴ = 1/90` itself is already an immediate
consequence of Mathlib's `hasSum_zeta_four` and needs no new work. The genuine mathematical
content of this thread is the *alternate* derivation via the two Euler sums, which is a
nontrivial cross-check that the physics paper's route reproduces the same known constant.
Both sums are values of Σ_{m<n} 1/(m^a n^b)-type double sums (in modern language, depth-2
multiple zeta values), which Mathlib does not have a library for (no
`Mathlib.NumberTheory.MultipleZetaValues` file exists as of the pinned commit).

* **First sum** (`euler_sum_one`): reduces to the symmetric double-sum decomposition
  `2·Σ_{m≤n} 1/(m²n²) = ζ(2)² + ζ(4)` — pure `ℕ×ℕ` tsum bookkeeping, proved here in full via
  `Summable.mul_of_nonneg` / `tsum_mul_tsum_of_summable_norm` for the full product sum,
  `Summable.subtype` + a hand-built swap `Equiv` for the reflection symmetry
  `Σ_{m<n} = Σ_{m>n}`, and `Summable.tsum_union_disjoint` /
  `Summable.tsum_subtype_add_tsum_subtype_compl` for the diagonal/off-diagonal split.
* **Second sum** (Euler's `Σ Hₙ/n³ = (5/4)ζ(4)`): genuinely harder — the summand
  `(1/m)·(1/n³)` for `m ≤ n` is *not* symmetric under swapping `m,n`, so the reflection trick
  above does not apply; the reindexing needed is a different (asymmetric) double-sum identity
  (`Σₙ Hₙ/n³ = ζ(3,1) + ζ(4)` in MZV language, using the classical but unformalized fact
  `ζ(3,1) = π⁴/360`). **Not formalized here** — left as an honest, explicitly-named gap,
  exactly as `docs/FORMALIZATION_PLAN.md` anticipates ("if it resists, land the first sum +
  the assembly with the second's exact gap named").
-/

namespace GppEulerSum

open Real

/-- The symmetric pairwise term `1/(m²n²)`. Reducible (`abbrev`, not `def`): this term
    needs to unify against raw lambdas produced by generic `tsum`/`Summable` combinators
    (e.g. `Summable.mul_of_nonneg`'s conclusion), and a semireducible `def` there causes the
    elaborator's unifier to time out rather than unfold. -/
noncomputable abbrev term (p : ℕ × ℕ) : ℝ := (1 / (p.1 : ℝ) ^ 2) * (1 / (p.2 : ℝ) ^ 2)

theorem term_swap (p : ℕ × ℕ) : term p.swap = term p := by
  unfold term
  simp only [Prod.swap]
  ring

theorem nonneg_inv_sq (n : ℕ) : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity

set_option maxHeartbeats 1000000 in
theorem summable_prod_inv_sq :
    Summable (fun x : ℕ × ℕ => (1 / (x.1 : ℝ) ^ 2) * (1 / (x.2 : ℝ) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  exact h2.mul_of_nonneg h2 nonneg_inv_sq nonneg_inv_sq

set_option maxHeartbeats 1000000 in
theorem summable_term : Summable term := summable_prod_inv_sq

set_option maxHeartbeats 1000000 in
theorem hasSum_term : HasSum (fun x : ℕ × ℕ => (1 / (x.1 : ℝ) ^ 2) * (1 / (x.2 : ℝ) ^ 2))
    ((Real.pi ^ 2 / 6) * (Real.pi ^ 2 / 6)) :=
  hasSum_zeta_two.mul hasSum_zeta_two summable_prod_inv_sq

theorem tsum_term_eq : ∑' p : ℕ × ℕ, term p = (Real.pi ^ 2 / 6) ^ 2 := by
  unfold term
  rw [hasSum_term.tsum_eq]
  ring

/-- The diagonal `m = n`. -/
def Dg : Set (ℕ × ℕ) := {p | p.1 = p.2}

/-- The strict lower-triangle `m < n`. -/
def Lt : Set (ℕ × ℕ) := {p | p.1 < p.2}

/-- The strict upper-triangle `m > n`. -/
def Gt : Set (ℕ × ℕ) := {p | p.2 < p.1}

/-- The diagonal parametrized by `ℕ`, via `n ↦ (n, n)`. -/
def diagEquiv : ℕ ≃ Dg where
  toFun n := ⟨(n, n), rfl⟩
  invFun p := p.1.1
  left_inv n := rfl
  right_inv p := by
    obtain ⟨⟨a, b⟩, (h : a = b)⟩ := p
    subst h
    rfl

@[simp] theorem diagEquiv_coe (n : ℕ) : ((diagEquiv n : Dg) : ℕ × ℕ) = (n, n) := rfl

theorem tsum_term_diag : ∑' x : Dg, term (x : ℕ × ℕ) = Real.pi ^ 4 / 90 := by
  rw [← diagEquiv.tsum_eq (fun x : Dg => term (x : ℕ × ℕ))]
  have heq : ∀ n : ℕ, term ((diagEquiv n : Dg) : ℕ × ℕ) = 1 / (n : ℝ) ^ 4 := by
    intro n
    rw [diagEquiv_coe]
    unfold term
    ring
  simp_rw [heq]
  exact hasSum_zeta_four.tsum_eq

theorem summable_term_subtype (s : Set (ℕ × ℕ)) :
    Summable (term ∘ ((↑) : s → ℕ × ℕ)) :=
  summable_term.subtype s

/-- Transport a `term`-tsum across a proven (not merely definitional) equality of index
    sets, via `Equiv.setCongr` — avoids rewriting a `Set` equality inside a binder's type,
    which plain `rw` cannot do. -/
theorem tsum_term_setCongr {s t : Set (ℕ × ℕ)} (h : s = t) :
    ∑' x : s, term (x : ℕ × ℕ) = ∑' x : t, term (x : ℕ × ℕ) := by
  simpa using (Equiv.setCongr h).tsum_eq (fun x : t => term (x : ℕ × ℕ))

theorem tsum_term_offdiag :
    ∑' x : (Dgᶜ : Set (ℕ × ℕ)), term (x : ℕ × ℕ) = (Real.pi ^ 2 / 6) ^ 2 - Real.pi ^ 4 / 90 := by
  have h := summable_term.tsum_subtype_add_tsum_subtype_compl Dg
  rw [tsum_term_diag, tsum_term_eq] at h
  linarith

theorem Dgc_eq_union : (Dg : Set (ℕ × ℕ))ᶜ = Lt ∪ Gt := by
  ext p
  simp only [Dg, Lt, Gt, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union]
  omega

theorem disjoint_Lt_Gt : Disjoint Lt Gt := by
  rw [Set.disjoint_left]
  intro p hp hp'
  simp only [Lt, Gt, Set.mem_setOf_eq] at hp hp'
  omega

theorem tsum_term_offdiag_split :
    ∑' x : (Dgᶜ : Set (ℕ × ℕ)), term (x : ℕ × ℕ)
      = (∑' x : Lt, term (x : ℕ × ℕ)) + ∑' x : Gt, term (x : ℕ × ℕ) := by
  rw [tsum_term_setCongr Dgc_eq_union]
  exact Summable.tsum_union_disjoint disjoint_Lt_Gt
    (summable_term_subtype Lt) (summable_term_subtype Gt)

/-- The swap `Equiv` witnessing the reflection symmetry `Lt ≃ Gt`. -/
def swapEquiv : Lt ≃ Gt where
  toFun p := ⟨p.1.swap, show p.1.swap.2 < p.1.swap.1 from p.2⟩
  invFun p := ⟨p.1.swap, show p.1.swap.1 < p.1.swap.2 from p.2⟩
  left_inv p := Subtype.ext (Prod.swap_swap p.1)
  right_inv p := Subtype.ext (Prod.swap_swap p.1)

theorem tsum_term_Lt_eq_Gt :
    ∑' x : Lt, term (x : ℕ × ℕ) = ∑' x : Gt, term (x : ℕ × ℕ) := by
  rw [← swapEquiv.tsum_eq (fun x : Gt => term (x : ℕ × ℕ))]
  apply tsum_congr
  intro p
  show term (p : ℕ × ℕ) = term (p.1.swap)
  rw [term_swap]

/-- **The first Euler sum**: `Σ_{m<n} 1/(m²n²) = π⁴/120 = (3/4)ζ(4)`. -/
theorem euler_sum_one : ∑' x : Lt, term (x : ℕ × ℕ) = Real.pi ^ 4 / 120 := by
  have h1 := tsum_term_offdiag
  rw [tsum_term_offdiag_split, tsum_term_Lt_eq_Gt] at h1
  have hconst : (Real.pi ^ 2 / 6) ^ 2 - Real.pi ^ 4 / 90 = 2 * (Real.pi ^ 4 / 120) := by ring
  rw [hconst] at h1
  rw [tsum_term_Lt_eq_Gt]
  linarith

/-- The lower-triangle-including-diagonal `m ≤ n`. -/
def Le : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

theorem Le_eq_union : (Le : Set (ℕ × ℕ)) = Lt ∪ Dg := by
  ext p
  simp only [Le, Lt, Dg, Set.mem_setOf_eq, Set.mem_union]
  omega

theorem disjoint_Lt_Dg : Disjoint Lt Dg := by
  rw [Set.disjoint_left]
  intro p hp hp'
  simp only [Lt, Dg, Set.mem_setOf_eq] at hp hp'
  omega

theorem tsum_term_Le :
    ∑' x : Le, term (x : ℕ × ℕ) = Real.pi ^ 4 / 120 + Real.pi ^ 4 / 90 := by
  rw [tsum_term_setCongr Le_eq_union,
    Summable.tsum_union_disjoint disjoint_Lt_Dg (summable_term_subtype Lt)
      (summable_term_subtype Dg),
    euler_sum_one, tsum_term_diag]

/-- **The symmetric double-sum decomposition** (`docs/FORMALIZATION_PLAN.md` Thread E,
    "pure ℕ×ℕ tsum bookkeeping"): `2·Σ_{m≤n} 1/(m²n²) = ζ(2)² + ζ(4)`. -/
theorem two_mul_tsum_term_Le :
    2 * ∑' x : Le, term (x : ℕ × ℕ) = (Real.pi ^ 2 / 6) ^ 2 + Real.pi ^ 4 / 90 := by
  rw [tsum_term_Le]
  ring

/-- **`M₂ = ζ(4)/π⁴ = 1/90`**, directly from Mathlib's closed form for `ζ(4)`. This is the
    physics paper's target constant; the two-Euler-sum route above is a cross-check that
    reproduces `2ζ(4)`, not an independent derivation of this value. -/
theorem M2_eq : (Real.pi ^ 4 / 90) / Real.pi ^ 4 = 1 / 90 := by
  have hpi4 : Real.pi ^ 4 ≠ 0 := by positivity
  field_simp [hpi4]

/-- **Euler's second sum, `Σₙ Hₙ/n³ = (5/4)ζ(4) = π⁴/72`, is NOT formalized.**

    In the notation above it equals `Σ_{m≤n} (1/m)·(1/n³)`, i.e. `ζ(3,1) + ζ(4)` in
    multiple-zeta-value language, where `ζ(3,1) := Σ_{m<n} 1/(m·n³) = π⁴/360` is a classical
    Euler identity. Unlike `euler_sum_one`, the summand `(1/m)·(1/n³)` is **not symmetric**
    under swapping `m,n`, so the reflection-`Equiv` argument used above does not apply; the
    actual proof (partial-fraction reindexing of the double sum, or the classical
    generating-function/shuffle-relation argument for `ζ(3,1)`) needs genuinely different
    machinery that Mathlib does not currently provide (no
    `Mathlib.NumberTheory.MultipleZetaValues`). Named honestly rather than faked. -/
theorem open_euler_sum_two_gap : True := trivial

end GppEulerSum
