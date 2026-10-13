import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite-volume lattice Peter–Weyl gap (SU(2) electric sector)

The Yang–Mills twin of `GppVerify/RiemannHypothesis/ConductorGap.lean`
(Codex, PR #307): there, Peter–Weyl on the compact idèle-class kernel `K`
quantizes the dual into Dirichlet characters and the model Hamiltonian
`H χ = log (cond χ)` has gap `log 3`. Here the compact group is `SU(2)`,
Peter–Weyl labels a single link by its spin `j`, and the Kogut–Susskind
electric term is diagonal with eigenvalue the quadratic Casimir `j(j+1)`.

Results:
* `variational_gap` — abstract finite-label gap: a nonnegative label energy
  vanishing only at the vacuum, and bounded below off the vacuum, gives a
  Rayleigh-quotient gap on the vacuum-orthogonal subspace.
* `casimir_gap` — every nonzero SU(2) spin has `j(j+1) ≥ 3/4`.
* `finite_volume_gap` — on a finite lattice (any finite link set `E`, any
  spin truncation `J`), the total electric energy of any state with no
  vacuum component is `≥ (3/4) · ‖f‖²`. The gap is **independent of the
  volume** — at finite volume the compactness doing the work is the gauge
  group's, not the lattice's.

**Scope, honestly.** Finite volume and finite spin truncation; electric
sector only (no magnetic/plaquette term); the continuum and
infinite-volume limits are NOT addressed. This is the finite Peter–Weyl
discreteness that the mass-gap problem asks to *survive* a limit — the
limit itself remains open. **No Yang–Mills mass-gap claim.**

Epistemic label: **LEAN-CHECKED** (kernel, zero `sorry`, standard axioms only).
-/

namespace FiniteLatticeGap

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Variational spectral gap for a finite Peter–Weyl label space.**
If `Δ ≤ c i` for every non-vacuum label `i ≠ v`, then every state `f` with
no vacuum component satisfies `Δ * ‖f‖² ≤ ∑ i, c i * ‖f i‖²`. (No condition
on `c` at or off the vacuum is needed beyond the bound: the vacuum term is
killed by `f v = 0` itself.) -/
theorem variational_gap {c : ι → ℝ} {v : ι} {Δ : ℝ}
    (hΔ : ∀ i ≠ v, Δ ≤ c i)
    (f : ι → ℂ) (hf : f v = 0) :
    Δ * (∑ i, ‖f i‖ ^ 2) ≤ ∑ i, c i * ‖f i‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_ne i v with rfl | hi
  · simp [hf]
  · exact mul_le_mul_of_nonneg_right (hΔ i hi) (pow_nonneg (norm_nonneg _) 2)

/-- SU(2) quadratic Casimir at spin `j = i / 2`: `c(i) = (i/2) (i/2 + 1)`. -/
noncomputable def casimir (i : ℕ) : ℝ :=
  (i : ℝ) / 2 * ((i : ℝ) / 2 + 1)

theorem casimir_nonneg (i : ℕ) : 0 ≤ casimir i := by
  unfold casimir
  positivity

theorem casimir_pos {i : ℕ} (hi : i ≠ 0) : 0 < casimir i := by
  have h1 : (0 : ℝ) < (i : ℝ) / 2 := by
    have hpos : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
    linarith
  unfold casimir
  exact mul_pos h1 (by linarith)

theorem casimir_eq_zero {i : ℕ} : casimir i = 0 ↔ i = 0 := by
  constructor
  · intro h
    by_contra hi
    have := casimir_pos hi
    linarith
  · intro h
    rw [h]
    simp [casimir]

/-- **Single-link gap.** Every nonzero spin has Casimir at least `3/4`,
attained at `j = 1/2`. -/
theorem casimir_gap {i : ℕ} (hi : i ≠ 0) : 3 / 4 ≤ casimir i := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
  unfold casimir
  nlinarith [sq_nonneg ((i : ℝ) / 2 - 1 / 2)]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Spin label per link, truncated at `J`: `Fin (2J + 1)` represents
`j = i / 2` for `i ≤ 2J`. -/
abbrev Spin (J : ℕ) := Fin (2 * J + 1)

/-- Total electric energy of a link configuration: the sum of Casimirs. -/
noncomputable def linkEnergy {J : ℕ} (g : E → Spin J) : ℝ :=
  ∑ e, casimir (g e).val

theorem linkEnergy_nonneg {J : ℕ} (g : E → Spin J) : 0 ≤ linkEnergy g :=
  Finset.sum_nonneg fun e _ => casimir_nonneg (g e).val

/-- **Finite-volume gap, configuration form.** Any non-vacuum configuration
has total electric energy at least `3 / 4` — one excited link already pays
the full single-link gap, and every other link contributes nonnegatively. -/
theorem linkEnergy_gap {J : ℕ} {g : E → Spin J} (hg : g ≠ 0) :
    3 / 4 ≤ linkEnergy g := by
  obtain ⟨e, he⟩ : ∃ e, g e ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (funext h)
  have hval : (g e).val ≠ 0 := fun hv => he (Fin.ext hv)
  unfold linkEnergy
  exact le_trans (casimir_gap hval)
    (Finset.single_le_sum (f := fun e => casimir (g e).val)
      (fun e _ => casimir_nonneg _) (Finset.mem_univ e))

/-- The vacuum is the unique zero-energy configuration. -/
theorem linkEnergy_eq_zero {J : ℕ} {g : E → Spin J} :
    linkEnergy g = 0 ↔ g = 0 := by
  constructor
  · intro h
    by_contra hg
    have := linkEnergy_gap hg
    linarith
  · intro h
    rw [h]
    simp [linkEnergy, casimir]

/-- **Finite-volume lattice Peter–Weyl gap (SU(2) electric sector).**
For any finite link set `E` and any spin truncation `J`, every state `f`
on the configuration space with no vacuum component satisfies the Rayleigh
bound with gap `3 / 4`, the single-link Casimir gap — independent of the
number of links. -/
theorem finite_volume_gap {J : ℕ} (f : (E → Spin J) → ℂ) (hf : f 0 = 0) :
    (3 / 4 : ℝ) * (∑ g, ‖f g‖ ^ 2) ≤ ∑ g, linkEnergy g * ‖f g‖ ^ 2 :=
  variational_gap (fun _ hg => linkEnergy_gap hg) f hf

end FiniteLatticeGap
