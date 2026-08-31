import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Thread S, Step 1 — the abstract Hermitian inertia core

Finite-dimensional, analysis-free, zero-free (no Riemann zeta zeros anywhere in this
file), completely `sorry`-free. See `GppVerify/ThreadS/SOURCES.md` for what this
formalizes and why, and `GppVerify/ThreadS/MATHLIB_RECON.md` for what was already
available at GPPVerify's pin (`c44e0c8`, Mathlib v4.19.0) versus what had to be built
locally.

This file does NOT reproduce, cite, or depend on Anthropic's `zeta-23-lean` repository
(different, newer Mathlib pin — `v4.33.0-rc2` / `51e6992e`). It is an independent
GPPVerify-native development, built against this repo's own pinned Mathlib source, whose
purpose is to give GPPVerify its own audited inertia core that can be bridged (a later
Thread S file) to `WeilPositivityCriterion.lean` and `CauchyKernelPositive.lean`.

## What is proved here

* `nPos`, `nNeg`, `nZero` — the positive/negative/zero eigenvalue counts of a Hermitian
  matrix, via `Matrix.IsHermitian.eigenvalues : n → ℝ` (chosen over `eigenvalues₀` because
  it is already indexed by the matrix's own index type `n`, per `MATHLIB_RECON.md`).
* `inertia_sum` — `nPos + nNeg + nZero = Fintype.card n`, by trichotomy partition of
  `Finset.univ`.

## What is NOT in this file

The subspace-dimension bounds (`dim_le_nPos_of_posDef_on` / `dim_le_nNeg_of_negDef_on`),
congruence invariance (`inertia_congruent`), and the rank–trace inequality (the paper's
Lemma 3.2, the actual load-bearing lemma of Thread S) are separate, larger developments
and are NOT claimed complete by this file. This file is the base layer only.
-/

namespace GppThreadS

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def nPos : ℕ := (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card

/-- The number of strictly negative eigenvalues of a Hermitian matrix. -/
noncomputable def nNeg : ℕ := (Finset.univ.filter (fun i => hQ.eigenvalues i < 0)).card

/-- The number of zero eigenvalues of a Hermitian matrix (the nullity). -/
noncomputable def nZero : ℕ := (Finset.univ.filter (fun i => hQ.eigenvalues i = 0)).card

/-- **Inertia identity.** The positive, negative, and zero eigenvalue counts sum to the
ambient dimension. This is the arithmetic core of the whole inertia mechanism: any
independently obtained bound on one component constrains the others once the total is
fixed.

Proved by two applications of `Finset.card_filter_add_card_filter_not`: first split
`univ` into `{eigenvalues i ≥ 0}` and its negation `{eigenvalues i < 0}` (giving `nNeg`
directly), then split `{eigenvalues i ≥ 0}` into `{eigenvalues i = 0}` and its negation
`{eigenvalues i ≠ 0} = {eigenvalues i > 0}` on that subset (giving `nZero` and `nPos`). -/
theorem inertia_sum : nPos hQ + nNeg hQ + nZero hQ = Fintype.card n := by
  classical
  have hstep1 : (Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).card +
      (Finset.univ.filter (fun i => ¬ 0 ≤ hQ.eigenvalues i)).card = Fintype.card n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hneg_eq : (Finset.univ.filter (fun i => ¬ 0 ≤ hQ.eigenvalues i)) =
      (Finset.univ.filter (fun i => hQ.eigenvalues i < 0)) := by
    apply Finset.filter_congr; intro i _; exact not_le
  have hstep2 :
      ((Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).filter
        (fun i => hQ.eigenvalues i = 0)).card +
      ((Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).filter
        (fun i => ¬ hQ.eigenvalues i = 0)).card
      = (Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hzero_eq : (Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).filter
        (fun i => hQ.eigenvalues i = 0) = Finset.univ.filter (fun i => hQ.eigenvalues i = 0) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro i _
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨h.ge, h⟩
  have hpos_eq : (Finset.univ.filter (fun i => 0 ≤ hQ.eigenvalues i)).filter
        (fun i => ¬ hQ.eigenvalues i = 0) = Finset.univ.filter (fun i => 0 < hQ.eigenvalues i) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr; intro i _
    constructor
    · rintro ⟨hge, hne⟩; exact hge.lt_of_ne (Ne.symm hne)
    · intro h; exact ⟨h.le, h.ne'⟩
  show nPos hQ + nNeg hQ + nZero hQ = Fintype.card n
  unfold nPos nNeg nZero
  rw [hzero_eq, hpos_eq] at hstep2
  rw [hneg_eq] at hstep1
  omega

end GppThreadS
