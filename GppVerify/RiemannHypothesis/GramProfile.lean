import GppVerify.RiemannHypothesis.AkgStatement
import GppVerify.RiemannHypothesis.WeilHRho

/-!
# Gram-profile definitions: the frame-independent half of UB

Turbo's funded-trajectory entry (bridge `9eaf136`) names **UB** as the open conjecture: at every width
`L ≥ 1/2`, in the width-`L` semilocal frame `𝔽_L`, (UB-A) the archimedean diagonal profile bound and
(UB-R) every normalised off-diagonal row sum `≤ ρ* < 1`, with `c_A*`, `ρ*` independent of `L`.

**This file states only what does not depend on `𝔽_L`.** For a finite family `φ` of test functions it
defines the Weil–Gram matrix `G_jk = B(φ_j, φ_k)` (`B` the bilinear form of `linearZeta`, whose diagonal
is `weilForm (autocorr ·)` — `gram_zeta_eq`), its normalisation `Ã`, and the two clauses as propositions
about *a given family*: `UBR φ ρ`, `UBA φ ω c`. **The frame `𝔽_L` itself — which family, and the Schur
elimination of the `Y` block and the border — is *not* defined here (it is owed, build-order step (ii)), and
no proposition in this file says anything about which family it is.** A statement of UB in this file's
terms is therefore a *schema*, not UB.

**Witnesses are not attributed here.** The `L = 0.5` witnesses (`c_A = 867483/500000`,
`ρ = 3632727590/2³²`, `WeilHAFiniteRange` / `WeilHRho`) are witnesses for the **`St` / `S_Z^eff` frame** —
the bordered Gram of the odd-face Σ-kernel `G(s,u) = ½[K_S(s−u) − K_S(s+u)]` after δ-elimination and the `Y`
Schur complement — modulo the named ball hypotheses recorded in those files. `St` is **not** literally the
matrix `B(φ_j, φ_k)` defined here, and no in-tree lemma identifies the two presentations; that identification
is an open obligation, on the same footing as the definition of `𝔽_L`. Nothing in this file says that
`UBR`/`UBA` for the `B`-Gram hold with those constants.

The one theorem is the elementary normalised-frame consequence: `UBR φ ρ` with positive diagonal gives
`(1 − ρ)‖x‖² ≤ xᵀ Ã x ≤ (1 + ρ)‖x‖²` (`gershgorin_normGram`), by the row-sum lemma of `WeilHRho`.
This is the Gershgorin statement in *normalised* coordinates only; it is **not** a margin in original
coordinates (where the profile decays like `log ω/ω⁴`), and nothing here derives `UB ⇒ μ(L) ≥ m* > 0`.

ARP, RH, OB-6, UB: OPEN. No `sorry`, no axiom.
-/

open scoped InnerProductSpace
open GppShadowTheory GppWeilCriterion GppKernelTheory

noncomputable section

namespace GppGramProfile

/-- The Weil–Gram matrix of a finite family of test functions: `G_jk = B(φ_j, φ_k)`, with
`B g f = Re corr(Θ g, f)` (`linearZeta.B`); `G_jj = weilForm (autocorr φ_j)` by `gram_zeta_eq`. -/
def gramMat {n : ℕ} (φ : Fin n → ZetaTest) (j k : Fin n) : ℝ := linearZeta.B (φ j) (φ k)

/-- The normalised Gram matrix `Ã_jk = G_jk / √(G_jj G_kk)`. -/
def normGram {n : ℕ} (φ : Fin n → ZetaTest) (j k : Fin n) : ℝ :=
  gramMat φ j k / (Real.sqrt (gramMat φ j j) * Real.sqrt (gramMat φ k k))

/-- **(UB-R), for a given family**: every normalised off-diagonal row sum is `≤ ρ`. -/
def UBR {n : ℕ} (φ : Fin n → ZetaTest) (ρ : ℝ) : Prop :=
  ∀ j : Fin n, ∑ k ∈ Finset.univ.erase j, |normGram φ j k| ≤ ρ

/-- **(UB-A), for a given family**: the diagonal profile bound `G_jj ≥ c · log ω_j / ω_j⁴`
(the profile of `ω`, e.g. `ω_j = 4πj` at `L = 0.5`, is an argument, not fixed here). -/
def UBA {n : ℕ} (φ : Fin n → ZetaTest) (ω : Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ j : Fin n, c * Real.log (ω j) / (ω j) ^ 4 ≤ gramMat φ j j

theorem gramMat_symm {n : ℕ} (φ : Fin n → ZetaTest) (j k : Fin n) :
    gramMat φ j k = gramMat φ k j := by
  show (linearZeta.corr (linearZeta.Θ (φ j)) (φ k)).re =
    (linearZeta.corr (linearZeta.Θ (φ k)) (φ j)).re
  exact congrArg Complex.re (linearZeta.corr_Θ_symm (φ j) (φ k))

/-- **Gershgorin, in normalised coordinates.** If the normalised off-diagonal row sums are `≤ ρ` and
every diagonal entry is positive, then `(1 − ρ)‖x‖² ≤ xᵀ Ã x ≤ (1 + ρ)‖x‖²`. -/
theorem gershgorin_normGram {n : ℕ} (φ : Fin n → ZetaTest) (ρ : ℝ) (hρ : UBR φ ρ)
    (hdiag : ∀ j, 0 < gramMat φ j j) (x : Fin n → ℝ) :
    (1 - ρ) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, normGram φ i j * x i * x j ∧
      ∑ i, ∑ j, normGram φ i j * x i * x j ≤ (1 + ρ) * ∑ i, x i ^ 2 := by
  set C : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0 with hC
  set R : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else |normGram φ i j| with hR
  have hsymm : ∀ i j, normGram φ i j = normGram φ j i := by
    intro i j
    unfold normGram
    rw [gramMat_symm φ i j, mul_comm]
  have hRsymm : ∀ i j, R i j = R j i := by
    intro i j
    simp only [hR]
    by_cases hij : i = j
    · subst hij; rfl
    · have : ¬ (j = i) := fun h => hij h.symm
      simp [hij, this, hsymm i j]
  have hb : ∀ i j, |normGram φ i j - C i j| ≤ R i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 : normGram φ i i = 1 := by
        unfold normGram
        have := hdiag i
        rw [← sq, Real.sq_sqrt this.le]
        exact div_self this.ne'
      simp [hC, hR, h1]
    · simp [hC, hR, hij]
  have hrow : ∀ i, ∑ j, R i j ≤ ρ := by
    intro i
    have : ∑ j, R i j = ∑ k ∈ Finset.univ.erase i, |normGram φ i k| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [hR, if_true, add_zero]
      exact Finset.sum_congr rfl fun k hk => by
        rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    rw [this]; exact hρ i
  have hsum : ∑ i, (∑ j, R i j) * x i ^ 2 ≤ ρ * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hCsum : ∑ i, ∑ j, C i j * x i * x j = ∑ i, x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hC, sq]
  have h1 := GppWeilHRho.quad_ge_of_ball (normGram φ) C R hRsymm hb x
  have h2 := GppWeilHRho.quad_le_of_ball (normGram φ) C R hRsymm hb x
  rw [hCsum] at h1 h2
  constructor <;> nlinarith [hsum]

end GppGramProfile

#print axioms GppGramProfile.gershgorin_normGram
