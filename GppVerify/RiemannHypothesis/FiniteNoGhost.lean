import GppVerify.RiemannHypothesis.TruncatedTransport
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The finite no-ghost theorem for the S-truncated arithmetic state space

Goddard-Thorn, translated. In the bosonic string the no-ghost theorem says the physical
subspace of an indefinite-metric Fock space is positive semi-definite, and that after
quotienting the null directions it is positive *definite*. The arithmetic analogue
replaces the oscillator metric by the Weil/Gram form carried by a positive-type kernel.

At the level of a finite set `S` of primes this is unconditional, because
`GppTransport.truncated_transport` puts a genuine positive-type datum on the truncated
chart `R x Z^S` with no adeles.

**Honest boundary.** Nothing here is uniform in `S`. By
`GppWeilCriterion.rh_iff_weil_pairedForm_nonneg` the uniform statement is equivalent to
RH and stays open.
-/

namespace GppNoGhost

open Finset GppTransport RCLike
open scoped ComplexOrder

variable {G : Type*} [AddCommGroup G]

/-- The level-`S` Weil pairing: `<c, d> = Σ conj(c i) d j P(x i - x j)`. -/
noncomputable def weilPairing (P : G → ℝ) {n : ℕ} (x : Fin n → G) (c d : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ (c i)) * d j * (P (x i - x j) : ℂ)

/-- The norm form `q(c) = <c, c>`. -/
noncomputable def weilForm (P : G → ℝ) {n : ℕ} (x : Fin n → G) (c : Fin n → ℂ) : ℂ :=
  weilPairing P x c c

theorem weilForm_nonneg {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ}
    (x : Fin n → G) (c : Fin n → ℂ) : 0 ≤ weilForm P x c := hP n x c

/-- A *ghost*: a state of strictly negative norm. -/
def Ghost (P : G → ℝ) {n : ℕ} (x : Fin n → G) (c : Fin n → ℂ) : Prop :=
  weilForm P x c < 0

/-- **The finite no-ghost theorem.** A positive-type kernel admits no ghosts. -/
theorem no_ghost {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ}
    (x : Fin n → G) (c : Fin n → ℂ) : ¬ Ghost P x c := fun h =>
  absurd (lt_of_le_of_lt (weilForm_nonneg hP x c) h) (lt_irrefl 0)

/-- **A positive-type kernel is even.** Forced by hermiticity of the 2x2 Gram block:
    the `c = ![1, I]` test vector has imaginary part `P y - P (-y)`, and a nonnegative
    complex number is real. -/
theorem positiveTypeOn_even {P : G → ℝ} (hP : PositiveTypeOn P) (y : G) :
    P (-y) = P y := by
  have h := hP 2 ![0, -y] ![1, Complex.I]
  have him := (Complex.le_def.mp h).2
  simp [Fin.sum_univ_two, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re] at him
  linarith

theorem weilPairing_add_left {P : G → ℝ} {n : ℕ} (x : Fin n → G) (c d e : Fin n → ℂ) :
    weilPairing P x (c + d) e = weilPairing P x c e + weilPairing P x d e := by
  simp only [weilPairing, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem weilPairing_smul_left {P : G → ℝ} {n : ℕ} (x : Fin n → G) (r : ℂ)
    (c d : Fin n → ℂ) :
    weilPairing P x (r • c) d = (starRingEnd ℂ r) * weilPairing P x c d := by
  simp only [weilPairing, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Hermitian symmetry, from evenness of `P`. -/
theorem weilPairing_conj_symm {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ}
    (x : Fin n → G) (c d : Fin n → ℂ) :
    (starRingEnd ℂ) (weilPairing P x d c) = weilPairing P x c d := by
  simp only [weilPairing, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : P (x j - x i) = P (x i - x j) := by
    have := positiveTypeOn_even hP (x i - x j); simpa [neg_sub] using this
  rw [this]; ring

/-- **The pre-inner-product structure carried by any positive-type kernel.** This is the
    step that makes Goddard-Thorn's argument available: Mathlib's Cauchy-Schwarz for a
    merely semi-definite form follows, and with it the fact that the null cone is a
    subspace. -/
noncomputable def core {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ} (x : Fin n → G) :
    PreInnerProductSpace.Core ℂ (Fin n → ℂ) where
  inner c d := weilPairing P x c d
  conj_inner_symm c d := weilPairing_conj_symm hP x c d
  re_inner_nonneg c := by
    have h := weilForm_nonneg hP x c
    simpa [weilForm] using (Complex.le_def.mp h).1
  add_left := weilPairing_add_left x
  smul_left c d r := weilPairing_smul_left x r c d

/-- **Cauchy-Schwarz at level `S`**, inherited from Mathlib via `core`. -/
theorem weilPairing_norm_mul_le {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ}
    (x : Fin n → G) (c d : Fin n → ℂ) :
    ‖weilPairing P x c d‖ * ‖weilPairing P x d c‖
      ≤ (weilForm P x c).re * (weilForm P x d).re := by
  let _i : PreInnerProductSpace.Core ℂ (Fin n → ℂ) := core hP x
  exact InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) c d

/-- **Null states decouple.** A state of zero norm is orthogonal to every state. This is
    the Goddard-Thorn decoupling step: it is what makes the null cone a subspace, so that
    the quotient carries a *definite* form rather than a merely semi-definite one. -/
theorem weilPairing_eq_zero_of_null {P : G → ℝ} (hP : PositiveTypeOn P) {n : ℕ}
    (x : Fin n → G) {c : Fin n → ℂ} (hc : weilForm P x c = 0) (d : Fin n → ℂ) :
    weilPairing P x c d = 0 := by
  have hsym : ‖weilPairing P x d c‖ = ‖weilPairing P x c d‖ := by
    rw [← weilPairing_conj_symm hP x c d, RCLike.norm_conj]
  have h := weilPairing_norm_mul_le hP x c d
  rw [hc, hsym] at h
  simp only [Complex.zero_re, zero_mul] at h
  have h2 : ‖weilPairing P x c d‖ * ‖weilPairing P x c d‖ ≤ 0 := h
  have : ‖weilPairing P x c d‖ = 0 := by nlinarith [norm_nonneg (weilPairing P x c d)]
  simpa using this

/-- **No ghosts on the S-truncated prime chart.** Specialisation of `no_ghost` along
    `truncated_transport` with weights `w_p = log p`: the level-`S` arithmetic state
    space carries no negative-norm states, unconditionally, with no adeles. -/
theorem no_ghost_prime_chart {S : Finset ℕ} {P : ℝ → ℝ}
    (hP : GppHaarPositivityWeil.PositiveType P) {n : ℕ}
    (x : Fin n → (ℝ × (S → ℤ))) (c : Fin n → ℂ) :
    ¬ Ghost (fun z : ℝ × (S → ℤ) =>
        P (z.1 + ∑ p : S, (z.2 p : ℝ) * Real.log ((p : ℕ) : ℝ))) x c :=
  no_ghost (truncated_transport (fun p : S => Real.log ((p : ℕ) : ℝ)) hP) x c

end GppNoGhost
