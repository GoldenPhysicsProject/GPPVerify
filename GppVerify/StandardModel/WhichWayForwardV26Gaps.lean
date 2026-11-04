import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# *Which Way Is Forward?* v26: finite statements not previously in Lean

Daniel Toupin, *Which Way Is Forward?* (v26), with AI assistance from Claude Code. An audit of the
paper's theorems against GPPVerify found most finite statements already formalized (four-lift
group and centre, real form, Clifford intertwiner, CAR pair production, orientation-covariant
second law, Grassmannian order four, Spin^c quotient, X = 3(B−L), Spin(10,2) reality, parity
exchange, Compton/zitter clock). This file adds the remaining finite ones:

* `equal_lift_weight`, `equal_lift_weight_half` (Prop. "Equal lift weight under an invariant
  state"): a probability weight on the four lifts invariant under the diagonal reversal gives
  `μ(++) = μ(--)`, `μ(+-) = μ(-+)`, and probability `1/2` within each two-point orbit;
* `even_profile_deriv_odd`, `oriented_rate_eq_abs` (Cor. "Time-symmetric entropy profile"): an even
  entropy profile has odd derivative, and with `t = sgn λ` the oriented rate `t · S'(λ)` is
  `|S'(λ)|` whenever `S'` has the sign of `λ` (entropy minimum at `λ = 0`);
* `half_flip_not_deck` (Prop. "A half flip is not the spin-deck element", linear case): no
  invertible matrix `U` satisfies `U R_t = −U`, because `R_t` fixes a nonzero vector;
* `det_lorentz_chart`, `det_hermitian_slice` (Prop. "Lorentz loops have zero determinant winding",
  algebraic part): `det(L A Rᵀ) = det A` for `det L = det R = 1`, and `det(L A Lᴴ) = det A` for
  `det L = 1`; the winding conclusion then follows from constancy of `det` along the orbit;
* `so102_dimension_split`, `offdiag_branching_dimension` (Thm. "Decomposition of a single
  Spin(10,2) connection", Cor. bidoublet): `66 = 28 + 6 + 32` and `32 = 24 + 4 + 4`;
* `unit_character_inv_eq_conj` (Prop. "Universal character–orientation duality"): for a unitary
  one-dimensional character value `z`, path reversal `z ↦ z⁻¹` equals `z ↦ conj z`.

Scope: finite algebra, real calculus and dimension counts. The antilinear case of the deck
obstruction, the winding-number topology and the representation-theoretic branching itself are
not formalized here. Nothing here concerns RH.
-/

namespace GppWhichWayV26

/-! ## Equal lift weight -/

/-- The diagonal reversal on the four lifts `(q, t)`. -/
def diag (x : Bool × Bool) : Bool × Bool := (!x.1, !x.2)

theorem equal_lift_weight (μ : Bool × Bool → ℝ) (hμ : ∀ x, μ (diag x) = μ x) :
    μ (true, true) = μ (false, false) ∧ μ (true, false) = μ (false, true) := by
  refine ⟨?_, ?_⟩
  · simpa [diag] using hμ (false, false)
  · simpa [diag] using hμ (false, true)

theorem equal_lift_weight_half (μ : Bool × Bool → ℝ) (hμ : ∀ x, μ (diag x) = μ x)
    (hpos : 0 < μ (true, true) + μ (false, false)) :
    μ (true, true) / (μ (true, true) + μ (false, false)) = 1 / 2 := by
  have h := (equal_lift_weight μ hμ).1
  rw [h] at hpos ⊢
  have hne : μ (false, false) ≠ 0 := by linarith
  field_simp
  ring

/-! ## Time-symmetric entropy profile -/

theorem even_profile_deriv_odd {S S' : ℝ → ℝ} (hS : ∀ l, S (-l) = S l)
    (hd : ∀ l, HasDerivAt S (S' l) l) (l : ℝ) : S' (-l) = -S' l := by
  have h1 : HasDerivAt (fun r => S (-r)) (S' (-l) * -1) l :=
    (hd (-l)).comp l (hasDerivAt_neg l)
  have h2 : HasDerivAt (fun r => S (-r)) (S' l) l := by
    have : (fun r => S (-r)) = S := funext hS
    rw [this]; exact hd l
  have := h1.unique h2
  linarith

theorem oriented_rate_eq_abs (l s : ℝ) (hsign : (0 < l → 0 ≤ s) ∧ (l < 0 → s ≤ 0)) (hl : l ≠ 0) :
    SignType.sign l * s = |s| := by
  rcases lt_or_gt_of_ne hl with h | h
  · rw [sign_neg h]; simp [abs_of_nonpos (hsign.2 h)]
  · rw [sign_pos h]; simp [abs_of_nonneg (hsign.1 h)]

/-! ## A half flip is not the spin-deck element -/

/-- The temporal half flip `|q,t⟩ ↦ |q,−t⟩` on the basis `++, +−, −+, −−`. -/
def Rt : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem half_flip_not_deck : ¬ ∃ U : Matrix (Fin 4) (Fin 4) ℂ, IsUnit U ∧ U * Rt = -U := by
  rintro ⟨U, hU, h⟩
  have hR : Rt = -1 := by
    have := congrArg (fun M => U⁻¹ * M) h
    simp only [← Matrix.mul_assoc, Matrix.mul_neg] at this
    rwa [Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).mp hU), Matrix.one_mul] at this
  have := congrFun (congrFun hR 0) 0
  simp [Rt] at this

/-! ## Lorentz action preserves the determinant -/

theorem det_lorentz_chart (L A R : Matrix (Fin 2) (Fin 2) ℂ) (hL : L.det = 1) (hR : R.det = 1) :
    (L * A * R.transpose).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hL, hR, one_mul, mul_one]

theorem det_hermitian_slice (L A : Matrix (Fin 2) (Fin 2) ℂ) (hL : L.det = 1) :
    (L * A * L.conjTranspose).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hL, star_one, one_mul, mul_one]

/-! ## Spin(10,2) adjoint dimension counts -/

theorem so102_dimension_split :
    Nat.choose 12 2 = Nat.choose 8 2 + Nat.choose 4 2 + 8 * 4 := by decide

theorem offdiag_branching_dimension : 8 * 4 = 6 * 2 * 2 + 1 * 2 * 2 + 1 * 2 * 2 := by decide

/-! ## Character–orientation duality -/

theorem unit_character_inv_eq_conj (z : ℂ) (hz : ‖z‖ = 1) : z⁻¹ = (starRingEnd ℂ) z := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

end GppWhichWayV26
