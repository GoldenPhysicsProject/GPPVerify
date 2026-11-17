import GppVerify.RiemannHypothesis.WeakCouplingFalsifier

/-!
# Positivity on a finite-codimension subspace bounds the negative index

The abstract core of GPP's all-width finite-negative-index theorem (Turbo relay `458ba0f`, §4 and request
(2)): if a function `q` is strictly positive on the nonzero vectors of the common kernel of `n` linear
functionals, then no subspace on which `q ≤ 0` has dimension greater than `n`.

* `finrank_le_of_pos_on_ker`: for functionals `φ₁ … φₙ` and `q` with `q f > 0` whenever all `φᵢ f = 0` and
  `f ≠ 0`, every subspace `U` with `q ≤ 0` on `U` is finite-dimensional with `finrank U ≤ n`.
* `momentFunctional`: the moment functionals `f ↦ ∫ xᵏ f(x) dx` as linear maps on the window space `V_L`,
  so the lemma applies with `φ_k` the first `n` moments.
* `negIndex_le_of_pos_on_vanishing_moments`: if the Weil-type quadratic form is positive on window test
  functions with vanishing moments `0 … n−1`, the negative index on `V_L` is at most `n`.

**Scope.** Pure linear algebra plus linearity of the moment integrals. The analytic inputs of the all-width
theorem — the low-band Fourier bound for functions with vanishing moments, the Plancherel identity for the
archimedean energy, the monotone divergence of the multiplier — are *not* here, so this proves no
positivity statement for the actual Weil form. ARP/OB-6/RH are untouched.

No `sorry`, no axiom.
-/

open MeasureTheory
open GppShiftPresentation

noncomputable section

namespace GppFiniteIndex

/-- **Finite-codimension positivity ⇒ finite index.** -/
theorem finrank_le_of_pos_on_ker {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (φ : Fin n → V →ₗ[ℝ] ℝ) (q : V → ℝ)
    (hq : ∀ f : V, (∀ i, φ i f = 0) → f ≠ 0 → 0 < q f)
    (U : Submodule ℝ V) (hU : ∀ u ∈ U, q u ≤ 0) :
    Module.finrank ℝ U ≤ n := by
  let Φ : U →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun i => (φ i).comp U.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    by_contra hne
    have hu0 : (u : V) ≠ 0 := fun h => hne (Subtype.ext h)
    have hall : ∀ i, φ i (u : V) = 0 := fun i => by
      have := congrFun hu i
      simpa [Φ] using this
    have hpos := hq (u : V) hall hu0
    have hle := hU (u : V) u.2
    linarith
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- Such a subspace `U` is automatically finite-dimensional, so the `finrank` bound is not vacuous. -/
theorem finiteDimensional_of_pos_on_ker {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (φ : Fin n → V →ₗ[ℝ] ℝ) (q : V → ℝ)
    (hq : ∀ f : V, (∀ i, φ i f = 0) → f ≠ 0 → 0 < q f)
    (U : Submodule ℝ V) (hU : ∀ u ∈ U, q u ≤ 0) :
    FiniteDimensional ℝ U := by
  let Φ : U →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun i => (φ i).comp U.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    by_contra hne
    have hu0 : (u : V) ≠ 0 := fun h => hne (Subtype.ext h)
    have hall : ∀ i, φ i (u : V) = 0 := fun i => by
      have := congrFun hu i
      simpa [Φ] using this
    have hpos := hq (u : V) hall hu0
    have hle := hU (u : V) u.2
    linarith
  exact Module.Finite.of_injective Φ hinj

/-! ### The moment functionals on the window space -/

/-- `x ↦ xᵏ f(x)` is integrable for a window test function. -/
theorem integrable_moment {L : ℝ} (f : windowSubmodule L) (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * f.1 x :=
  ((continuous_pow k).mul f.2.1.1.continuous).integrable_of_hasCompactSupport
    f.2.1.2.mul_left

/-- **The `k`-th moment functional** `f ↦ ∫ xᵏ f(x) dx` on the window space `V_L`. -/
def momentFunctional (L : ℝ) (k : ℕ) : windowSubmodule L →ₗ[ℝ] ℝ where
  toFun f := ∫ x, x ^ k * f.1 x
  map_add' f g := by
    have h := integral_add (integrable_moment f k) (integrable_moment g k)
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact h
  map_smul' c f := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : (fun x : ℝ => x ^ k * (c * f.1 x)) = fun x => c * (x ^ k * f.1 x) := by
      funext x; ring
    rw [this, integral_const_mul]

/-- **Window finite-index bound.** If a function `q` on window test functions is strictly positive on
the nonzero ones with vanishing moments `0 … n−1`, every subspace on which `q ≤ 0` is finite-dimensional
of dimension at most `n`. (Apply with `q` the Weil quadratic form to get the negative-index bound.) -/
theorem index_le_of_pos_on_vanishing_moments (L : ℝ) (n : ℕ) (q : windowSubmodule L → ℝ)
    (hq : ∀ f : windowSubmodule L, (∀ i : Fin n, momentFunctional L i f = 0) → f ≠ 0 → 0 < q f)
    (U : Submodule ℝ (windowSubmodule L)) (hU : ∀ u ∈ U, q u ≤ 0) :
    FiniteDimensional ℝ U ∧ Module.finrank ℝ U ≤ n :=
  ⟨finiteDimensional_of_pos_on_ker (fun i : Fin n => momentFunctional L i) q hq U hU,
    finrank_le_of_pos_on_ker (fun i : Fin n => momentFunctional L i) q hq U hU⟩

end GppFiniteIndex

#print axioms GppFiniteIndex.finrank_le_of_pos_on_ker
#print axioms GppFiniteIndex.finiteDimensional_of_pos_on_ker
#print axioms GppFiniteIndex.index_le_of_pos_on_vanishing_moments
