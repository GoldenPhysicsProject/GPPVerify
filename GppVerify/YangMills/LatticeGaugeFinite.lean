import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped Matrix

/-!
# Finite lattice gauge theory: the finite stage of the lattice road

This module constructs, in finite terms only, the first stage of the lattice
road to quantum Yang–Mills on `R^4` (programme: "Constructing Quantum
Yang–Mills on R⁴ with a Mass Gap: Programme", YM-PROGRAMME.md, metaproblem
goal files, 2026-10-28). Everything here is finite: a finite incidence
geometry (finite `Sites`, finite `Links`), a finite gauge group `G`,
configurations `U : Links → G`, finite sums for the Gibbs state.

## What is proved

1. The gauge action of `Sites → G` on configurations, with its identity and
   composition laws.
2. Plaquette holonomy for closed walks, its conjugation law under gauge
   transformations, and gauge invariance of the Wilson action built from a
   class function.
3. The Gibbs state: partition function `Z > 0` for positive weights,
   Boltzmann weights, expectations, and the constant-expectation identity.
4. Reflection positivity in finite form: for a configuration space split as
   `B × P × P` (boundary / plus / minus link values) with the swap involution
   `θ`, any Gibbs weight that factorises as `W(b, p, q) = A(b, p) · w₀(b) ·
   A(b, q)` with `A, w₀ ≥ 0` — the `θ`-symmetric factorised form, `W ∘ θ = W`
   is proved — satisfies `⟨θF · F⟩ ≥ 0` for every `F` depending only on the
   plus side. The proof is the finite conditioning argument: conditioned on
   the boundary `b`, the double sum is a square times `w₀(b) ≥ 0`.
5. The smallest worked case: the two-value transfer kernel
   `T = !![2, 1; 1, 2]` (one link, link values indexed by `Fin 2`, the
   elements of `ZMod 2`). `T` is symmetric with positive entries, Perron
   eigenvalue `3` on constants, eigenvalue `1` on the zero-sum subspace;
   the normalised kernel therefore has spectral gap `1 - 1/3 = 2/3`.

## What is not claimed

The gap in item 5 is a **finite-volume** gap of an explicit finite kernel.
Nothing here addresses uniformity: **(U1)** the gap staying open as the volume
grows at fixed lattice spacing, and **(U2)** correlation decay at a physical
rate `m > 0` uniform in the lattice spacing along the renormalised
trajectory, are the open content of the mass gap problem (see the closure
contract on `open_yang_mills_mass_gap` in `GppVerify.YangMills.MassGap`).
They are not claimed, in any form, by this module.
-/

namespace GppLatticeGauge

/-! ## 1. Incidence geometry and the gauge action -/

section GaugeAction

variable {Sites Links : Type*} {G : Type*} [Group G]
variable (src tgt : Links → Sites)

/-- A gauge field configuration: an element of the finite gauge group `G` on
    each link. -/
abbrev Config (Links : Type*) (G : Type*) := Links → G

/-- The gauge action: a gauge transformation `g : Sites → G` acts on a
    configuration by conjugation along each link,
    `(g • U)(ℓ) = g(src ℓ) * U(ℓ) * (g(tgt ℓ))⁻¹`. -/
def gaugeAct (g : Sites → G) (U : Config Links G) (ℓ : Links) : G :=
  g (src ℓ) * U ℓ * (g (tgt ℓ))⁻¹

theorem gaugeAct_one (U : Config Links G) :
    gaugeAct src tgt (1 : Sites → G) U = U := by
  funext ℓ
  simp [gaugeAct]

theorem gaugeAct_mul (g h : Sites → G) (U : Config Links G) :
    gaugeAct src tgt (g * h) U = gaugeAct src tgt g (gaugeAct src tgt h U) := by
  funext ℓ
  simp only [gaugeAct, Pi.mul_apply, mul_inv_rev]
  group

end GaugeAction

/-! ## 2. Plaquette holonomy and the Wilson action -/

section Holonomy

variable {Sites Links : Type*} {G : Type*} [Group G]
variable (src tgt : Links → Sites)

/-- The site a signed link step starts at: forward steps start at `src`,
    backward steps at `tgt`. -/
def stepFrom (p : Links × Bool) : Sites := if p.2 then src p.1 else tgt p.1

/-- The site a signed link step ends at. -/
def stepTo (p : Links × Bool) : Sites := if p.2 then tgt p.1 else src p.1

/-- A walk from `x` to `y`: a list of signed links whose endpoints chain
    from `x` to `y`. -/
inductive Walk : Sites → Sites → List (Links × Bool) → Prop where
  | nil (x : Sites) : Walk x x []
  | cons {x y z : Sites} {p : Links × Bool} {ps : List (Links × Bool)}
      (hf : stepFrom src tgt p = x) (ht : stepTo src tgt p = y)
      (h : Walk y z ps) : Walk x z (p :: ps)

/-- The group element a single signed step contributes: `U ℓ` forward,
    `(U ℓ)⁻¹` backward. -/
def stepFactor (U : Config Links G) (p : Links × Bool) : G :=
  if p.2 then U p.1 else (U p.1)⁻¹

/-- The holonomy of a walk: the ordered product of its step factors. -/
def holonomy (U : Config Links G) : List (Links × Bool) → G
  | [] => 1
  | p :: ps => stepFactor U p * holonomy U ps

theorem stepFactor_gaugeAct (g : Sites → G) (U : Config Links G)
    (p : Links × Bool) :
    stepFactor (gaugeAct src tgt g U) p
      = g (stepFrom src tgt p) * stepFactor U p * (g (stepTo src tgt p))⁻¹ := by
  obtain ⟨ℓ, b⟩ := p
  cases b <;> simp [stepFactor, stepFrom, stepTo, gaugeAct, mul_inv_rev, inv_inv]
    <;> group

/-- Under a gauge transformation, the holonomy of a walk from `x` to `y`
    conjugates by the endpoint values. -/
theorem holonomy_gaugeAct (g : Sites → G) (U : Config Links G) {x y : Sites}
    {ps : List (Links × Bool)} (h : Walk src tgt x y ps) :
    holonomy (gaugeAct src tgt g U) ps
      = g x * holonomy U ps * (g y)⁻¹ := by
  induction h with
  | nil x => simp [holonomy]
  | cons hf ht h ih =>
    simp only [holonomy, stepFactor_gaugeAct, ih, hf, ht]
    group

/-- A class function on `G`: constant on conjugacy classes. -/
def IsClassFn (w : G → ℝ) : Prop := ∀ a b : G, w (a * b * a⁻¹) = w b

theorem holonomy_class_invariant {τ : G → ℝ} (hτ : IsClassFn τ)
    (g : Sites → G) (U : Config Links G) {x : Sites}
    {ps : List (Links × Bool)} (h : Walk src tgt x x ps) :
    τ (holonomy (gaugeAct src tgt g U) ps) = τ (holonomy U ps) := by
  rw [holonomy_gaugeAct src tgt g U h, hτ]

/-- The Wilson action: the sum of a class function of the holonomy over a
    finite set of plaquettes (closed walks, supplied as lists of signed
    links). -/
def wilsonAction (τ : G → ℝ) (plaq : Finset (List (Links × Bool)))
    (U : Config Links G) : ℝ :=
  ∑ ps ∈ plaq, τ (holonomy U ps)

/-- The Wilson action is gauge invariant, provided every plaquette in `plaq`
    is a closed walk. -/
theorem wilsonAction_gauge_invariant {τ : G → ℝ} (hτ : IsClassFn τ)
    {plaq : Finset (List (Links × Bool))}
    (hplaq : ∀ ps ∈ plaq, ∃ x, Walk src tgt x x ps)
    (g : Sites → G) (U : Config Links G) :
    wilsonAction τ plaq (gaugeAct src tgt g U)
      = wilsonAction τ plaq U := by
  apply Finset.sum_congr rfl
  intro ps hps
  obtain ⟨x, hx⟩ := hplaq ps hps
  exact holonomy_class_invariant src tgt hτ g U hx

end Holonomy

/-! ## 3. The Gibbs state -/

section Gibbs

variable {C : Type*} [Fintype C]

/-- The partition function of a weight `W` on a finite configuration
    space: the finite sum of the weights. -/
def partitionFn (W : C → ℝ) : ℝ := ∑ c, W c

/-- The expectation of `F` in the Gibbs state with weight `W`. -/
noncomputable def expectation (W : C → ℝ) (F : C → ℝ) : ℝ :=
  (partitionFn W)⁻¹ * ∑ c, F c * W c

theorem partitionFn_pos (W : C → ℝ) (hW : ∀ c, 0 < W c) [Nonempty C] :
    0 < partitionFn W := by
  show 0 < ∑ c, W c
  exact Finset.sum_pos (fun c _ => hW c) Finset.univ_nonempty

/-- The Boltzmann weight of an action `S`. -/
noncomputable def boltzmann (S : C → ℝ) (c : C) : ℝ := Real.exp (- S c)

omit [Fintype C] in
theorem boltzmann_pos (S : C → ℝ) (c : C) : 0 < boltzmann S c :=
  Real.exp_pos _

/-- The Gibbs partition function of any action is positive: every Boltzmann
    weight is positive and the configuration space is nonempty. -/
theorem gibbs_partitionFn_pos (S : C → ℝ) [Nonempty C] :
    0 < partitionFn (boltzmann S) :=
  partitionFn_pos _ (boltzmann_pos S)

theorem expectation_const (W : C → ℝ) (hW : partitionFn W ≠ 0) (a : ℝ) :
    expectation W (fun _ => a) = a := by
  have h1 : (∑ c, (fun _ => a) c * W c) = a * partitionFn W := by
    simp [partitionFn, Finset.mul_sum]
  rw [expectation, h1, mul_comm a _, ← mul_assoc, inv_mul_cancel₀ hW, one_mul]

end Gibbs

section GaugeGibbs

variable {Links : Type*} {G : Type*} [Group G] [Fintype G]
variable [Fintype Links] [DecidableEq Links]

/-- The partition function of the finite lattice gauge theory with Wilson
    action `wilsonAction τ plaq` is positive. -/
theorem gauge_partitionFn_pos (τ : G → ℝ)
    (plaq : Finset (List (Links × Bool))) :
    0 < partitionFn (boltzmann (wilsonAction τ plaq)) := by
  have : Nonempty (Config Links G) := ⟨fun _ => 1⟩
  exact gibbs_partitionFn_pos _

end GaugeGibbs

/-! ## 4. Reflection positivity, finite form

The configuration space is split as `B × P × P`: boundary (fixed) link
values `B`, plus-side link values `P`, minus-side link values `P`. The
reflection `θ` swaps the two `P` factors. The factorised weight below is the
`θ`-symmetric factorised form: the minus factor is the same function `A` as
the plus factor, which is exactly what makes `W ∘ θ = W` (proved as
`splitWeight_theta`). -/

section ReflectionPositivity

variable {B P : Type*} [Fintype B] [Fintype P]
variable (A : B → P → ℝ) (w0 : B → ℝ)

/-- The reflection on split configurations: swap plus and minus. -/
def thetaSwap (c : B × P × P) : B × P × P := (c.1, c.2.2, c.2.1)

omit [Fintype B] [Fintype P] in
theorem thetaSwap_involutive :
    Function.Involutive (thetaSwap (B := B) (P := P)) := by
  rintro ⟨b, p, q⟩
  rfl

/-- The pullback of a function along the reflection. -/
def thetaPull (F : B × P × P → ℝ) (c : B × P × P) : ℝ := F (thetaSwap c)

/-- The factorised Gibbs weight across the split:
    `W(b, p, q) = A(b, p) · w₀(b) · A(b, q)`. -/
def splitWeight (c : B × P × P) : ℝ :=
  A c.1 c.2.1 * w0 c.1 * A c.1 c.2.2

omit [Fintype B] [Fintype P] in
/-- The factorised weight is reflection invariant. -/
theorem splitWeight_theta (c : B × P × P) :
    splitWeight A w0 (thetaSwap c) = splitWeight A w0 c := by
  show A c.1 c.2.2 * w0 c.1 * A c.1 c.2.1 = A c.1 c.2.1 * w0 c.1 * A c.1 c.2.2
  ring

/-- Finite conditioning: with `F` depending only on the plus side, the
    `θF · F` numerator sum is a sum over boundary configurations of a square
    times the boundary weight. Only `w₀ ≥ 0` is needed: the plus/minus
    factor `A` appears inside the square. -/
theorem reflection_positivity_sum (hw0 : ∀ b, 0 ≤ w0 b) (f : P → ℝ) :
    0 ≤ ∑ c : B × P × P, (f c.2.2 * f c.2.1) * splitWeight A w0 c := by
  have key : ∀ b : B, w0 b * (∑ p : P, A b p * f p) ^ 2
      = ∑ p : P, ∑ q : P, (f q * f p) * splitWeight A w0 (b, p, q) := by
    intro b
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp only [splitWeight]
    ring
  have hsum : ∑ c : B × P × P, (f c.2.2 * f c.2.1) * splitWeight A w0 c
      = ∑ b : B, w0 b * (∑ p : P, A b p * f p) ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.sum_prod_type]
    exact (key b).symm
  rw [hsum]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (hw0 b) (sq_nonneg _))

/-- **Reflection positivity (finite form).** For the reflection-symmetric
    factorised Gibbs weight, `⟨θF · F⟩ ≥ 0` for every `F` depending only on
    the plus side. The hypotheses used are exactly `w₀ ≥ 0` and `Z > 0`;
    nonnegativity of `A` is what makes `W` a nonnegative weight and is not
    needed for the inequality. -/
theorem reflection_positivity (hw0 : ∀ b, 0 ≤ w0 b)
    (hZ : 0 < partitionFn (splitWeight A w0)) (f : P → ℝ) :
    0 ≤ expectation (splitWeight A w0) (fun c => f c.2.2 * f c.2.1) := by
  unfold expectation
  apply mul_nonneg
  · exact inv_nonneg.mpr hZ.le
  · exact reflection_positivity_sum A w0 hw0 f

end ReflectionPositivity

/-! ## 5. The smallest worked case

One link, two link values (indexed by `Fin 2`, the elements of `ZMod 2`).
The transfer kernel between successive time slices has bond Boltzmann
weights `K(a, b) = 2` if `a = b` and `1` if `a ≠ b`, i.e. the explicit
matrix `T = !![2, 1; 1, 2]` over `ℝ`. Its spectrum is computed exactly:
eigenvalue `3` on constants (the vacuum), eigenvalue `1` on the zero-sum
subspace. The normalised kernel `3⁻¹ • T` therefore has spectral gap
`1 - 1/3 = 2/3`. This is a finite-volume gap of this finite kernel; see the
module header for what it does not claim. -/

section WorkedCase

/-- The bond Boltzmann weight of the two-value link: `2` on equal values,
    `1` on unequal values. -/
def bondWeight (a b : Fin 2) : ℝ := if a = b then 2 else 1

/-- The transfer matrix of the smallest case. -/
def transferT : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

theorem transferT_apply (a b : Fin 2) : transferT a b = bondWeight a b := by
  fin_cases a <;> fin_cases b <;> simp [transferT, bondWeight]

theorem transferT_transpose : transferTᵀ = transferT := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem transferT_pos : ∀ i j, 0 < transferT i j := by
  intro i j
  rw [transferT_apply]
  by_cases h : i = j <;> simp [bondWeight, h]

/-- Perron eigenvalue: `T` acts on constant vectors as `3 • `. -/
theorem transferT_mulVec_const :
    transferT *ᵥ ![1, 1] = 3 • ![1, 1] := by
  ext i
  fin_cases i <;>
    simp [transferT, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The zero-sum subspace is the `1`-eigenspace of `T`, exactly. -/
theorem transferT_gap (v : Fin 2 → ℝ) (hv : v 0 + v 1 = 0) :
    transferT *ᵥ v = v := by
  have hv1 : v 1 = -v 0 := by linarith
  ext i
  fin_cases i <;>
    simp [transferT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · show 2 * v 0 + v 1 = v 0
    rw [hv1]; ring
  · show v 0 + 2 * v 1 = v 1
    rw [hv1]; ring

/-- The normalised kernel fixes the vacuum (constants). -/
theorem transferT_normalized_const :
    ((3 : ℝ)⁻¹ • transferT) *ᵥ ![1, 1] = ![1, 1] := by
  rw [Matrix.smul_mulVec, transferT_mulVec_const]
  ext i
  fin_cases i <;> simp

/-- The normalised kernel contracts the zero-sum subspace by exactly
    `1/3`: its second eigenvalue is `1/3`, so its spectral gap is
    `1 - 1/3 = 2/3 > 0`. -/
theorem transferT_normalized_gap (v : Fin 2 → ℝ) (hv : v 0 + v 1 = 0) :
    ((3 : ℝ)⁻¹ • transferT) *ᵥ v = (1 / 3 : ℝ) • v := by
  rw [Matrix.smul_mulVec, transferT_gap v hv]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem transferT_gap_value : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num

end WorkedCase

end GppLatticeGauge
