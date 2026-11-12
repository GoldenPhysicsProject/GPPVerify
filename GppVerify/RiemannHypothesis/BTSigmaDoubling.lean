import GppVerify.RiemannHypothesis.BTSigmaShiftedTheta
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# BT-Σ: the doubling (B) as a `BTSigmaDatum`

Lean port (Heart of the Cosmos / Grok, GPPDiscovery5 seat) of the operator-level doubling (B)
of GPPDiscovery5 `c755de5` (`BTSigmaGenuineBT2Theta`, paper part), as confirmed by Turbo on
GPP-bridge PR #11, comment 6815125311.

**Construction (all PROVED, standard axioms).** For *any* `D : BTSigmaDatum H Gu Gp` put
`H' = H ⊕₂ H`, `Gu' = Gu ⊕₂ Gu`, `Gp' = Gp ⊕₂ Gp` (`WithLp 2` products) and
* `T' = T* ⊕ (−T*)` on `dom T* ⊕ dom T*`;
* `Γ₀' = (Γ₀ x₁, Γ₀ x₂)`, `Γ₁' = (Γ₁ x₁, −Γ₁ x₂)`, blockwise on the unit and prime strata;
* test vectors `(ψ_{h,W}, 0)`.
Green's identity holds because the second copy's Green form and its block forms both change
sign (`greenForm_double`), and the boundary map is onto (`double`). The swap
`J(x₁, x₂) = (x₂, x₁)` is a unitary involution with `T' J = −J T'` (`swap_anticomm`), and `T'`
takes a negative form value wherever `T*` takes a positive one (`double_form_neg`), so `T'` is
not semibounded when `T* ≥ 0` is nontrivial.

**What transfers.** The prime and unit blocks on test vectors are unchanged
(`primeBlock_double`, `unitBlock_double`), so finite-cut BT3, BT3 and (P-UNIT) hold for the
double iff they hold for `D` (`traceSN_double_iff`, `trace_double_iff`, `punit_double_iff`);
(P-COV) transfers with `S'_b = S_b ⊕ S_b` (`pcov_double`). The kernel of `Γ'` is
`ker Γ ⊕ ker Γ` (`mem_kerΓ_double_iff`).

**What it does not do — ζ-blind.** The swap does not act `W ↦ −W` on the test family: if it
did, every test vector of `D` would vanish (`swap_reflection_forces_zero`). The doubled family
meets both operator clauses of `PLogTheta` (`double_operator_clauses`), and the tree kill
`ptheta_punit_kill` still forbids the full clause against (P-UNIT) (`double_ptheta_punit_kill`).
Nothing in the doubling sees `ζ`: it works verbatim for every datum.

Lean results PROVED, standard axioms. No `sorry`, no custom axiom, no cited theorem.
(P-LOG) provenance, `c < 0`, (BT-Σ), ARP, CGC and RH remain OPEN.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaDoubling

open GppBTSigmaShiftedTheta GppBTSigmaLocalEuler GppBTSigma Complex
open scoped InnerProductSpace ContDiff

/-- The `ℓ²` double `E ⊕₂ E`. -/
abbrev Dbl (E : Type*) := WithLp 2 (E × E)

section Double

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- `dom T ⊕ dom T` inside `H ⊕₂ H`. -/
abbrev dblDomain (T : H →ₗ.[ℂ] H) : Submodule ℂ (Dbl H) :=
  (T.domain.prod T.domain).comap (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap

/-- First component on `dblDomain`. -/
def q₁ (T : H →ₗ.[ℂ] H) : dblDomain T →ₗ[ℂ] T.domain :=
  LinearMap.codRestrict T.domain
    ((LinearMap.fst ℂ H H).comp
      ((WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap.comp (dblDomain T).subtype))
    (fun x => x.2.1)

/-- Second component on `dblDomain`. -/
def q₂ (T : H →ₗ.[ℂ] H) : dblDomain T →ₗ[ℂ] T.domain :=
  LinearMap.codRestrict T.domain
    ((LinearMap.snd ℂ H H).comp
      ((WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap.comp (dblDomain T).subtype))
    (fun x => x.2.2)

/-- Pair two linear maps into the `ℓ²` double. -/
def pairL {M G : Type*} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (a b : M →ₗ[ℂ] G) : M →ₗ[ℂ] Dbl G :=
  (WithLp.linearEquiv 2 ℂ (G × G)).symm.toLinearMap.comp (a.prod b)

section PairL

variable {M G : Type*} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup G]
  [InnerProductSpace ℂ G]

@[simp] theorem pairL_fst (a b : M →ₗ[ℂ] G) (m : M) : (pairL a b m).fst = a m := rfl

@[simp] theorem pairL_snd (a b : M →ₗ[ℂ] G) (m : M) : (pairL a b m).snd = b m := rfl

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] in
theorem dbl_ext {a b : Dbl G} (h₁ : a.fst = b.fst) (h₂ : a.snd = b.snd) : a = b := by
  cases a with | toLp a => cases b with | toLp b => simp_all [Prod.ext_iff]

omit [InnerProductSpace ℂ G] in
theorem dbl_eq_zero_iff (v : Dbl G) : v = 0 ↔ v.fst = 0 ∧ v.snd = 0 :=
  ⟨fun h => by simp [h], fun h => dbl_ext (by simp [h.1]) (by simp [h.2])⟩

/-- The block form of paired boundary maps splits over the two copies. PROVED. -/
theorem blockForm_pairL (a b c d : M →ₗ[ℂ] G) (x y : M) :
    blockForm (pairL a b x) (pairL c d x) (pairL a b y) (pairL c d y) =
      blockForm (a x) (c x) (a y) (c y) + blockForm (b x) (d x) (b y) (d y) := by
  unfold blockForm
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  show ⟪c x, a y⟫_ℂ + ⟪d x, b y⟫_ℂ - (⟪a x, c y⟫_ℂ + ⟪b x, d y⟫_ℂ) = _
  ring

end PairL

theorem blockForm_neg {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (a b c d : G) : blockForm a (-b) c (-d) = -blockForm a b c d := by
  simp only [blockForm, inner_neg_left, inner_neg_right]
  ring

/-- `T ⊕ (−T)` on `dom T ⊕ dom T`. -/
abbrev dblOp (T : H →ₗ.[ℂ] H) : Dbl H →ₗ.[ℂ] Dbl H where
  domain := dblDomain T
  toFun := pairL (T.toFun.comp (q₁ T)) (-(T.toFun.comp (q₂ T)))

/-- First component on `dom (T ⊕ −T)`. -/
def pr₁ (T : H →ₗ.[ℂ] H) : (dblOp T).domain →ₗ[ℂ] T.domain := q₁ T

/-- Second component on `dom (T ⊕ −T)`. -/
def pr₂ (T : H →ₗ.[ℂ] H) : (dblOp T).domain →ₗ[ℂ] T.domain := q₂ T

@[simp] theorem pr₁_coe (T : H →ₗ.[ℂ] H) (x : (dblOp T).domain) :
    ((pr₁ T x : T.domain) : H) = (x : Dbl H).fst := rfl

@[simp] theorem pr₂_coe (T : H →ₗ.[ℂ] H) (x : (dblOp T).domain) :
    ((pr₂ T x : T.domain) : H) = (x : Dbl H).snd := rfl

theorem dblOp_fst (T : H →ₗ.[ℂ] H) (x : (dblOp T).domain) :
    (dblOp T x).fst = T (pr₁ T x) := rfl

theorem dblOp_snd (T : H →ₗ.[ℂ] H) (x : (dblOp T).domain) :
    (dblOp T x).snd = -T (pr₂ T x) := rfl

/-- The Green form of the double is the first copy's minus the second copy's. PROVED. -/
theorem greenForm_double (T : H →ₗ.[ℂ] H) (x y : (dblOp T).domain) :
    greenForm (dblOp T) x y =
      greenForm T (pr₁ T x) (pr₁ T y) - greenForm T (pr₂ T x) (pr₂ T y) := by
  unfold greenForm
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  show ⟪T (pr₁ T x), ((pr₁ T y : T.domain) : H)⟫_ℂ + ⟪-T (pr₂ T x), ((pr₂ T y : T.domain) : H)⟫_ℂ -
      (⟪((pr₁ T x : T.domain) : H), T (pr₁ T y)⟫_ℂ +
        ⟪((pr₂ T x : T.domain) : H), -T (pr₂ T y)⟫_ℂ) = _
  rw [inner_neg_left, inner_neg_right]
  ring

/-- Rebuild a vector of `dom T ⊕ dom T` from its two components. -/
def mkDbl (T : H →ₗ.[ℂ] H) (x₁ x₂ : T.domain) : (dblOp T).domain :=
  ⟨WithLp.toLp 2 ((x₁ : H), (x₂ : H)), x₁.2, x₂.2⟩

@[simp] theorem pr₁_mkDbl (T : H →ₗ.[ℂ] H) (x₁ x₂ : T.domain) : pr₁ T (mkDbl T x₁ x₂) = x₁ :=
  rfl

@[simp] theorem pr₂_mkDbl (T : H →ₗ.[ℂ] H) (x₁ x₂ : T.domain) : pr₂ T (mkDbl T x₁ x₂) = x₂ :=
  rfl

@[simp] theorem mkDbl_fst (T : H →ₗ.[ℂ] H) (x₁ x₂ : T.domain) :
    ((mkDbl T x₁ x₂ : (dblOp T).domain) : Dbl H).fst = x₁ := rfl

@[simp] theorem mkDbl_snd (T : H →ₗ.[ℂ] H) (x₁ x₂ : T.domain) :
    ((mkDbl T x₁ x₂ : (dblOp T).domain) : Dbl H).snd = x₂ := rfl

/-- **The doubling (B) of any datum is a `BTSigmaDatum`.** Green's identity and surjectivity
PROVED in the construction. -/
noncomputable abbrev double (D : BTSigmaDatum H Gu Gp) :
    BTSigmaDatum (Dbl H) (Dbl Gu) (Dbl Gp) where
  Tstar := dblOp D.Tstar
  Γ₀u := pairL (D.Γ₀u.comp (pr₁ D.Tstar)) (D.Γ₀u.comp (pr₂ D.Tstar))
  Γ₁u := pairL (D.Γ₁u.comp (pr₁ D.Tstar)) (-(D.Γ₁u.comp (pr₂ D.Tstar)))
  Γ₀p := pairL (D.Γ₀p.comp (pr₁ D.Tstar)) (D.Γ₀p.comp (pr₂ D.Tstar))
  Γ₁p := pairL (D.Γ₁p.comp (pr₁ D.Tstar)) (-(D.Γ₁p.comp (pr₂ D.Tstar)))
  green x y := by
    rw [greenForm_double, D.green, D.green, blockForm_pairL, blockForm_pairL]
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, blockForm_neg]
    ring
  surj := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    obtain ⟨x₁, hx₁⟩ := D.surj ((a.fst, b.fst), (c.fst, d.fst))
    obtain ⟨x₂, hx₂⟩ := D.surj ((a.snd, b.snd), (-c.snd, -d.snd))
    simp only [Prod.mk.injEq] at hx₁ hx₂
    refine ⟨mkDbl D.Tstar x₁ x₂, ?_⟩
    simp only [Prod.mk.injEq]
    refine ⟨⟨dbl_ext ?_ ?_, dbl_ext ?_ ?_⟩, dbl_ext ?_ ?_, dbl_ext ?_ ?_⟩
    · exact hx₁.1.1
    · exact hx₂.1.1
    · exact hx₁.1.2
    · exact hx₂.1.2
    · exact hx₁.2.1
    · show -D.Γ₁u x₂ = _
      rw [hx₂.2.1, neg_neg]
    · exact hx₁.2.2
    · show -D.Γ₁p x₂ = _
      rw [hx₂.2.2, neg_neg]
  testVec h W := mkDbl D.Tstar (D.testVec h W) 0

variable (D : BTSigmaDatum H Gu Gp)

@[simp] theorem double_testVec_fst (h : ℝ → ℝ) (W : ℝ) :
    (((double D).testVec h W : (double D).Tstar.domain) : Dbl H).fst = D.testVec h W := rfl

@[simp] theorem double_testVec_snd (h : ℝ → ℝ) (W : ℝ) :
    (((double D).testVec h W : (double D).Tstar.domain) : Dbl H).snd = 0 := rfl

/-- The prime block of the double on test vectors is the prime block of `D`. PROVED. -/
theorem primeBlock_double (h : ℝ → ℝ) (W : ℝ) : primeBlock (double D) h W = primeBlock D h W := by
  unfold primeBlock
  rw [blockForm_pairL]
  show blockForm (D.Γ₀p (D.testVec h W)) (D.Γ₁p (D.testVec h W)) (D.Γ₀p (D.testVec h W))
      (D.Γ₁p (D.testVec h W)) + blockForm (D.Γ₀p (0 : D.Tstar.domain))
      (-D.Γ₁p (0 : D.Tstar.domain)) (D.Γ₀p (0 : D.Tstar.domain)) (-D.Γ₁p (0 : D.Tstar.domain)) = _
  simp [blockForm]

/-- The unit block of the double on test vectors is the unit block of `D`. PROVED. -/
theorem unitBlock_double (h : ℝ → ℝ) (W : ℝ) : unitBlock (double D) h W = unitBlock D h W := by
  unfold unitBlock
  rw [blockForm_pairL]
  show blockForm (D.Γ₀u (D.testVec h W)) (D.Γ₁u (D.testVec h W)) (D.Γ₀u (D.testVec h W))
      (D.Γ₁u (D.testVec h W)) + blockForm (D.Γ₀u (0 : D.Tstar.domain))
      (-D.Γ₁u (0 : D.Tstar.domain)) (D.Γ₀u (0 : D.Tstar.domain)) (-D.Γ₁u (0 : D.Tstar.domain)) = _
  simp [blockForm]

/-- Finite-cut BT3 transfers both ways. PROVED. -/
theorem traceSN_double_iff (S : Finset ℕ) (N : ℕ) :
    BTSigmaTraceSN (double D) S N ↔ BTSigmaTraceSN D S N := by
  simp only [BTSigmaTraceSN, primeBlock_double]

/-- BT3 transfers both ways. PROVED. -/
theorem trace_double_iff : BTSigmaTrace (double D) ↔ BTSigmaTrace D := by
  simp only [BTSigmaTrace, primeBlock_double]

/-- (P-UNIT) transfers both ways. PROVED. -/
theorem punit_double_iff : PUnit (double D) ↔ PUnit D := by
  simp only [GppBTSigmaLocalEuler.PUnit, unitBlock_double]

/-- (P-COV) transfers with `S'_b = S_b ⊕ S_b`. PROVED. -/
theorem pcov_double (Sd : ℝ → H ≃ₗᵢ[ℂ] H) (hS : PCov D Sd) :
    PCov (double D) (fun b => LinearIsometryEquiv.withLpProdCongr 2 (Sd b) (Sd b)) := by
  obtain ⟨hgrp, hmove⟩ := hS
  refine ⟨fun a b x => dbl_ext ?_ ?_, fun h W b => dbl_ext ?_ ?_⟩
  · simpa using hgrp a b x.fst
  · simpa using hgrp a b x.snd
  · simpa using hmove h W b
  · simp

/-- `ker Γ'` is `ker Γ ⊕ ker Γ`. PROVED. -/
theorem mem_kerΓ_double_iff (x : (dblOp D.Tstar).domain) :
    ((double D).Γ₀u x = 0 ∧ (double D).Γ₁u x = 0 ∧ (double D).Γ₀p x = 0 ∧
        (double D).Γ₁p x = 0) ↔
      (D.Γ₀u (pr₁ D.Tstar x) = 0 ∧ D.Γ₁u (pr₁ D.Tstar x) = 0 ∧ D.Γ₀p (pr₁ D.Tstar x) = 0 ∧
        D.Γ₁p (pr₁ D.Tstar x) = 0) ∧
      (D.Γ₀u (pr₂ D.Tstar x) = 0 ∧ D.Γ₁u (pr₂ D.Tstar x) = 0 ∧ D.Γ₀p (pr₂ D.Tstar x) = 0 ∧
        D.Γ₁p (pr₂ D.Tstar x) = 0) := by
  simp only [dbl_eq_zero_iff, pairL_fst, pairL_snd, LinearMap.comp_apply, LinearMap.neg_apply,
    neg_eq_zero]
  tauto

end Double

section Swap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The swap `J(x₁, x₂) = (x₂, x₁)` on `H ⊕₂ H`. -/
noncomputable def swapJ : Dbl H ≃ₗᵢ[ℂ] Dbl H := LinearIsometryEquiv.withLpProdComm 2 ℂ H H

@[simp] theorem swapJ_fst (x : Dbl H) : (swapJ x).fst = x.snd := rfl
@[simp] theorem swapJ_snd (x : Dbl H) : (swapJ x).snd = x.fst := rfl

/-- The swap is an involution. PROVED. -/
theorem swapJ_invol (x : Dbl H) : swapJ (swapJ x) = x := dbl_ext rfl rfl

/-- **`J T' J = −T'`.** The swap maps `dom T'` to itself and anticommutes with `T ⊕ (−T)`.
PROVED. -/
theorem swap_anticomm (T : H →ₗ.[ℂ] H) (x : (dblOp T).domain) :
    ∃ y : (dblOp T).domain, (y : Dbl H) = swapJ x ∧ dblOp T y = -swapJ (dblOp T x) := by
  refine ⟨mkDbl T (pr₂ T x) (pr₁ T x), dbl_ext rfl rfl, dbl_ext ?_ ?_⟩
  · show T (pr₂ T x) = -(-T (pr₂ T x))
    rw [neg_neg]
  · show -T (pr₁ T x) = -T (pr₁ T x)
    rfl

/-- **Not semibounded.** Wherever `T` has a positive form value, `T ⊕ (−T)` has the negative of
it. PROVED. -/
theorem double_form_neg (T : H →ₗ.[ℂ] H) (x : T.domain) :
    ∃ y : (dblOp T).domain, (⟪dblOp T y, (y : Dbl H)⟫_ℂ).re = -(⟪T x, (x : H)⟫_ℂ).re := by
  refine ⟨mkDbl T 0 x, ?_⟩
  rw [WithLp.prod_inner_apply]
  show (⟪T (0 : T.domain), ((0 : T.domain) : H)⟫_ℂ + ⟪-T x, (x : H)⟫_ℂ).re = _
  simp

end Swap

section ZetaBlind

variable {H Gu Gp : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Gu] [InnerProductSpace ℂ Gu]
  [NormedAddCommGroup Gp] [InnerProductSpace ℂ Gp]

/-- **The swap does not reflect the test family.** If `J` acted `W ↦ −W` on the doubled test
vectors, every test vector of `D` would be zero. PROVED. -/
theorem swap_reflection_forces_zero (D : BTSigmaDatum H Gu Gp)
    (hJ : ∀ (h : ℝ → ℝ) (W : ℝ),
      (((double D).testVec h (-W) : (double D).Tstar.domain) : Dbl H) =
        swapJ ((double D).testVec h W)) (h : ℝ → ℝ) (W : ℝ) :
    ((D.testVec h W : D.Tstar.domain) : H) = 0 := by
  have := congrArg WithLp.fst (hJ h (-W))
  simpa using this

/-- **Operator-level clauses of `PLogTheta` hold for the doubled family.** The swap is a unitary
involution anticommuting with every `T'`. PROVED. -/
theorem double_operator_clauses (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp) :
    (∀ x : Dbl H, swapJ (swapJ x) = x) ∧
      (∀ S N (x : (double (D S N)).Tstar.domain), ∃ y : (double (D S N)).Tstar.domain,
        (y : Dbl H) = swapJ x ∧ (double (D S N)).Tstar y = -swapJ ((double (D S N)).Tstar x)) :=
  ⟨swapJ_invol, fun S N x => swap_anticomm (D S N).Tstar x⟩

/-- **ζ-blind.** Doubling meets the operator clause but cannot meet the full (P-θ) clause against
(P-UNIT): the tree kill applies to the doubled family with any `J`. PROVED. -/
theorem double_ptheta_punit_kill (D : Finset ℕ → ℕ → BTSigmaDatum H Gu Gp)
    (J : Dbl H ≃ₗᵢ[ℂ] Dbl H) (S : Finset ℕ) (N : ℕ) :
    ¬ (PLogTheta (fun S N => double (D S N)) J ∧ PUnit (D S N)) := by
  rw [← punit_double_iff]
  exact ptheta_punit_kill (fun S N => double (D S N)) J S N

end ZetaBlind

end GppBTSigmaDoubling
