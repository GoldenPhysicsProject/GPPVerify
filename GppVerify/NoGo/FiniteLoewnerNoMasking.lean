import GppVerify.NoGo.FiniteNoMasking
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# No finite on-line mass masks the Loewner (Stieltjes) negativity of off-axis quartets

Companion to `GppNoGo.FiniteNoMaskingMulti` (real-node Pick form, #300), now in the shifted-Stieltjes
picture of Codex's completed resolvent response
(`work/codex/2026-10-12_completed_resolvent_sector_passivity_and_loewner_gap.md`, §B).

Setup. In `m_*(u) = Σ 1/(u + 1 − z²)`:
* an off-axis quartet contributes `2 Re 1/(u + a + ib)` with `b ≠ 0`;
* an on-line pair contributes `κ/(u + μ)` with `μ > 0`.

Take `r` quartets with distinct `(a_j, b_j²)`, `a_j > 0`, `b_j ≠ 0`, plus `m` pieces at distinct
`μ_l > 0` with arbitrary real weights `κ_l`. Write `f_j = 1/(u + a_j + i b_j) = R_j + i I_j` and
`g_l = 1/(u + μ_l)`.

* `loewnerK`: the Loewner kernel `Σ_j 2(R_j(x)R_j(y) − I_j(x)I_j(y)) + Σ_l κ_l g_l(x) g_l(y)`.
  * `loewnerK_eq`: off the diagonal it is the divided difference `−(m(x) − m(y))/(x − y)`.
  * `hasDerivAt_resp`: on the diagonal it is `−m'(x)`.
  So it is exactly the Loewner matrix of `m`.
* `loewner_form`: the form `Σ c_x c_y L(x,y)` equals
  `Σ_j 2((Σ c R_j)² − (Σ c I_j)²) + Σ_l κ_l (Σ c g_l)²`.
* `Ppoly_natDegree_lt`, `features_independent_on`: the cleared polynomial has degree `< 2r + m`,
  so a feature combination vanishing at **any** `2r + m` distinct positive nodes clears to the zero
  polynomial. Evaluating at `−μ_l` and at the complex roots `−a_j + i b_j` then kills every
  coefficient (`eq_zero_of_Ppoly`). This is Codex's "scaled Vandermonde after a partial-fraction
  change of basis" in polynomial form.
* `span_top_on`, `realize`: at every such node set, every moment vector is realized by weights
  supported on the nodes. `form_of_moments`: the form then equals
  `Σ_j 2(τ_{j,R}² − τ_{j,I}²) + Σ_l κ_l τ_l²`.
* `no_masking`: at **every** set of `≥ 2r + m` positive nodes, the Loewner form is `−2 Σ_j t_j²` on
  an `r`-dimensional family of weights. **No finite on-line mass, of any sign, makes it PSD.**
* `pos_family`, `pos_family_pos`: with `κ_l > 0`, the same nodes carry an `(r + m)`-dimensional
  family on which the form is `2Σ s_j² + Σ κ_l t_l² > 0`. At exactly `2r + m` nodes, the two
  families force inertia `(r + m, r, 0)` (Codex's C6 Loewner theorem, 2026-10-12, GPP-bridge PR #11
  comment 6121892934), by a dimension count that is not itself formalized here.

**Scope.** Finite only. For the actual `ξ` the on-line family is infinite, and Stieltjes-ness of the
full `m_*` (support in `[1, ∞)`) is Codex's v34 RH-equivalent criterion. This file proves only that
no *finite* on-line correction can mask an off-axis quartet. **No RH claim.**
-/

namespace GppNoGo.FiniteLoewnerNoMasking

open Finset Polynomial

variable {r m : ℕ}

/-- `|u + a + ib|²`. -/
def N (a b u : ℝ) : ℝ := (u + a) ^ 2 + b ^ 2

/-- `Re 1/(u + a + ib)`. -/
noncomputable def R (a b u : ℝ) : ℝ := (u + a) / N a b u

/-- `Im 1/(u + a + ib)`. -/
noncomputable def I (a b u : ℝ) : ℝ := -b / N a b u

/-- On-line piece `1/(u + μ)`. -/
noncomputable def g (μ u : ℝ) : ℝ := 1 / (u + μ)

lemma N_pos {a b u : ℝ} (hu : 0 < u + a) : 0 < N a b u := by unfold N; positivity

/-- The response `m(u) = Σ_j 2 Re f_j(u) + Σ_l κ_l g_l(u)`. -/
noncomputable def resp (a b : Fin r → ℝ) (μ κ : Fin m → ℝ) (u : ℝ) : ℝ :=
  ∑ j, 2 * R (a j) (b j) u + ∑ l, κ l * g (μ l) u

/-- The Loewner kernel. -/
noncomputable def loewnerK (a b : Fin r → ℝ) (μ κ : Fin m → ℝ) (x y : ℝ) : ℝ :=
  ∑ j, 2 * (R (a j) (b j) x * R (a j) (b j) y - I (a j) (b j) x * I (a j) (b j) y) +
    ∑ l, κ l * (g (μ l) x * g (μ l) y)

/-- Off the diagonal the kernel is the divided difference of `m`. -/
theorem loewnerK_eq {a b : Fin r → ℝ} {μ κ : Fin m → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : ∀ j, 0 < a j) (hμ : ∀ l, 0 < μ l) (hxy : x ≠ y) :
    loewnerK a b μ κ x y = -(resp a b μ κ x - resp a b μ κ y) / (x - y) := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [eq_div_iff hxy', loewnerK, resp, resp, add_mul, Finset.sum_mul, Finset.sum_mul]
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, neg_add, ←
    Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := (N_pos (b := b j) (by linarith [ha j] : 0 < x + a j)).ne'
    have h2 := (N_pos (b := b j) (by linarith [ha j] : 0 < y + a j)).ne'
    unfold R I
    field_simp
    unfold N
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    have h1 : x + μ l ≠ 0 := by linarith [hμ l]
    have h2 : y + μ l ≠ 0 := by linarith [hμ l]
    unfold g
    field_simp
    ring

/-- On the diagonal the kernel is `−m'`. -/
theorem hasDerivAt_resp {a b : Fin r → ℝ} {μ κ : Fin m → ℝ} {x : ℝ} (hx : 0 < x)
    (ha : ∀ j, 0 < a j) (hμ : ∀ l, 0 < μ l) :
    HasDerivAt (resp a b μ κ) (-loewnerK a b μ κ x x) x := by
  have hR : ∀ j, HasDerivAt (fun u => 2 * R (a j) (b j) u)
      (-(2 * (R (a j) (b j) x * R (a j) (b j) x - I (a j) (b j) x * I (a j) (b j) x))) x := by
    intro j
    have hN := (N_pos (b := b j) (by linarith [ha j] : 0 < x + a j)).ne'
    have hnum : HasDerivAt (fun u => u + a j) 1 x := (hasDerivAt_add_const_iff (a j)).mpr
      (hasDerivAt_id' x)
    have hden : HasDerivAt (fun u => N (a j) (b j) u) (2 * (x + a j)) x := by
      unfold N
      exact ((hasDerivAt_add_const_iff _).mpr (HasDerivAt.fun_pow hnum 2)).congr_deriv
        (by norm_num)
    have := HasDerivAt.const_mul 2 (HasDerivAt.fun_div hnum hden hN)
    refine this.congr_deriv ?_
    unfold R I
    unfold N at hN ⊢
    field_simp
    ring
  have hg : ∀ l, HasDerivAt (fun u => κ l * g (μ l) u)
      (-(κ l * (g (μ l) x * g (μ l) x))) x := by
    intro l
    have h0 : x + μ l ≠ 0 := by linarith [hμ l]
    have hnum : HasDerivAt (fun u => u + μ l) 1 x := (hasDerivAt_add_const_iff (μ l)).mpr
      (hasDerivAt_id' x)
    have := HasDerivAt.const_mul (κ l) (HasDerivAt.fun_div (hasDerivAt_const x (1 : ℝ)) hnum h0)
    refine this.congr_deriv ?_
    unfold g
    field_simp
    ring
  have := HasDerivAt.add (HasDerivAt.fun_sum fun j (_ : j ∈ (univ : Finset (Fin r))) => hR j)
    (HasDerivAt.fun_sum fun l (_ : l ∈ (univ : Finset (Fin m))) => hg l)
  refine this.congr_deriv ?_
  rw [loewnerK, neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]

/-- **The Loewner form through the features.** -/
theorem loewner_form (a b : Fin r → ℝ) (μ κ : Fin m → ℝ) (S : Finset ℝ) (c : ℝ → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * loewnerK a b μ κ x y =
      ∑ j, 2 * ((∑ x ∈ S, c x * R (a j) (b j) x) ^ 2 - (∑ x ∈ S, c x * I (a j) (b j) x) ^ 2) +
        ∑ l, κ l * (∑ x ∈ S, c x * g (μ l) x) ^ 2 := by
  have key : ∀ F : ℝ → ℝ,
      (∑ x ∈ S, c x * F x) ^ 2 = ∑ x ∈ S, ∑ y ∈ S, c x * c y * (F x * F y) := by
    intro F
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp_rw [key, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hswap : ∀ {ι : Type} [Fintype ι] (F : ι → ℝ → ℝ → ℝ),
      ∑ i : ι, ∑ x ∈ S, ∑ y ∈ S, F i x y = ∑ x ∈ S, ∑ y ∈ S, ∑ i : ι, F i x y := by
    intro ι _ F
    calc _ = ∑ x ∈ S, ∑ i : ι, ∑ y ∈ S, F i x y := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [hswap, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [loewnerK, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun l _ => by ring

/-- Feature index: `(j, 0) ↦ R_j`, `(j, 1) ↦ I_j`, `l ↦ g_l`. -/
abbrev Idx (r m : ℕ) := (Fin r × Fin 2) ⊕ Fin m

/-- Feature vector. -/
noncomputable def φ (a b : Fin r → ℝ) (μ : Fin m → ℝ) (x : ℝ) : Idx r m → ℝ
  | Sum.inl (j, k) => if (k : ℕ) = 0 then R (a j) (b j) x else I (a j) (b j) x
  | Sum.inr l => g (μ l) x

/-- `N` as a polynomial. -/
noncomputable def Np (a b : ℝ) : ℝ[X] := (X + C a) ^ 2 + C (b ^ 2)
/-- `u + μ` as a polynomial. -/
noncomputable def Lp (μ : ℝ) : ℝ[X] := X + C μ

/-- The quartet numerators `α(X + a) − βb`. -/
noncomputable def Apoly (a b : Fin r → ℝ) (c : Idx r m → ℝ) (j : Fin r) : ℝ[X] :=
  C (c (Sum.inl (j, 0))) * (X + C (a j)) - C (c (Sum.inl (j, 1)) * b j)

/-- The cleared-denominator polynomial. -/
noncomputable def Ppoly (a b : Fin r → ℝ) (μ : Fin m → ℝ) (c : Idx r m → ℝ) : ℝ[X] :=
  ∑ j, Apoly a b c j * (∏ j' ∈ univ.erase j, Np (a j') (b j')) * ∏ l, Lp (μ l) +
    ∑ l, C (c (Sum.inr l)) * (∏ j, Np (a j) (b j)) * ∏ l' ∈ univ.erase l, Lp (μ l')

lemma sum_idx (c v : Idx r m → ℝ) :
    ∑ i, c i * v i = ∑ j : Fin r, (c (Sum.inl (j, 0)) * v (Sum.inl (j, 0)) +
      c (Sum.inl (j, 1)) * v (Sum.inl (j, 1))) + ∑ l : Fin m, c (Sum.inr l) * v (Sum.inr l) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Fin.sum_univ_two _

lemma Ppoly_eval {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hμ : ∀ l, 0 < μ l)
    (c : Idx r m → ℝ) {x : ℝ} (hx : 0 < x) :
    (Ppoly a b μ c).eval x =
      ((∏ j, N (a j) (b j) x) * ∏ l, (x + μ l)) * ∑ i, c i * φ a b μ x i := by
  have hN : ∀ j, N (a j) (b j) x ≠ 0 := fun j => (N_pos (by linarith [ha j])).ne'
  have hL : ∀ l, x + μ l ≠ 0 := fun l => by linarith [hμ l]
  have hNe : ∀ j, (Np (a j) (b j)).eval x = N (a j) (b j) x := fun j => by simp [Np, N]
  have hLe : ∀ l, (Lp (μ l)).eval x = x + μ l := fun l => by simp [Lp]
  rw [sum_idx, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [Ppoly, Apoly, eval_add, eval_mul, eval_sub, eval_finsetSum, eval_prod, eval_C,
    eval_X, hNe, hLe, φ]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase univ (fun j' => N (a j') (b j') x) (mem_univ j)]
    have := hN j
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false, R, I]
    field_simp
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_prod_erase univ (fun l' => x + μ l') (mem_univ l)]
    have := hL l
    simp only [g]
    field_simp

/-- The cleared polynomial has degree `< 2r + m`. -/
lemma Ppoly_natDegree_lt (a b : Fin r → ℝ) (μ : Fin m → ℝ) (c : Idx r m → ℝ) (hd : 0 < 2 * r + m) :
    (Ppoly a b μ c).natDegree < 2 * r + m := by
  have hNp : ∀ s : Finset (Fin r), (∏ j ∈ s, Np (a j) (b j)).natDegree ≤ 2 * s.card := by
    intro s
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul s _ 2 fun j _ => ?_).trans (by simp [mul_comm])
    unfold Np; compute_degree!
  have hLp : ∀ s : Finset (Fin m), (∏ l ∈ s, Lp (μ l)).natDegree ≤ s.card := by
    intro s
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul s _ 1 fun l _ => ?_).trans (by simp)
    unfold Lp; compute_degree!
  have hA : ∀ j, (Apoly a b c j).natDegree ≤ 1 := fun j => by unfold Apoly; compute_degree!
  have hbound : (Ppoly a b μ c).natDegree ≤ 2 * r + m - 1 := by
    apply natDegree_add_le_of_degree_le
    · refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      refine (natDegree_mul_le).trans ?_
      have h1 := (natDegree_mul_le (p := Apoly a b c j)
        (q := ∏ j' ∈ univ.erase j, Np (a j') (b j'))).trans
        (add_le_add (hA j) (hNp (univ.erase j)))
      have h2 := hLp univ
      rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, Fintype.card_fin] at h1
      rw [Finset.card_univ, Fintype.card_fin] at h2
      have : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr fun h => (h ▸ j).elim0
      omega
    · refine natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
      refine (natDegree_mul_le).trans ?_
      have h1 := (natDegree_mul_le (p := C (c (Sum.inr l)))
        (q := ∏ j, Np (a j) (b j))).trans (add_le_add (natDegree_C _).le (hNp univ))
      have h2 := hLp (univ.erase l)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      rw [Finset.card_erase_of_mem (mem_univ l), Finset.card_univ, Fintype.card_fin] at h2
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => (h ▸ l).elim0
      omega
  omega

/-- The cleared polynomial vanishes only for the zero coefficient vector. -/
theorem eq_zero_of_Ppoly {a b : Fin r → ℝ} {μ : Fin m → ℝ}
    (hb : ∀ j, b j ≠ 0) (hab : Function.Injective fun j => (a j, b j ^ 2))
    (hμi : Function.Injective μ) (c : Idx r m → ℝ) (hP : Ppoly a b μ c = 0) : c = 0 := by
  -- on-line coefficients: evaluate at `−μ_l`
  have hK : ∀ l, c (Sum.inr l) = 0 := by
    intro l
    have h0 := congrArg (eval (-μ l)) hP
    have hLl : (Lp (μ l)).eval (-μ l) = 0 := by simp [Lp]
    rw [eval_zero, Ppoly, eval_add, eval_finsetSum, Finset.sum_eq_zero, zero_add, eval_finsetSum,
      Finset.sum_eq_single l] at h0
    · simp only [eval_mul, eval_prod, eval_C] at h0
      have hND : ∏ j, (Np (a j) (b j)).eval (-μ l) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j _
        have := hb j
        simp only [Np, eval_add, eval_pow, eval_X, eval_C]
        positivity
      have hLD : ∏ l' ∈ univ.erase l, (Lp (μ l')).eval (-μ l) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro l' hl'
        simp only [Lp, eval_add, eval_X, eval_C]
        intro H
        exact Finset.ne_of_mem_erase hl' (hμi (by linarith))
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 hND
      · exact absurd h1 hLD
    · intro l' _ hl'
      simp only [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hl', mem_univ l⟩) hLl, mul_zero]
    · intro H; exact absurd (mem_univ l) H
    · intro j _
      simp only [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (mem_univ l) hLl, mul_zero]
  have hP' : ∑ j, Apoly a b c j * (∏ j' ∈ univ.erase j, Np (a j') (b j')) *
      ∏ l, Lp (μ l) = 0 := by
    have := hP
    simp only [Ppoly, hK, C_0, zero_mul, Finset.sum_const_zero, add_zero] at this
    exact this
  -- quartet coefficients: evaluate at the complex root `−a_j + i b_j`
  have hA : ∀ j, c (Sum.inl (j, 0)) = 0 ∧ c (Sum.inl (j, 1)) = 0 := by
    intro j
    set z : ℂ := -(a j : ℂ) + (b j : ℂ) * Complex.I with hz
    have hNz : ∀ j', aeval z (Np (a j') (b j')) =
        ((a j' - a j : ℝ) : ℂ) ^ 2 - (b j : ℂ) ^ 2 + (b j' : ℂ) ^ 2 +
          2 * ((a j' - a j : ℝ) : ℂ) * (b j : ℂ) * Complex.I := by
      intro j'
      simp only [Np, map_add, map_pow, aeval_X, aeval_C, Complex.coe_algebraMap, hz]
      push_cast
      linear_combination (b j : ℂ) ^ 2 * Complex.I_sq
    have hNj : aeval z (Np (a j) (b j)) = 0 := by
      rw [hNz]
      simp
    have h0 := congrArg (aeval z) hP'
    rw [map_zero, map_sum, Finset.sum_eq_single j] at h0
    · simp only [map_mul, map_prod] at h0
      have hND : ∏ j' ∈ univ.erase j, aeval z (Np (a j') (b j')) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j' hj' H
        rw [hNz] at H
        have hre := congrArg Complex.re H
        have him := congrArg Complex.im H
        simp [pow_two] at hre him
        have hda : a j' = a j := by
          rcases him with h | h
          · linarith
          · exact absurd h (hb j)
        rw [hda] at hre
        exact Finset.ne_of_mem_erase hj' (hab (Prod.ext hda (by nlinarith)))
      have hLD : ∏ l, aeval z (Lp (μ l)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro l _ H
        simp only [Lp, map_add, aeval_X, aeval_C, Complex.coe_algebraMap, hz] at H
        have := congrArg Complex.im H
        simp at this
        exact hb j this
      have hAz : aeval z (Apoly a b c j) = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · exact h2
          · exact absurd h2 hND
        · exact absurd h1 hLD
      simp only [Apoly, map_sub, map_mul, map_add, aeval_X, aeval_C, Complex.coe_algebraMap,
        hz] at hAz
      have hre := congrArg Complex.re hAz
      have him := congrArg Complex.im hAz
      simp at hre him
      refine ⟨?_, ?_⟩
      · rcases him with h | h
        · exact h
        · exact absurd h (hb j)
      · rcases hre with h | h
        · exact h
        · exact absurd h (hb j)
    · intro j'' _ hj''
      simp only [map_mul, map_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hj'', mem_univ j⟩) hNj, mul_zero,
        zero_mul]
    · intro H; exact absurd (mem_univ j) H
  funext i
  rcases i with ⟨j, k⟩ | l
  · fin_cases k
    · exact (hA j).1
    · exact (hA j).2
  · exact hK l

/-- **Invertibility at any `2r + m` nodes.** If a feature combination vanishes at `2r + m` distinct
positive nodes, it is zero. (Codex: the evaluation matrix is a scaled Vandermonde matrix after a
partial-fraction change of basis.) -/
theorem features_independent_on {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j)
    (hb : ∀ j, b j ≠ 0) (hab : Function.Injective fun j => (a j, b j ^ 2)) (hμ : ∀ l, 0 < μ l)
    (hμi : Function.Injective μ) {S : Finset ℝ} (hS : ∀ x ∈ S, 0 < x) (hcard : 2 * r + m ≤ S.card)
    (c : Idx r m → ℝ) (hc : ∀ x ∈ S, ∑ i, c i * φ a b μ x i = 0) : c = 0 := by
  rcases Nat.eq_zero_or_pos (2 * r + m) with hd | hd
  · have hr : r = 0 := by omega
    have hm : m = 0 := by omega
    subst hr hm
    funext i
    rcases i with ⟨j, _⟩ | l
    · exact j.elim0
    · exact l.elim0
  refine eq_zero_of_Ppoly hb hab hμi c ?_
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun x hx => ?_)
    ((Ppoly_natDegree_lt a b μ c hd).trans_le hcard)
  rw [Ppoly_eval ha hμ c (hS x hx), hc x hx, mul_zero]

/-- **The features at any `2r + m` positive nodes span** `ℝ^{2r+m}`. -/
theorem span_top_on {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hb : ∀ j, b j ≠ 0)
    (hab : Function.Injective fun j => (a j, b j ^ 2)) (hμ : ∀ l, 0 < μ l)
    (hμi : Function.Injective μ) {S : Finset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hcard : 2 * r + m ≤ S.card) :
    Submodule.span ℝ (φ a b μ '' (S : Set ℝ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : Idx r m → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hc : ∀ x ∈ S, ∑ i, c i * φ a b μ x i = 0 := by
    intro x hx
    have hmem : φ a b μ x ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at hmem
    rw [← hmem]
    exact Finset.sum_congr rfl fun i _ => by simp [c, smul_eq_mul, mul_comm]
  have h0 := features_independent_on ha hb hab hμ hμi hS hcard c hc
  apply hf
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : c i = 0 := congrFun h0 i
  simp only [c] at this
  rw [this, smul_zero]

/-- **Every moment vector is realized** by weights supported on `S`. -/
theorem realize {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hb : ∀ j, b j ≠ 0)
    (hab : Function.Injective fun j => (a j, b j ^ 2)) (hμ : ∀ l, 0 < μ l)
    (hμi : Function.Injective μ) {S : Finset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hcard : 2 * r + m ≤ S.card) :
    ∃ e : Idx r m → ℝ → ℝ, ∀ τ : Idx r m → ℝ, ∀ k,
      ∑ x ∈ S, (∑ i, τ i * e i x) * φ a b μ x k = τ k := by
  classical
  have hspan := span_top_on ha hb hab hμ hμi hS hcard
  have hmem : ∀ i : Idx r m, (Pi.single i (1 : ℝ) : Idx r m → ℝ) ∈
      Submodule.span ℝ (φ a b μ '' (S : Set ℝ)) := fun i => hspan ▸ Submodule.mem_top
  choose l hl hle using fun i => (Finsupp.mem_span_image_iff_linearCombination ℝ).mp (hmem i)
  have hcomb : ∀ i k, ∑ x ∈ S, l i x * φ a b μ x k = (Pi.single i (1 : ℝ) : Idx r m → ℝ) k := by
    intro i k
    rw [← hle i, Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (l i) (hl i)]
    · rw [Finset.sum_apply]; rfl
    · intro x _; simp
  refine ⟨fun i x => l i x, fun τ k => ?_⟩
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcomb]
  simp [Pi.single_apply]

/-- The Loewner form of a weight with prescribed moments `τ`. -/
theorem form_of_moments (a b : Fin r → ℝ) (μ κ : Fin m → ℝ) (S : Finset ℝ) (c : ℝ → ℝ)
    (τ : Idx r m → ℝ) (hτ : ∀ k, ∑ x ∈ S, c x * φ a b μ x k = τ k) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * loewnerK a b μ κ x y =
      ∑ j, 2 * (τ (Sum.inl (j, 0)) ^ 2 - τ (Sum.inl (j, 1)) ^ 2) + ∑ l, κ l * τ (Sum.inr l) ^ 2 := by
  rw [loewner_form]
  have eR : ∀ j, ∑ x ∈ S, c x * R (a j) (b j) x = τ (Sum.inl (j, 0)) := fun j => by
    rw [← hτ]; rfl
  have eI : ∀ j, ∑ x ∈ S, c x * I (a j) (b j) x = τ (Sum.inl (j, 1)) := fun j => by
    rw [← hτ]; rfl
  have eg : ∀ l, ∑ x ∈ S, c x * g (μ l) x = τ (Sum.inr l) := fun l => by
    rw [← hτ]; rfl
  simp only [eR, eI, eg]

/-- **No finite on-line mass masks the Loewner negativity, at any `2r + m` nodes.** For `r`
off-axis quartets and any finite family of on-line pieces with arbitrary real weights `κ`, at
*every* set `S` of at least `2r + m` positive nodes there are weights `w_j` supported on `S` whose
combinations `Σ_j t_j w_j` have Loewner form `−2 Σ_j t_j²`. -/
theorem no_masking {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hb : ∀ j, b j ≠ 0)
    (hab : Function.Injective fun j => (a j, b j ^ 2)) (hμ : ∀ l, 0 < μ l)
    (hμi : Function.Injective μ) (κ : Fin m → ℝ) {S : Finset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hcard : 2 * r + m ≤ S.card) :
    ∃ w : Fin r → ℝ → ℝ, ∀ t : Fin r → ℝ,
      ∑ x ∈ S, ∑ y ∈ S, (∑ j, t j * w j x) * (∑ j, t j * w j y) * loewnerK a b μ κ x y =
        -2 * ∑ j, t j ^ 2 := by
  classical
  obtain ⟨e, he⟩ := realize ha hb hab hμ hμi hS hcard
  refine ⟨fun j => e (Sum.inl (j, 1)), fun t => ?_⟩
  set τ : Idx r m → ℝ := fun i => match i with
    | Sum.inl (j, k) => if (k : ℕ) = 1 then t j else 0
    | Sum.inr _ => 0 with hτdef
  have hsum : ∀ x, ∑ j, t j * e (Sum.inl (j, 1)) x = ∑ i, τ i * e i x := by
    intro x
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [τ]
  simp_rw [hsum]
  rw [form_of_moments a b μ κ S _ τ (he τ)]
  simp [τ, Finset.mul_sum]

/-- **The positive directions.** If the on-line weights are positive, the same nodes carry an
`(r + m)`-dimensional family on which the Loewner form is `2 Σ_j s_j² + Σ_l κ_l t_l² > 0`. With
`no_masking` and `2r + m` nodes, the Loewner matrix has inertia exactly `(r + m, r, 0)`, by a
dimension count. -/
theorem pos_family {a b : Fin r → ℝ} {μ : Fin m → ℝ} (ha : ∀ j, 0 < a j) (hb : ∀ j, b j ≠ 0)
    (hab : Function.Injective fun j => (a j, b j ^ 2)) (hμ : ∀ l, 0 < μ l)
    (hμi : Function.Injective μ) (κ : Fin m → ℝ) {S : Finset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hcard : 2 * r + m ≤ S.card) :
    ∃ wq : Fin r → ℝ → ℝ, ∃ wp : Fin m → ℝ → ℝ, ∀ (s : Fin r → ℝ) (t : Fin m → ℝ),
      ∑ x ∈ S, ∑ y ∈ S, (∑ j, s j * wq j x + ∑ l, t l * wp l x) *
          (∑ j, s j * wq j y + ∑ l, t l * wp l y) * loewnerK a b μ κ x y =
        2 * ∑ j, s j ^ 2 + ∑ l, κ l * t l ^ 2 := by
  classical
  obtain ⟨e, he⟩ := realize ha hb hab hμ hμi hS hcard
  refine ⟨fun j => e (Sum.inl (j, 0)), fun l => e (Sum.inr l), fun s t => ?_⟩
  set τ : Idx r m → ℝ := fun i => match i with
    | Sum.inl (j, k) => if (k : ℕ) = 0 then s j else 0
    | Sum.inr l => t l with hτdef
  have hsum : ∀ x, ∑ j, s j * e (Sum.inl (j, 0)) x + ∑ l, t l * e (Sum.inr l) x =
      ∑ i, τ i * e i x := by
    intro x
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [τ]
  simp_rw [hsum]
  rw [form_of_moments a b μ κ S _ τ (he τ)]
  simp [τ, Finset.mul_sum]

/-- With positive on-line weights, the positive form is strictly positive off zero. -/
theorem pos_family_pos {r m : ℕ} (κ : Fin m → ℝ) (hκ : ∀ l, 0 < κ l) (s : Fin r → ℝ)
    (t : Fin m → ℝ) (hst : s ≠ 0 ∨ t ≠ 0) : 0 < 2 * ∑ j, s j ^ 2 + ∑ l, κ l * t l ^ 2 := by
  have h1 : 0 ≤ ∑ j, s j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ ∑ l, κ l * t l ^ 2 := Finset.sum_nonneg fun l _ => by
    have := hκ l; positivity
  rcases hst with hs | ht
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
    have : 0 < ∑ j, s j ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨j, mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))⟩
    linarith
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp ht
    have : 0 < ∑ l, κ l * t l ^ 2 :=
      Finset.sum_pos' (fun l _ => by have := hκ l; positivity)
        ⟨l, mem_univ _, mul_pos (hκ l) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hl)))⟩
    linarith

end GppNoGo.FiniteLoewnerNoMasking
