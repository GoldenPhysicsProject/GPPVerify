import GppVerify.NoGo.FiniteNoMasking
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# No finite on-line mass can mask any of `r` off-axis quartets

Source: Codex, directive C6 answer (GPP-bridge PR #11 comment 6121060807; full proof in
`work/codex/2026-10-12_completed_positivity_c3_c6_higgs_controls.md`). This generalizes
`GppNoGo.FiniteNoMasking` (one quartet, #296) to `r` distinct off-axis quartets.

Setup: quartets `(h_j, w_j)` with `h_j, w_j > 0`, pairwise distinct; on-line pairs at distinct heights
`γ_l ≠ 0`. The total Pick kernel is the sum of the quartet kernels `K_{h_j,w_j}` and the pair kernels.

**Theorem (`no_masking_multi`).** At some finite set of positive real nodes the total Pick form is
strictly negative on a `2r`-dimensional family of weights, parametrized by `(α_j, β_j)_j ≠ 0`. So the
negative index is `≥ 2r`, and no finite on-line mass masks any of the quartets.

**Proof.**
* `pick_eq_multi`: the form is `Σ_j 4·Q_j(quartet-j moments) + Σ_l 2(γ_l² m₀² + m₁²)`.
* `features_independent_multi`: the features `x^k/D_j(x)` (`k < 4`) and `x^i/E_l(x)` (`i < 2`) are
  linearly independent on `(0,∞)`. Clear denominators, so the polynomial vanishes identically.
  * Evaluating at `iγ_l` kills the `l`-th pair coefficients, since `D_j(iγ_l) = (h_j−γ_l²)² + w_j ≠ 0`.
  * Evaluating at each of the four distinct complex roots of `D_j` (`z² = −h_j ± i√w_j`) shows that
    the cubic quartet numerator `A_j` has four roots, hence `A_j = 0`. Here `D_{j'}(z) ≠ 0` for
    `j' ≠ j` because the quartets are distinct, and `E_l(z) ≠ 0` because `Im z² = ±√w_j ≠ 0`.
* `span_top_multi` → `no_masking_multi`: realize each quartet's negative plane independently, with
  every other moment zero.

**Scope.** This is the lower bound `≥ 2r`. Codex's exact inertia `(2r+2m, 2r)` also needs Sylvester's
law, which is not formalized here. Everything is finite: in the full infinite sum over ξ's zeros,
masking is the Weil-positivity question itself. **No RH claim.**
-/

namespace GppNoGo.FiniteNoMaskingMulti

open GppNoGo.QuartetThreeNode GppNoGo.QuartetSignature GppNoGo.FiniteNoMasking Finset Polynomial

variable {r m : ℕ}

/-- Total Pick kernel: `r` quartets plus `m` on-line pairs. -/
noncomputable def KtotR (h w : Fin r → ℝ) (γ : Fin m → ℝ) (x y : ℝ) : ℝ :=
  ∑ j, K (h j) (w j) x y + ∑ l, (fPair (γ l) x + fPair (γ l) y) / (x + y)

/-- It is the Pick kernel of the total response `Σ_j f_j + Σ_l 2x/(x²+γ_l²)`. -/
lemma KtotR_eq (h w : Fin r → ℝ) (γ : Fin m → ℝ) (x y : ℝ) :
    KtotR h w γ x y = ((∑ j, f (h j) (w j) x + ∑ l, fPair (γ l) x) +
      (∑ j, f (h j) (w j) y + ∑ l, fPair (γ l) y)) / (x + y) := by
  unfold KtotR K
  rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Feature index. -/
abbrev IdxR (r m : ℕ) := (Fin r × Fin 4) ⊕ (Fin m × Fin 2)

/-- Feature vector. -/
noncomputable def φR (h w : Fin r → ℝ) (γ : Fin m → ℝ) (x : ℝ) : IdxR r m → ℝ
  | Sum.inl (j, k) => x ^ (k : ℕ) / D (h j) (w j) x
  | Sum.inr (l, i) => x ^ (i : ℕ) / E (γ l) x

/-- **The Pick form through the feature vector.** -/
theorem pick_eq_multi {h w : Fin r → ℝ} (hh : ∀ j, 0 < h j) (hw : ∀ j, 0 ≤ w j)
    (γ : Fin m → ℝ) (S : Finset ℝ) (hS : ∀ x ∈ S, 0 < x) (c : ℝ → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * KtotR h w γ x y =
      ∑ j, 4 * Q (h j) (w j) (∑ x ∈ S, c x * φR h w γ x (Sum.inl (j, 0)))
          (∑ x ∈ S, c x * φR h w γ x (Sum.inl (j, 1)))
          (∑ x ∈ S, c x * φR h w γ x (Sum.inl (j, 2)))
          (∑ x ∈ S, c x * φR h w γ x (Sum.inl (j, 3)))
        + ∑ l, 2 * (γ l ^ 2 * (∑ x ∈ S, c x * φR h w γ x (Sum.inr (l, 0))) ^ 2
            + (∑ x ∈ S, c x * φR h w γ x (Sum.inr (l, 1))) ^ 2) := by
  have hexp : ∀ x y, c x * c y * KtotR h w γ x y =
      ∑ j : Fin r, c x * c y * K (h j) (w j) x y +
        ∑ l : Fin m, c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)) := by
    intro x y; unfold KtotR; rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hexp, Finset.sum_add_distrib]
  have hswap : ∀ {ι : Type} [Fintype ι] (F : ι → ℝ → ℝ → ℝ),
      ∑ x ∈ S, ∑ y ∈ S, ∑ i : ι, F i x y = ∑ i : ι, ∑ x ∈ S, ∑ y ∈ S, F i x y := by
    intro ι _ F
    calc _ = ∑ x ∈ S, ∑ i : ι, ∑ y ∈ S, F i x y :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap (fun j x y => c x * c y * K (h j) (w j) x y),
    hswap (fun l x y => c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)))]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [quartet_part (hh j) (hw j) S hS c]
    congr 1
    simp only [φR]
    congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> simp <;> ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [pair_part (γ l) S hS c]
    have e0 : ∑ x ∈ S, c x * φR h w γ x (Sum.inr (l, 0)) = ∑ x ∈ S, c x / E (γ l) x :=
      Finset.sum_congr rfl fun x _ => by simp [φR]; ring
    have e1 : ∑ x ∈ S, c x * φR h w γ x (Sum.inr (l, 1)) = ∑ x ∈ S, c x * x / E (γ l) x :=
      Finset.sum_congr rfl fun x _ => by simp [φR]; ring
    rw [e0, e1]

/-- Quartet numerators `A_j = Σ_k a_{j,k} X^k` and pair numerators `B_l = b_l + c_l X`. -/
noncomputable def ApolyR (a : IdxR r m → ℝ) (j : Fin r) : ℝ[X] :=
  ∑ k : Fin 4, C (a (Sum.inl (j, k))) * X ^ (k : ℕ)
noncomputable def BpolyR (a : IdxR r m → ℝ) (l : Fin m) : ℝ[X] :=
  C (a (Sum.inr (l, 0))) + C (a (Sum.inr (l, 1))) * X

/-- The cleared-denominator polynomial. -/
noncomputable def PpolyR (h w : Fin r → ℝ) (γ : Fin m → ℝ) (a : IdxR r m → ℝ) : ℝ[X] :=
  ∑ j, ApolyR a j * (∏ j' ∈ univ.erase j, Dp (h j') (w j')) * ∏ l, Ep (γ l) +
    ∑ l, BpolyR a l * (∏ j, Dp (h j) (w j)) * ∏ l' ∈ univ.erase l, Ep (γ l')

lemma sum_idxR (a v : IdxR r m → ℝ) :
    ∑ i, a i * v i = ∑ j : Fin r, ∑ k : Fin 4, a (Sum.inl (j, k)) * v (Sum.inl (j, k)) +
      ∑ l : Fin m, (a (Sum.inr (l, 0)) * v (Sum.inr (l, 0)) +
        a (Sum.inr (l, 1)) * v (Sum.inr (l, 1))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_congr rfl fun l _ => Fin.sum_univ_two _

lemma PpolyR_eval {h w : Fin r → ℝ} (hh : ∀ j, 0 < h j) (hw : ∀ j, 0 ≤ w j) (γ : Fin m → ℝ)
    (a : IdxR r m → ℝ) {x : ℝ} (hx : 0 < x) :
    (PpolyR h w γ a).eval x =
      ((∏ j, D (h j) (w j) x) * ∏ l, E (γ l) x) * ∑ i, a i * φR h w γ x i := by
  have hD : ∀ j, D (h j) (w j) x ≠ 0 := fun j => (D_pos (hh j) (hw j)).ne'
  have hE : ∀ l, E (γ l) x ≠ 0 := fun l => (E_pos (γ l) hx).ne'
  rw [sum_idxR, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [PpolyR, ApolyR, BpolyR, eval_add, eval_mul, eval_finsetSum, eval_prod, eval_C,
    eval_pow, eval_X, Dp_eval, Ep_eval, φR]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase univ (fun j' => D (h j') (w j') x) (mem_univ j), Finset.sum_mul,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hD j
    field_simp
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_prod_erase univ (fun l' => E (γ l') x) (mem_univ l)]
    have := hE l
    field_simp
    norm_num
    ring

lemma Dp_aeval (h w : ℝ) (z : ℂ) : aeval z (Dp h w) = (z ^ 2 + h) ^ 2 + w := by simp [Dp]
lemma Ep_aeval (γ : ℝ) (z : ℂ) : aeval z (Ep γ) = z ^ 2 + γ ^ 2 := by simp [Ep]

section roots

variable {h w σ : ℝ} {z : ℂ}

/-- A root of `D_{h,w}`: `z² = −h + σ√w·i` with `σ = ±1`. -/
lemma Dp_aeval_root (hw : 0 ≤ w) (hσ : σ ^ 2 = 1)
    (hz : z ^ 2 = ((-h : ℝ) : ℂ) + ((σ * Real.sqrt w : ℝ) : ℂ) * Complex.I) :
    aeval z (Dp h w) = 0 := by
  rw [Dp_aeval, hz]
  have hs : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
  apply Complex.ext
  all_goals simp [pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [hs, hσ]

/-- Other quartets do not vanish there. -/
lemma Dp_aeval_other {h' w' : ℝ} (hw : 0 < w) (hσ : σ ^ 2 = 1)
    (hz : z ^ 2 = ((-h : ℝ) : ℂ) + ((σ * Real.sqrt w : ℝ) : ℂ) * Complex.I)
    (hne : (h', w') ≠ (h, w)) : aeval z (Dp h' w') ≠ 0 := by
  rw [Dp_aeval, hz]
  intro H
  have hs : (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw.le
  have hsp : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hre := congrArg Complex.re H
  have him := congrArg Complex.im H
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  -- imaginary part forces h' = h, real part then forces w' = w
  have hh : h' = h := by
    have : (-h + h') * (σ * Real.sqrt w) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 (mul_ne_zero hσ0 hsp.ne')
  subst hh
  apply hne
  have : w' = w := by nlinarith [hs, hσ]
  rw [this]

/-- Pair denominators do not vanish there. -/
lemma Ep_aeval_ne (hw : 0 < w) (hσ : σ ^ 2 = 1)
    (hz : z ^ 2 = ((-h : ℝ) : ℂ) + ((σ * Real.sqrt w : ℝ) : ℂ) * Complex.I) (γ : ℝ) :
    aeval z (Ep γ) ≠ 0 := by
  rw [Ep_aeval, hz]
  intro H
  have him := congrArg Complex.im H
  have hγ : ((γ : ℂ) ^ 2).im = 0 := by simp [pow_two]
  simp only [Complex.add_im, hγ, add_zero] at him
  simp at him
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  rcases him with h0 | h0
  · exact hσ0 h0
  · exact (Real.sqrt_pos.mpr hw).ne' h0

/-- A real polynomial of degree `≤ 3` vanishing at every complex square root of `−h ± i√w` is zero. -/
lemma eq_zero_of_roots {A : ℝ[X]} (hA : A.natDegree ≤ 3) (hw : 0 < w)
    (hroot : ∀ (σ : ℝ) (z : ℂ), σ ^ 2 = 1 →
      z ^ 2 = ((-h : ℝ) : ℂ) + ((σ * Real.sqrt w : ℝ) : ℂ) * Complex.I → aeval z A = 0) :
    A = 0 := by
  have hsp : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  obtain ⟨z₁, hz₁⟩ := IsAlgClosed.exists_eq_mul_self
    (((-h : ℝ) : ℂ) + ((1 * Real.sqrt w : ℝ) : ℂ) * Complex.I)
  obtain ⟨z₂, hz₂⟩ := IsAlgClosed.exists_eq_mul_self
    (((-h : ℝ) : ℂ) + ((-1 * Real.sqrt w : ℝ) : ℂ) * Complex.I)
  rw [← pow_two] at hz₁ hz₂
  have hz₁0 : z₁ ≠ 0 := by
    rintro rfl
    have := congrArg Complex.im hz₁
    simp at this
    exact hsp.ne' this
  have hz₂0 : z₂ ≠ 0 := by
    rintro rfl
    have := congrArg Complex.im hz₂
    simp at this
    exact hsp.ne' this
  have hsq : z₁ ^ 2 ≠ z₂ ^ 2 := by
    rw [← hz₁, ← hz₂]
    intro H
    have := congrArg Complex.im H
    simp at this
    linarith
  have h12 : z₁ ≠ z₂ := fun H => hsq (by rw [H])
  have h12' : z₁ ≠ -z₂ := fun H => hsq (by rw [H, neg_sq])
  let f : Fin 4 → ℂ := ![z₁, -z₁, z₂, -z₂]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first
      | exact hz₁0 hij | exact hz₂0 hij | exact h12 hij | exact h12' hij
      | exact h12 hij.symm | exact h12' hij.symm | exact hz₁0 (by linear_combination hij / 2)
      | exact hz₂0 (by linear_combination hij / 2) | exact hz₁0 (by linear_combination -hij / 2)
      | exact hz₂0 (by linear_combination -hij / 2) | exact h12 (by linear_combination -hij)
      | exact h12' (by linear_combination -hij) | exact h12' (by linear_combination hij)
  have hmap : A.map (algebraMap ℝ ℂ) = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf (fun i => ?_) ?_
    · rw [eval_map_algebraMap]
      fin_cases i
      · exact hroot 1 z₁ (by norm_num) hz₁.symm
      · exact hroot 1 (-z₁) (by norm_num) (by rw [neg_sq]; exact hz₁.symm)
      · exact hroot (-1) z₂ (by norm_num) hz₂.symm
      · exact hroot (-1) (-z₂) (by norm_num) (by rw [neg_sq]; exact hz₂.symm)
    · simp only [Fintype.card_fin]
      exact (natDegree_map_le).trans_lt (by omega)
  exact (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp hmap

end roots

lemma ApolyR_natDegree (a : IdxR r m → ℝ) (j : Fin r) : (ApolyR a j).natDegree ≤ 3 :=
  natDegree_sum_le_of_forall_le _ _ fun k _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := k.isLt; omega)

/-- **Linear independence of the features** on `(0, ∞)`, for `r` distinct off-axis quartets and
`m` on-line pairs at distinct nonzero heights. -/
theorem features_independent_multi {h w : Fin r → ℝ} (hh : ∀ j, 0 < h j) (hw : ∀ j, 0 < w j)
    (hhw : Function.Injective fun j => (h j, w j)) (γ : Fin m → ℝ) (hγ : ∀ l, γ l ≠ 0)
    (hinj : Function.Injective fun l => γ l ^ 2) (a : IdxR r m → ℝ)
    (ha : ∀ x, 0 < x → ∑ i, a i * φR h w γ x i = 0) : a = 0 := by
  -- the cleared polynomial vanishes on (0, ∞), hence identically
  have hP : PpolyR h w γ a = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => ?_) (Set.Ioi_infinite 0)
    show IsRoot _ x
    rw [IsRoot, PpolyR_eval hh (fun j => (hw j).le) γ a hx, ha x hx, mul_zero]
  -- pair coefficients: evaluate at iγ_l
  have hB : ∀ l, a (Sum.inr (l, 0)) = 0 ∧ a (Sum.inr (l, 1)) = 0 := by
    intro l
    set z : ℂ := (γ l : ℂ) * Complex.I with hz
    have hEz : ∀ l', aeval z (Ep (γ l')) = ((γ l' ^ 2 - γ l ^ 2 : ℝ) : ℂ) := by
      intro l'; simp [Ep, hz, mul_pow, Complex.I_sq]; ring
    have hEl : aeval z (Ep (γ l)) = 0 := by rw [hEz]; simp
    have hDz : ∀ j, aeval z (Dp (h j) (w j)) = (((h j - γ l ^ 2) ^ 2 + w j : ℝ) : ℂ) := by
      intro j; simp [Dp, hz, mul_pow, Complex.I_sq]; ring
    have h0 := congrArg (aeval z) hP
    rw [map_zero, PpolyR, map_add, map_sum, Finset.sum_eq_zero, zero_add, map_sum,
      Finset.sum_eq_single l] at h0
    · simp only [map_mul, map_prod] at h0
      have hprodE : ∏ l' ∈ univ.erase l, aeval z (Ep (γ l')) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro l' hl'
        rw [hEz]
        have hne : l' ≠ l := Finset.ne_of_mem_erase hl'
        have : γ l' ^ 2 - γ l ^ 2 ≠ 0 := sub_ne_zero.mpr fun h => hne (hinj h)
        exact_mod_cast this
      have hprodD : ∏ j, aeval z (Dp (h j) (w j)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j _
        rw [hDz]
        have := hw j
        exact_mod_cast (by positivity : (h j - γ l ^ 2) ^ 2 + w j ≠ 0)
      have hBz : aeval z (BpolyR a l) = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · exact h2
          · exact absurd h2 hprodD
        · exact absurd h1 hprodE
      simp only [BpolyR, map_add, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap] at hBz
      have hre := congrArg Complex.re hBz
      have him := congrArg Complex.im hBz
      simp [hz] at hre him
      exact ⟨hre, by
        rcases him with h | h
        · exact h
        · exact absurd h (hγ l)⟩
    · intro l' _ hl'
      simp only [map_mul, map_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hl', mem_univ l⟩) hEl, mul_zero]
    · intro H; exact absurd (mem_univ l) H
    · intro j _
      simp only [map_mul, map_prod]
      rw [Finset.prod_eq_zero (mem_univ l) hEl, mul_zero]
  have hBpoly : ∀ l, BpolyR a l = 0 := fun l => by simp [BpolyR, (hB l).1, (hB l).2]
  have hP' : ∑ j, ApolyR a j * (∏ j' ∈ univ.erase j, Dp (h j') (w j')) * ∏ l, Ep (γ l) = 0 := by
    have := hP
    simp only [PpolyR, hBpoly, zero_mul, Finset.sum_const_zero, add_zero] at this
    exact this
  -- quartet coefficients: evaluate at the four complex roots of each `D_j`
  have hA : ∀ j, ApolyR a j = 0 := by
    intro j
    refine eq_zero_of_roots (h := h j) (ApolyR_natDegree a j) (hw j) fun σ z hσ hz => ?_
    have h0 := congrArg (aeval z) hP'
    rw [map_zero, map_sum, Finset.sum_eq_single j] at h0
    · simp only [map_mul, map_prod] at h0
      have hprodD : ∏ j' ∈ univ.erase j, aeval z (Dp (h j') (w j')) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j' hj'
        exact Dp_aeval_other (hw j) hσ hz fun H => Finset.ne_of_mem_erase hj' (hhw H)
      have hprodE : ∏ l, aeval z (Ep (γ l)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro l _
        exact Ep_aeval_ne (hw j) hσ hz _
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 hprodD
      · exact absurd h1 hprodE
    · intro j'' _ hj''
      simp only [map_mul, map_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hj'', mem_univ j⟩)
        (Dp_aeval_root (hw j).le hσ hz), mul_zero, zero_mul]
    · intro H; exact absurd (mem_univ j) H
  funext i
  rcases i with ⟨j, k⟩ | ⟨l, i⟩
  · have := congrArg (fun p => coeff p (k : ℕ)) (hA j)
    simp only [ApolyR, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single k] at this
    · simpa using this
    · intro k' _ hk'; rw [if_neg (fun h => hk' (Fin.ext h).symm), mul_zero]
    · simp
  · fin_cases i
    · exact (hB l).1
    · exact (hB l).2

/-- **The features span** `ℝ^{4r+2m}` as `x` ranges over `(0, ∞)`. -/
theorem span_top_multi {h w : Fin r → ℝ} (hh : ∀ j, 0 < h j) (hw : ∀ j, 0 < w j)
    (hhw : Function.Injective fun j => (h j, w j)) (γ : Fin m → ℝ) (hγ : ∀ l, γ l ≠ 0)
    (hinj : Function.Injective fun l => γ l ^ 2) :
    Submodule.span ℝ (φR h w γ '' Set.Ioi 0) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set a : IdxR r m → ℝ := fun i => f fun j => if i = j then 1 else 0
  have ha : ∀ x, 0 < x → ∑ i, a i * φR h w γ x i = 0 := by
    intro x hx
    have hmem : φR h w γ x ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at hmem
    rw [← hmem]
    exact Finset.sum_congr rfl fun i _ => by simp [a, smul_eq_mul, mul_comm]
  have h0 := features_independent_multi hh hw hhw γ hγ hinj a ha
  apply hf
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a i = 0 := congrFun h0 i
  simp only [a] at this
  rw [this, smul_zero]

/-- The negative-plane target: on quartet `j` the moments `(α_j, β_j, −(h_j²+w_j)/h_j·α_j, −h_j β_j)`,
and every pair moment zero. It is linear and injective in `(α, β)`. -/
noncomputable def target (h w α β : Fin r → ℝ) : IdxR r m → ℝ
  | Sum.inl (j, k) => ![α j, β j, -(h j ^ 2 + w j) / h j * α j, -h j * β j] k
  | Sum.inr _ => 0

/-- **No masking, `r` quartets.** At some finite set of positive real nodes, with fixed weight
functions `c_i`, the total Pick form is strictly negative on the weights
`Σ_i target(α, β)_i · c_i` for every `(α, β) ∈ ℝ^r × ℝ^r` that is not zero. That is a
`2r`-dimensional negative family. -/
theorem no_masking_multi {h w : Fin r → ℝ} (hh : ∀ j, 0 < h j) (hw : ∀ j, 0 < w j)
    (hhw : Function.Injective fun j => (h j, w j)) (γ : Fin m → ℝ) (hγ : ∀ l, γ l ≠ 0)
    (hinj : Function.Injective fun l => γ l ^ 2) :
    ∃ S : Finset ℝ, (∀ x ∈ S, 0 < x) ∧ ∃ c : IdxR r m → ℝ → ℝ, ∀ α β : Fin r → ℝ,
      (∃ j, α j ≠ 0 ∨ β j ≠ 0) →
      ∑ x ∈ S, ∑ y ∈ S, (∑ i, target h w α β i * c i x) * (∑ i, target h w α β i * c i y) *
        KtotR h w γ x y < 0 := by
  classical
  have hspan := span_top_multi hh hw hhw γ hγ hinj
  have hmem : ∀ i : IdxR r m, Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (φR h w γ '' Set.Ioi 0) :=
    fun i => hspan ▸ Submodule.mem_top
  choose l hl hle using fun i => (Finsupp.mem_span_image_iff_linearCombination ℝ).mp (hmem i)
  set S := univ.biUnion fun i => (l i).support
  have hS : ∀ x ∈ S, 0 < x := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hl i hi
  -- each `l i` realizes the `i`-th basis vector over `S`
  have hcomb : ∀ i k, ∑ x ∈ S, l i x * φR h w γ x k = (Pi.single i (1 : ℝ) : IdxR r m → ℝ) k := by
    intro i k
    rw [← hle i, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset (l i) 
      (fun x hx => Finset.subset_biUnion_of_mem (fun i => (l i).support) (mem_univ i) hx)]
    · rw [Finset.sum_apply]; rfl
    · intro x _; simp
  have hmom : ∀ (t : IdxR r m → ℝ) k,
      ∑ x ∈ S, (fun x => ∑ i, t i * l i x) x * φR h w γ x k = t k := by
    intro t k
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcomb]
    simp [Pi.single_apply]
  refine ⟨S, hS, fun i x => l i x, fun α β hαβ => ?_⟩
  rw [pick_eq_multi hh (fun j => (hw j).le) γ S hS (fun x => ∑ i, target h w α β i * l i x)]
  simp only [hmom]
  have t0 : ∀ j, target (m := m) h w α β (Sum.inl (j, 0)) = α j := fun _ => rfl
  have t1 : ∀ j, target (m := m) h w α β (Sum.inl (j, 1)) = β j := fun _ => rfl
  have t2 : ∀ j, target (m := m) h w α β (Sum.inl (j, 2)) = -(h j ^ 2 + w j) / h j * α j :=
    fun _ => rfl
  have t3 : ∀ j, target (m := m) h w α β (Sum.inl (j, 3)) = -h j * β j := fun _ => rfl
  have tr : ∀ q, target (m := m) h w α β (Sum.inr q) = 0 := fun _ => rfl
  simp only [t0, t1, t2, t3, tr]
  have hpair : ∑ l : Fin m, 2 * (γ l ^ 2 * (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 := by simp
  rw [hpair, add_zero]
  obtain ⟨j₀, hj₀⟩ := hαβ
  calc ∑ j, 4 * Q (h j) (w j) (α j) (β j) (-(h j ^ 2 + w j) / h j * α j) (-h j * β j)
      < ∑ _j : Fin r, (0 : ℝ) := by
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, mem_univ _, ?_⟩
        · by_cases hj : α j ≠ 0 ∨ β j ≠ 0
          · have := Q_neg_plane (hh j) (hw j) _ _ hj
            linarith
          · simp only [not_or, not_not] at hj
            rw [hj.1, hj.2]
            simp [Q]
        · have := Q_neg_plane (hh j₀) (hw j₀) _ _ hj₀
          linarith
    _ = 0 := by simp

end GppNoGo.FiniteNoMaskingMulti
