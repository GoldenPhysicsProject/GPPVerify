import GppVerify.NoGo.QuartetFourNode
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-!
# No finite on-line mass can mask an off-axis quartet

Source: Codex, 2026-10-11 (GPP-bridge `work/codex/2026-10-11_pick_real_node_resolvent_lean.md`, §K;
PR #11). The question left open in the No-Go ledger was whether positive on-line mass could
hide an off-axis quartet's negative directions in the real-node Pick form.

The setup is one off-axis quartet with folded response `f = 4x(x²+h)/D(x)` (`h, w > 0`;
`GppNoGo.QuartetThreeNode`). Add **any** finite family of on-line zero pairs at distinct heights
`γ_l ≠ 0`, each with response `2x/(x² + γ_l²)`. The Pick kernel of the sum is
`K(x,y) = (F(x)+F(y))/(x+y)`, where `F` is the total response.

**Theorem (`no_masking`).** There is a finite set of positive real nodes and a two-dimensional
family of weights on which the total Pick form is **strictly negative**. So finitely many on-line
pairs never mask an off-axis quartet. The negative index stays `≥ 2`.

**Proof.**
* `pick_eq`: the Pick form factors through a feature vector
  `φ(x) = (x^k/D(x))_{k<4} ⊕ (1/E_l(x), x/E_l(x))_l` with `E_l = x² + γ_l²`. It equals
  `4·Q(quartet moments) + Σ_l 2(γ_l² m₀² + m₁²)`, using `GppNoGo.QuartetSignature.Q` and
  each pair's kernel `2(xy + γ²)/(E(x)E(y))`.
* `features_independent`: the features are linearly independent on `(0,∞)`. Clear denominators
  and get a polynomial `P` vanishing on `(0,∞)`, so `P = 0`. Evaluate at the **complex** point
  `iγ_l`. Every term except the `l`-th pair contains the factor `E_l(iγ_l) = 0`, and
  `D(iγ_l) = (h−γ_l²)² + w ≠ 0`, so the `l`-th pair coefficients vanish. Then `A·∏E = 0`
  forces the quartet coefficients to vanish.
* `span_top`: hence the features span. So some finite positive node set realizes the quartet
  moments of `Q`'s negative plane (`Q_neg_plane`) with **all pair moments zero**. The pair terms
  then contribute nothing, and the form is `4Q < 0`.

**Scope and hint.** This is finite, and it covers one quartet. Codex's full statement (`r` quartets
+ `m` pairs ⇒ inertia exactly `(2r+2m, 2r)`) also needs the analogous independence across
quartets and Sylvester's law. It is not formalized here. In the infinite sum over ξ's zeros the
on-line mass is infinite, and the moment-zeroing step needs infinitely many constraints. That is
exactly where Weil positivity (RH) lives. **No RH claim.**
-/

namespace GppNoGo.FiniteNoMasking

open GppNoGo.QuartetThreeNode GppNoGo.QuartetSignature Finset Polynomial

variable {m : ℕ}

/-- `E_γ(x) = x² + γ²`, the denominator of an on-line pair at height `γ`. -/
noncomputable def E (γ x : ℝ) : ℝ := x ^ 2 + γ ^ 2

/-- Response of an on-line pair: `2x/(x²+γ²)`. -/
noncomputable def fPair (γ x : ℝ) : ℝ := 2 * x / E γ x

/-- Total response: one off-axis quartet plus `m` on-line pairs. -/
noncomputable def F (h w : ℝ) (γ : Fin m → ℝ) (x : ℝ) : ℝ := f h w x + ∑ l, fPair (γ l) x

/-- Total Pick kernel. -/
noncomputable def Ktot (h w : ℝ) (γ : Fin m → ℝ) (x y : ℝ) : ℝ :=
  (F h w γ x + F h w γ y) / (x + y)

/-- Feature index: four quartet moments, two moments per pair. -/
abbrev Idx (m : ℕ) := Fin 4 ⊕ (Fin m × Fin 2)

/-- Feature vector. -/
noncomputable def φ (h w : ℝ) (γ : Fin m → ℝ) (x : ℝ) : Idx m → ℝ
  | Sum.inl k => x ^ (k : ℕ) / D h w x
  | Sum.inr (l, j) => x ^ (j : ℕ) / E (γ l) x

lemma E_pos (γ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < E γ x := by unfold E; positivity

/-- The on-line pair kernel. -/
lemma pair_kernel (γ : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (fPair γ x + fPair γ y) / (x + y) = 2 * (x * y + γ ^ 2) / (E γ x * E γ y) := by
  have h1 := (E_pos γ hx).ne'
  have h2 := (E_pos γ hy).ne'
  have h3 : x + y ≠ 0 := by positivity
  unfold fPair
  unfold E at h1 h2 ⊢
  field_simp
  ring

lemma Ktot_split (h w : ℝ) (γ : Fin m → ℝ) (x y : ℝ) :
    Ktot h w γ x y = K h w x y + ∑ l, (fPair (γ l) x + fPair (γ l) y) / (x + y) := by
  unfold Ktot F K
  rw [← Finset.sum_div, ← add_div, Finset.sum_add_distrib]
  ring

/-- Quartet part of the Pick form. -/
lemma quartet_part {h w : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (S : Finset ℝ) (hS : ∀ x ∈ S, 0 < x)
    (c : ℝ → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * K h w x y =
      4 * Q h w (∑ x ∈ S, c x / D h w x) (∑ x ∈ S, c x / D h w x * x)
        (∑ x ∈ S, c x / D h w x * x ^ 2) (∑ x ∈ S, c x / D h w x * x ^ 3) := by
  have hk : ∀ x ∈ S, ∀ y ∈ S, c x * c y * K h w x y =
      4 * ((c x / D h w x) * (c y / D h w y) * N h w x y) := by
    intro x hx y hy
    rw [K_eq hh hw (hS x hx) (hS y hy)]
    have hDx := (D_pos (x := x) hh hw).ne'
    have hDy := (D_pos (x := y) hh hw).ne'
    field_simp
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hk x hx y hy]
  simp_rw [← Finset.mul_sum]
  congr 1
  exact sum_N_eq_Q S (fun z => c z / D h w z) (fun z => z) h w

/-- One on-line pair's part of the Pick form: `2(γ² m₀² + m₁²) ≥ 0`. -/
lemma pair_part (γ : ℝ) (S : Finset ℝ) (hS : ∀ x ∈ S, 0 < x) (c : ℝ → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * ((fPair γ x + fPair γ y) / (x + y)) =
      2 * (γ ^ 2 * (∑ x ∈ S, c x / E γ x) ^ 2 + (∑ x ∈ S, c x * x / E γ x) ^ 2) := by
  have hk : ∀ x ∈ S, ∀ y ∈ S, c x * c y * ((fPair γ x + fPair γ y) / (x + y)) =
      2 * (γ ^ 2 * ((c x / E γ x) * (c y / E γ y)) + (c x * x / E γ x) * (c y * y / E γ y)) := by
    intro x hx y hy
    rw [pair_kernel γ (hS x hx) (hS y hy)]
    have h1 := (E_pos γ (hS x hx)).ne'
    have h2 := (E_pos γ (hS y hy)).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hk x hx y hy]
  rw [sq (∑ x ∈ S, c x / E γ x), sq (∑ x ∈ S, c x * x / E γ x), prod_sums, prod_sums,
    Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-- **The Pick form through the feature vector.** -/
theorem pick_eq {h w : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (γ : Fin m → ℝ) (S : Finset ℝ)
    (hS : ∀ x ∈ S, 0 < x) (c : ℝ → ℝ) :
    ∑ x ∈ S, ∑ y ∈ S, c x * c y * Ktot h w γ x y =
      4 * Q h w (∑ x ∈ S, c x * φ h w γ x (Sum.inl 0)) (∑ x ∈ S, c x * φ h w γ x (Sum.inl 1))
          (∑ x ∈ S, c x * φ h w γ x (Sum.inl 2)) (∑ x ∈ S, c x * φ h w γ x (Sum.inl 3))
        + ∑ l, 2 * (γ l ^ 2 * (∑ x ∈ S, c x * φ h w γ x (Sum.inr (l, 0))) ^ 2
            + (∑ x ∈ S, c x * φ h w γ x (Sum.inr (l, 1))) ^ 2) := by
  have hexp : ∀ x y, c x * c y * Ktot h w γ x y = c x * c y * K h w x y +
      ∑ l : Fin m, c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)) := by
    intro x y; rw [Ktot_split, mul_add, Finset.mul_sum]
  simp_rw [hexp, Finset.sum_add_distrib]
  rw [quartet_part hh hw S hS c]
  have hswap : ∑ x ∈ S, ∑ y ∈ S, ∑ l : Fin m, c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)) =
      ∑ l : Fin m, ∑ x ∈ S, ∑ y ∈ S, c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)) := by
    calc _ = ∑ x ∈ S, ∑ l : Fin m, ∑ y ∈ S,
          c x * c y * ((fPair (γ l) x + fPair (γ l) y) / (x + y)) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  congr 1
  · congr 1
    simp only [φ]
    congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> simp <;> ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [pair_part (γ l) S hS c]
    have e0 : ∑ x ∈ S, c x * φ h w γ x (Sum.inr (l, 0)) = ∑ x ∈ S, c x / E (γ l) x :=
      Finset.sum_congr rfl fun x _ => by simp [φ]; ring
    have e1 : ∑ x ∈ S, c x * φ h w γ x (Sum.inr (l, 1)) = ∑ x ∈ S, c x * x / E (γ l) x :=
      Finset.sum_congr rfl fun x _ => by simp [φ]; ring
    rw [e0, e1]

/-- Polynomial denominators. -/
noncomputable def Dp (h w : ℝ) : ℝ[X] := (X ^ 2 + C h) ^ 2 + C w
noncomputable def Ep (γ : ℝ) : ℝ[X] := X ^ 2 + C (γ ^ 2)

lemma Dp_eval (h w x : ℝ) : (Dp h w).eval x = D h w x := by simp [Dp, D]
lemma Ep_eval (γ x : ℝ) : (Ep γ).eval x = E γ x := by simp [Ep, E]

/-- The quartet numerator `A = Σ_k a_k X^k` and the pair numerators `B_l = b_l + c_l X`. -/
noncomputable def Apoly (a : Idx m → ℝ) : ℝ[X] := ∑ k : Fin 4, C (a (Sum.inl k)) * X ^ (k : ℕ)
noncomputable def Bpoly (a : Idx m → ℝ) (l : Fin m) : ℝ[X] :=
  C (a (Sum.inr (l, 0))) + C (a (Sum.inr (l, 1))) * X

/-- The cleared-denominator polynomial. -/
noncomputable def Ppoly (h w : ℝ) (γ : Fin m → ℝ) (a : Idx m → ℝ) : ℝ[X] :=
  Apoly a * ∏ l, Ep (γ l) + ∑ l, Bpoly a l * Dp h w * ∏ l' ∈ univ.erase l, Ep (γ l')

lemma sum_idx (a : Idx m → ℝ) (v : Idx m → ℝ) :
    ∑ i, a i * v i = ∑ k : Fin 4, a (Sum.inl k) * v (Sum.inl k) +
      ∑ l : Fin m, (a (Sum.inr (l, 0)) * v (Sum.inr (l, 0)) +
        a (Sum.inr (l, 1)) * v (Sum.inr (l, 1))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_congr rfl fun l _ => Fin.sum_univ_two _

lemma Ppoly_eval {h w : ℝ} (hh : 0 < h) (hw : 0 ≤ w) (γ : Fin m → ℝ) (a : Idx m → ℝ) {x : ℝ}
    (hx : 0 < x) :
    (Ppoly h w γ a).eval x = (D h w x * ∏ l, E (γ l) x) * ∑ i, a i * φ h w γ x i := by
  have hD := (D_pos (x := x) hh hw).ne'
  have hE : ∀ l, E (γ l) x ≠ 0 := fun l => (E_pos (γ l) hx).ne'
  rw [sum_idx, mul_add, Finset.mul_sum]
  simp only [Ppoly, Apoly, Bpoly, eval_add, eval_mul, eval_finsetSum, eval_prod, eval_C,
    eval_pow, eval_X, Dp_eval, Ep_eval, φ]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_prod_erase univ (fun l' => E (γ l') x) (mem_univ l)]
    have hl := hE l
    field_simp
    norm_num
    ring

/-- **The features are linearly independent on `(0, ∞)`.** -/
theorem features_independent {h w : ℝ} (hh : 0 < h) (hw : 0 < w) (γ : Fin m → ℝ)
    (hγ : ∀ l, γ l ≠ 0) (hinj : Function.Injective fun l => γ l ^ 2) (a : Idx m → ℝ)
    (ha : ∀ x, 0 < x → ∑ i, a i * φ h w γ x i = 0) : a = 0 := by
  -- the cleared polynomial vanishes on (0, ∞), hence identically
  have hP : Ppoly h w γ a = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => ?_) (Set.Ioi_infinite 0)
    show IsRoot _ x
    rw [IsRoot, Ppoly_eval hh hw.le γ a hx, ha x hx, mul_zero]
  -- evaluate at the complex point iγ_l
  have hB : ∀ l, a (Sum.inr (l, 0)) = 0 ∧ a (Sum.inr (l, 1)) = 0 := by
    intro l
    set z : ℂ := (γ l : ℂ) * Complex.I with hz
    have hEz : ∀ l', aeval z (Ep (γ l')) = ((γ l' ^ 2 - γ l ^ 2 : ℝ) : ℂ) := by
      intro l'; simp [Ep, hz, mul_pow, Complex.I_sq]; ring
    have hEl : aeval z (Ep (γ l)) = 0 := by rw [hEz]; simp
    have hDz : aeval z (Dp h w) = (((h - γ l ^ 2) ^ 2 + w : ℝ) : ℂ) := by
      simp [Dp, hz, mul_pow, Complex.I_sq]; ring
    have h0 := congrArg (aeval z) hP
    rw [map_zero, Ppoly, map_add, map_mul, map_prod, Finset.prod_eq_zero (mem_univ l) hEl,
      mul_zero, zero_add, map_sum, Finset.sum_eq_single l] at h0
    · rw [map_mul, map_mul, map_prod, hDz] at h0
      have hprod : ∏ l' ∈ univ.erase l, aeval z (Ep (γ l')) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro l' hl'
        rw [hEz]
        have hne : l' ≠ l := Finset.ne_of_mem_erase hl'
        have : γ l' ^ 2 - γ l ^ 2 ≠ 0 := sub_ne_zero.mpr fun h => hne (hinj h)
        exact_mod_cast this
      have hDne : (((h - γ l ^ 2) ^ 2 + w : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (h - γ l ^ 2) ^ 2 + w ≠ 0)
      have hBz : aeval z (Bpoly a l) = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · exact h2
          · exact absurd h2 hDne
        · exact absurd h1 hprod
      simp only [Bpoly, map_add, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap] at hBz
      have hre := congrArg Complex.re hBz
      have him := congrArg Complex.im hBz
      simp [hz] at hre him
      exact ⟨hre, by
        rcases him with h | h
        · exact h
        · exact absurd h (hγ l)⟩
    · intro l' _ hl'
      rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hl', mem_univ l⟩) hEl,
        mul_zero]
    · intro h; exact absurd (mem_univ l) h
  -- then A · ∏E = 0, so A = 0
  have hBpoly : ∀ l, Bpoly a l = 0 := fun l => by simp [Bpoly, (hB l).1, (hB l).2]
  have hA : Apoly a = 0 := by
    have : Apoly a * ∏ l, Ep (γ l) = 0 := by
      have := hP; simp only [Ppoly, hBpoly, zero_mul, Finset.sum_const_zero, add_zero] at this
      exact this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨l, _, hl⟩ := h
      have := congrArg (eval 0) hl
      simp [Ep] at this
      exact hγ l this
  funext i
  rcases i with k | ⟨l, j⟩
  · have := congrArg (fun p => coeff p (k : ℕ)) hA
    simp only [Apoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single k] at this
    · simpa using this
    · intro k' _ hk'; rw [if_neg (fun h => hk' (Fin.ext h).symm), mul_zero]
    · simp
  · fin_cases j
    · exact (hB l).1
    · exact (hB l).2

/-- **The features span** `ℝ^{4+2m}` as `x` ranges over `(0, ∞)`. -/
theorem span_top {h w : ℝ} (hh : 0 < h) (hw : 0 < w) (γ : Fin m → ℝ) (hγ : ∀ l, γ l ≠ 0)
    (hinj : Function.Injective fun l => γ l ^ 2) :
    Submodule.span ℝ (φ h w γ '' Set.Ioi 0) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set a : Idx m → ℝ := fun i => f fun j => if i = j then 1 else 0
  have ha : ∀ x, 0 < x → ∑ i, a i * φ h w γ x i = 0 := by
    intro x hx
    have hmem : φ h w γ x ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at hmem
    rw [← hmem]
    exact Finset.sum_congr rfl fun i _ => by simp [a, smul_eq_mul, mul_comm]
  have h0 := features_independent hh hw γ hγ hinj a ha
  apply hf
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a i = 0 := congrFun h0 i
  simp only [a] at this
  rw [this, smul_zero]

/-- **No masking.** One off-axis quartet plus any finite family of on-line pairs at distinct
heights: at some finite set of positive real nodes the total Pick form is strictly negative on a
two-dimensional family of weights. -/
theorem no_masking {h w : ℝ} (hh : 0 < h) (hw : 0 < w) (γ : Fin m → ℝ) (hγ : ∀ l, γ l ≠ 0)
    (hinj : Function.Injective fun l => γ l ^ 2) :
    ∃ S : Finset ℝ, (∀ x ∈ S, 0 < x) ∧ ∃ c₁ c₂ : ℝ → ℝ, ∀ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) →
      ∑ x ∈ S, ∑ y ∈ S, (α * c₁ x + β * c₂ x) * (α * c₁ y + β * c₂ y) * Ktot h w γ x y < 0 := by
  -- target feature vectors: quartet negative-plane moments, all pair moments zero
  let tE : Idx m → ℝ := Sum.elim ![1, 0, -(h ^ 2 + w) / h, 0] 0
  let tO : Idx m → ℝ := Sum.elim ![0, 1, 0, -h] 0
  have hspan := span_top hh hw γ hγ hinj
  have hE : tE ∈ Submodule.span ℝ (φ h w γ '' Set.Ioi 0) := hspan ▸ Submodule.mem_top
  have hO : tO ∈ Submodule.span ℝ (φ h w γ '' Set.Ioi 0) := hspan ▸ Submodule.mem_top
  rw [Finsupp.mem_span_image_iff_linearCombination] at hE hO
  obtain ⟨l₁, hl₁, hl₁e⟩ := hE
  obtain ⟨l₂, hl₂, hl₂e⟩ := hO
  set S := l₁.support ∪ l₂.support
  have hS : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with h1 | h1
    · exact hl₁ h1
    · exact hl₂ h1
  -- the feature combination over S
  have hcomb : ∀ (l : ℝ →₀ ℝ), l.support ⊆ S →
      ∀ i, ∑ x ∈ S, l x * φ h w γ x i = Finsupp.linearCombination ℝ (φ h w γ) l i := by
    intro l hl i
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hl]
    · rw [Finset.sum_apply]; rfl
    · intro x _; simp
  refine ⟨S, hS, l₁, l₂, fun α β hαβ => ?_⟩
  rw [pick_eq hh hw.le γ S hS]
  have hv : ∀ i, ∑ x ∈ S, (α * l₁ x + β * l₂ x) * φ h w γ x i = α * tE i + β * tO i := by
    intro i
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [hcomb l₁ Finset.subset_union_left, hcomb l₂ Finset.subset_union_right, hl₁e, hl₂e]
  simp only [hv]
  simp [tE, tO]
  rw [show α * ((-w + -h ^ 2) / h) = -(h ^ 2 + w) / h * α by ring, show -(β * h) = -h * β by ring]
  have := Q_neg_plane hh hw α β hαβ
  linarith

end GppNoGo.FiniteNoMasking
