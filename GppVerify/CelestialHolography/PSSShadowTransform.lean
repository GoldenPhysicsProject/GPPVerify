import GppVerify.CelestialHolography.ConformalPrimaryWavefunction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# PSS File 6: the shadow transform

Pasterski–Shao, arXiv:1705.01027, §2.3. For a scalar conformal primary `O_Δ` on the celestial
`ℝ^d`, the shadow is the non-local operator (2.20)

  `Õ_Δ(w̃) = Γ(Δ) / (π^{d/2} Γ(Δ − d/2)) ∫ d^d w̃' |w̃ − w̃'|^{−2(d−Δ)} O_Δ(w̃')`,

and it transforms as a scalar conformal primary of dimension `d − Δ`.

## What is proved

* `shadow`: the operator (2.20), with the paper's normalisation `shadowConst`.
* `shadow_translate`: **translation covariance.** `S_Δ (f(· + a)) = (S_Δ f)(· + a)`.
* `shadow_dilate`: **dilation covariance with the shadow weight.** With
  `dilate Δ λ f (w̃) = λ^Δ f(λ w̃)` (the transformation of a weight-`Δ` primary under
  `w̃ ↦ λ w̃`, `λ > 0`), `S_Δ (dilate Δ λ f) = dilate (d − Δ) λ (S_Δ f)`. The output carries weight
  `d − Δ`. This is the statement that the shadow intertwines the dilation action, sending a
  dimension-`Δ` primary to a dimension-`(d − Δ)` one.
* `shadowDim`, `shadowDim_involutive`: **the label action** `Δ ↦ d − Δ` read off from
  `shadow_dilate`, and its involutivity.
* `neg_mink_nullVec_pos`: for `X` in the forward timelike cone, `−q(w̃)·X > 0` for every
  boundary point. So the massless primary `(−q·X)^{−Δ}` has a positive real base there.

Both covariance theorems are unconditional: they hold for every function `f`, because they rest
only on the invariance of Lebesgue measure under translations (`integral_add_right_eq_self`) and
its scaling under dilations (`Measure.integral_comp_smul`). For functions where the integral
does not exist, both sides are `0`.

## The named obligation

`ShadowKernelIdentity d`, OPEN: the integral identity (2.23),

  `∫ d^d z |z − w̃|^{−2(d−Δ)} (−q(z)·X)^{−Δ}
     = π^{d/2} Γ(Δ − d/2)/Γ(Δ) · (−X²)^{d/2−Δ} (−q(w̃)·X)^{Δ−d}`,

for `d ≥ 1`, `d/2 < Re Δ` and `X` forward timelike. The bound `d/2 < Re Δ` makes the kernel
integrable at `z = w̃`; at infinity the integrand decays like `|z|^{−2d}`. It is stated, not
asserted: no `sorry`, no `axiom`.
`shadow_masslessPrimary_of_kernelIdentity` derives the massless form of (2.24) from it:

  `S_{d−Δ} φ_{d−Δ} = (−X²)^{Δ−d/2} φ_Δ`,  `φ_Δ(w̃) = (−q(w̃)·X)^{−Δ}`.

For the massive wavefunction (2.19) the factor `(−X²)^{Δ−d/2}` is absorbed and (2.24) reads
`φ̃_{d−Δ} = φ_Δ`. Inversions (special conformal transformations) are not treated here. The
label-consistency corollary against the in-tree label map
`ConformalShadowPrincipalSeries.conformalShadow` belongs to the dictionary (File 7), because
that file imports the RiemannHypothesis tree and this one may not.

The PSS import wall holds: this file imports only Mathlib and File 1.
-/

open Complex MeasureTheory Set Filter
open GppConformalPrimaryWavefunction

namespace GppPSSShadowTransform

/-! ## The operator -/

/-- The normalisation of (2.20): `Γ(Δ) / (π^{d/2} Γ(Δ − d/2))`. -/
noncomputable def shadowConst (d : ℕ) (Δ : ℂ) : ℂ :=
  Gamma Δ / ((Real.pi : ℂ) ^ ((d : ℂ) / 2) * Gamma (Δ - (d : ℂ) / 2))

/-- The shadow kernel `|u|^{−2(d−Δ)} = (|u|²)^{−(d−Δ)}`. -/
noncomputable def shadowKernel (d : ℕ) (Δ : ℂ) (u : Fin d → ℝ) : ℂ :=
  ((normSqW u : ℝ) : ℂ) ^ (-((d : ℂ) - Δ))

/-- **The shadow transform** (1705.01027 (2.20)). -/
noncomputable def shadow (d : ℕ) (Δ : ℂ) (f : (Fin d → ℝ) → ℂ) (w : Fin d → ℝ) : ℂ :=
  shadowConst d Δ * ∫ z, shadowKernel d Δ (z - w) * f z

/-- The shadow dimension `d − Δ`. -/
def shadowDim (d : ℕ) (Δ : ℂ) : ℂ := d - Δ

/-- **The label action is an involution.** -/
theorem shadowDim_involutive (d : ℕ) (Δ : ℂ) : shadowDim d (shadowDim d Δ) = Δ := by
  unfold shadowDim; ring

/-! ## Translation covariance -/

/-- **Translation covariance.** `S_Δ (f(· + a))(w̃) = (S_Δ f)(w̃ + a)`. -/
theorem shadow_translate (d : ℕ) (Δ : ℂ) (f : (Fin d → ℝ) → ℂ) (a w : Fin d → ℝ) :
    shadow d Δ (fun z => f (z + a)) w = shadow d Δ f (w + a) := by
  unfold shadow
  congr 1
  have h := integral_add_right_eq_self
    (μ := (volume : Measure (Fin d → ℝ))) (fun y => shadowKernel d Δ (y - (w + a)) * f y) a
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  congr 2
  abel

/-! ## Dilation covariance -/

/-- The action of `w̃ ↦ λ w̃` on a weight-`Δ` primary: `λ^Δ f(λ w̃)`. -/
noncomputable def dilate {d : ℕ} (Δ : ℂ) (lam : ℝ) (f : (Fin d → ℝ) → ℂ) (w : Fin d → ℝ) : ℂ :=
  (lam : ℂ) ^ Δ * f (lam • w)

theorem normSqW_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : normSqW (c • v) = c ^ 2 * normSqW v := by
  unfold normSqW
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

theorem normSqW_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ normSqW v := by
  unfold normSqW; positivity

/-- For `λ > 0`: `(λ²)^z = λ^{2z}` with complex exponents. -/
theorem ofReal_sq_cpow {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    ((lam ^ 2 : ℝ) : ℂ) ^ z = (lam : ℂ) ^ (2 * z) := by
  have hlog : (Complex.log (lam : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hlam.le]
  rw [Complex.cpow_mul (x := (lam : ℂ)) (y := 2) z (by rw [Complex.mul_im]; simp [hlog]; positivity)
    (by rw [Complex.mul_im]; simp [hlog]; positivity)]
  congr 1
  push_cast
  rw [show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

/-- The kernel scales: `K(λ⁻¹ v) = λ^{2(d−Δ)} K(v)` for `λ > 0`. -/
theorem shadowKernel_inv_smul {d : ℕ} (Δ : ℂ) {lam : ℝ} (hlam : 0 < lam) (v : Fin d → ℝ) :
    shadowKernel d Δ (lam⁻¹ • v) = (lam : ℂ) ^ (2 * ((d : ℂ) - Δ)) * shadowKernel d Δ v := by
  unfold shadowKernel
  rw [normSqW_smul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity)
    (normSqW_nonneg v)]
  congr 1
  rw [inv_pow, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
  rw [ofReal_sq_cpow hlam, ← Complex.cpow_neg]
  congr 1
  ring

/-- **Dilation covariance with the shadow weight.** For `λ > 0`,
`S_Δ (dilate Δ λ f) = dilate (d − Δ) λ (S_Δ f)`: the shadow of a weight-`Δ` primary is a
weight-`(d − Δ)` primary. -/
theorem shadow_dilate (d : ℕ) (Δ : ℂ) {lam : ℝ} (hlam : 0 < lam) (f : (Fin d → ℝ) → ℂ)
    (w : Fin d → ℝ) :
    shadow d Δ (dilate Δ lam f) w = dilate (shadowDim d Δ) lam (shadow d Δ f) w := by
  have hl0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  set g : (Fin d → ℝ) → ℂ := fun u =>
    (lam : ℂ) ^ (2 * ((d : ℂ) - Δ)) * ((lam : ℂ) ^ Δ * (shadowKernel d Δ (u - lam • w) * f u))
    with hg
  have hF : ∀ z : Fin d → ℝ, shadowKernel d Δ (z - w) * dilate Δ lam f z = g (lam • z) := by
    intro z
    have e : z - w = lam⁻¹ • (lam • z - lam • w) := by
      rw [← smul_sub, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rw [hg]
    show shadowKernel d Δ (z - w) * ((lam : ℂ) ^ Δ * f (lam • z)) = _
    rw [e, shadowKernel_inv_smul Δ hlam]
    ring
  have hscale := Measure.integral_comp_smul (volume : Measure (Fin d → ℝ)) g lam
  rw [Module.finrank_fin_fun] at hscale
  unfold shadow shadowDim
  simp_rw [hF]
  rw [hscale]
  unfold dilate
  have hpow : |(lam ^ d)⁻¹| = (lam ^ d)⁻¹ := abs_of_pos (by positivity)
  rw [hpow, Complex.real_smul]
  simp only [hg]
  rw [integral_const_mul, integral_const_mul]
  have hd : (((lam ^ d)⁻¹ : ℝ) : ℂ) = (lam : ℂ) ^ (-(d : ℂ)) := by
    rw [Complex.cpow_neg, Complex.cpow_natCast]; push_cast; ring
  rw [hd]
  have hexp : (lam : ℂ) ^ (-(d : ℂ)) * ((lam : ℂ) ^ (2 * ((d : ℂ) - Δ)) * (lam : ℂ) ^ Δ) =
      (lam : ℂ) ^ ((d : ℂ) - Δ) := by
    rw [← Complex.cpow_add _ _ hl0, ← Complex.cpow_add _ _ hl0]
    congr 1; ring
  calc shadowConst d Δ * ((lam : ℂ) ^ (-(d : ℂ)) * ((lam : ℂ) ^ (2 * ((d : ℂ) - Δ)) *
          ((lam : ℂ) ^ Δ * ∫ u, shadowKernel d Δ (u - lam • w) * f u)))
      = ((lam : ℂ) ^ (-(d : ℂ)) * ((lam : ℂ) ^ (2 * ((d : ℂ) - Δ)) * (lam : ℂ) ^ Δ)) *
          (shadowConst d Δ * ∫ u, shadowKernel d Δ (u - lam • w) * f u) := by ring
    _ = (lam : ℂ) ^ ((d : ℂ) - Δ) *
          (shadowConst d Δ * ∫ u, shadowKernel d Δ (u - lam • w) * f u) := by rw [hexp]

/-! ## The massless primary and the forward cone -/

/-- `X` is in the forward timelike cone: `X⁰ > 0` and `X² < 0`. -/
def ForwardTimelike {d : ℕ} (X : Spacetime d) : Prop := 0 < X 0 ∧ mink X X < 0

theorem mink_eq {d : ℕ} (X Y : Spacetime d) :
    mink X Y = -(X 0 * Y 0) + ∑ i : Fin (d + 1), X i.succ * Y i.succ := by
  unfold mink
  rw [Fin.sum_univ_succ]
  simp [GppConformalPrimaryWavefunction.eta, Fin.succ_ne_zero]

/-- **A future null vector pairs negatively with a forward timelike vector.** If `q² = 0`,
`q⁰ > 0` and `X` is forward timelike, then `−q·X > 0`. -/
theorem neg_mink_pos_of_null {d : ℕ} {q X : Spacetime d} (hq : mink q q = 0) (hq0 : 0 < q 0)
    (hX : ForwardTimelike X) : 0 < -mink q X := by
  obtain ⟨hX0, hXX⟩ := hX
  rw [mink_eq] at hq hXX ⊢
  set S := ∑ i : Fin (d + 1), q i.succ * X i.succ with hS
  set Q := ∑ i : Fin (d + 1), q i.succ ^ 2 with hQ
  set P := ∑ i : Fin (d + 1), X i.succ ^ 2 with hP
  have hQ' : ∑ i : Fin (d + 1), q i.succ * q i.succ = Q := by
    rw [hQ]; exact Finset.sum_congr rfl fun i _ => by ring
  have hP' : ∑ i : Fin (d + 1), X i.succ * X i.succ = P := by
    rw [hP]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hQ'] at hq
  rw [hP'] at hXX
  have hcs : S ^ 2 ≤ Q * P := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hQeq : Q = q 0 ^ 2 := by nlinarith
  have hPlt : P < X 0 ^ 2 := by nlinarith
  have hlt : S ^ 2 < (q 0 * X 0) ^ 2 := by
    have : Q * P < q 0 ^ 2 * X 0 ^ 2 := by
      rw [hQeq]; exact mul_lt_mul_of_pos_left hPlt (by positivity)
    nlinarith
  have hpos : 0 < q 0 * X 0 := mul_pos hq0 hX0
  have := abs_lt_of_sq_lt_sq' hlt hpos.le
  linarith [this.2]

theorem nullVec_zero {d : ℕ} (w : Fin d → ℝ) : nullVec w 0 = 1 + normSqW w := by
  simp [nullVec]

/-- **`−q(w̃)·X > 0` on the forward cone**, for every boundary point `w̃`. -/
theorem neg_mink_nullVec_pos {d : ℕ} (w : Fin d → ℝ) {X : Spacetime d} (hX : ForwardTimelike X) :
    0 < -mink (nullVec w) X :=
  neg_mink_pos_of_null (minkowski_null_vector w)
    (by rw [nullVec_zero]; linarith [normSqW_nonneg w]) hX

/-- The massless conformal primary `(−q(w̃)·X)^{−Δ}` (the `ε → 0` form of File 1's closed form,
up to `Γ(Δ)` and the branch phase), on the forward cone where its base is positive. -/
noncomputable def masslessPrimary {d : ℕ} (Δ : ℂ) (X : Spacetime d) (w : Fin d → ℝ) : ℂ :=
  ((-mink (nullVec w) X : ℝ) : ℂ) ^ (-Δ)

/-! ## The kernel identity (2.23): named obligation -/

/-- **Named obligation (OPEN): the shadow kernel identity, 1705.01027 (2.23).** For `d ≥ 1`,
`d/2 < Re Δ` and `X` forward timelike,
`∫ d^d z |z − w̃|^{−2(d−Δ)} (−q(z)·X)^{−Δ}
  = π^{d/2} Γ(Δ − d/2)/Γ(Δ) · (−X²)^{d/2−Δ} (−q(w̃)·X)^{Δ−d}`. -/
def ShadowKernelIdentity (d : ℕ) : Prop :=
  ∀ (Δ : ℂ), 1 ≤ d → (d : ℝ) / 2 < Δ.re → ∀ (X : Spacetime d), ForwardTimelike X →
    ∀ w : Fin d → ℝ,
      ∫ z, shadowKernel d Δ (z - w) * masslessPrimary Δ X z =
        (Real.pi : ℂ) ^ ((d : ℂ) / 2) * Gamma (Δ - (d : ℂ) / 2) / Gamma Δ *
          ((-mink X X : ℝ) : ℂ) ^ ((d : ℂ) / 2 - Δ) *
          ((-mink (nullVec w) X : ℝ) : ℂ) ^ (Δ - d)

/-- **The massless form of (2.24), from the kernel identity.** If `ShadowKernelIdentity d`
holds, then for `Re Δ < d/2` and `X` forward timelike,
`S_{d−Δ} φ_{d−Δ} = (−X²)^{Δ−d/2} φ_Δ`. -/
theorem shadow_masslessPrimary_of_kernelIdentity {d : ℕ} (hK : ShadowKernelIdentity d)
    (hd : 1 ≤ d) {Δ : ℂ} (hΔ : Δ.re < (d : ℝ) / 2) (hΔ0 : 0 < Δ.re) {X : Spacetime d}
    (hX : ForwardTimelike X) (w : Fin d → ℝ) :
    shadow d ((d : ℂ) - Δ) (masslessPrimary ((d : ℂ) - Δ) X) w =
      ((-mink X X : ℝ) : ℂ) ^ (Δ - (d : ℂ) / 2) * masslessPrimary Δ X w := by
  have hre : (d : ℝ) / 2 < ((d : ℂ) - Δ).re := by simp; linarith
  have hk := hK ((d : ℂ) - Δ) hd hre X hX w
  unfold shadow
  rw [hk]
  have hG1 : Gamma ((d : ℂ) - Δ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  have hG2 : Gamma ((d : ℂ) - Δ - (d : ℂ) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ^ ((d : ℂ) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold shadowConst masslessPrimary
  have e1 : (d : ℂ) / 2 - ((d : ℂ) - Δ) = Δ - (d : ℂ) / 2 := by ring
  have e2 : (d : ℂ) - Δ - (d : ℂ) = -Δ := by ring
  rw [e1, e2]
  generalize Gamma ((d : ℂ) - Δ) = G1 at hG1 ⊢
  generalize Gamma ((d : ℂ) - Δ - (d : ℂ) / 2) = G2 at hG2 ⊢
  generalize (Real.pi : ℂ) ^ ((d : ℂ) / 2) = P at hpi ⊢
  field_simp

end GppPSSShadowTransform

#print axioms GppPSSShadowTransform.shadowDim_involutive
#print axioms GppPSSShadowTransform.shadow_translate
#print axioms GppPSSShadowTransform.shadow_dilate
#print axioms GppPSSShadowTransform.neg_mink_nullVec_pos
#print axioms GppPSSShadowTransform.shadow_masslessPrimary_of_kernelIdentity
