import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Completed resolvent response: the π/6 sector, derivative signs, and the two-node Loewner obstruction

Source: Codex, `work/codex/2026-10-12_completed_resolvent_sector_passivity_and_loewner_gap.md`
(GPP-bridge 08754b6), items (i)–(iii) of its request for Lean. This file is the **finite algebra
only**.

Setup. A zero `z = δ + iγ` of `Ξ(z) = ξ(1/2 + z)` contributes, together with its conjugate partner,
`m_q(u) = 1/(u + A + iB) + 1/(u + A − iB)` to `m_*(u) = Ξ'(r)/(2rΞ(r))`, `r = √(1+u)`, where
`A = 1 + γ² − δ²` and `B = 2δγ`.

* `sector_identity`: `A − √3|B| = (|γ| − √3|δ|)² + 1 − 4δ²`. So `|δ| < 1/2` (the classical zero-free
  strip) puts `1 − z²` strictly inside the cone `Re λ > √3 |Im λ|` (`sector_pos`).
* `mq`, `d1`, `d2`: `m_q` in real form, its first derivative and its second derivative
  (`hasDerivAt_mq`, `hasDerivAt_d1`). If `u + A > √3|B|`, then `m_q > 0`, `m_q' < 0` and `m_q'' > 0`
  (`mq_pos`, `d1_neg`, `d2_pos`). The `√3` is exactly the condition `(u+A)² > 3B²` for the sign of
  `Re (u+A+iB)⁻³`. `quartet_signs` packages this for an actual quartet with `|δ| < 1/2`, `u ≥ 0`.
* `loewner_eq`, `loewner_det`: for the off-diagonal Loewner entry `−(m_q(u) − m_q(v))/(u − v)` and
  the diagonal `−m_q'`, the 2×2 determinant is exactly `−4B²(u−v)²/(N_u² N_v²)`. It is `< 0` for
  `B ≠ 0`, `u ≠ v` (`loewner_det_neg`). So one off-axis quartet is not Stieltjes at any two nodes,
  even though it passes the scalar sign tests above. `loewner_control` checks Codex's rational
  control `δ = 1/10`, `γ = 14`, `u = 1`, `v = 2`.
* `resolvent_identity`, `loewner_mixed`: abstractly, `R_u − R_v = (v − u) R_u R_v`. Hence if
  `m(u) = ℓ(R_u W)` for a linear functional `ℓ`, the Loewner entry is the mixed amplitude
  `ℓ(R_u R_v W)`.

**Scope.** These are the finite identities only. The unconditional statement for the full `m_*`
needs the zero-strip theorem, Hadamard factorization and normal convergence, none of which are
formalized here. The quadratic-form identity `c*L*c = ⟨W, h_c * h̃_c⟩` and its sign are not
formalized. Any positive factorization of it is open and would be RH-strength. **No RH claim.**
-/

namespace GppCompletedResolventSector

/-- `Re (1 − z²)` for `z = δ + iγ`. -/
def A (δ γ : ℝ) : ℝ := 1 + γ ^ 2 - δ ^ 2

/-- `−Im (1 − z²)` for `z = δ + iγ`. -/
def B (δ γ : ℝ) : ℝ := 2 * δ * γ

/-- **The sector identity.** -/
theorem sector_identity (δ γ : ℝ) :
    A δ γ - Real.sqrt 3 * |B δ γ| = (|γ| - Real.sqrt 3 * |δ|) ^ 2 + 1 - 4 * δ ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hγ := sq_abs γ
  have hδ := sq_abs δ
  unfold A B
  rw [abs_mul, abs_mul, abs_two]
  linear_combination (-1 : ℝ) * hγ - |δ| ^ 2 * h3 - 3 * hδ

/-- **Inside the zero-free strip the squared-mass shift lies in the `π/6` cone.** -/
theorem sector_pos {δ : ℝ} (hδ : |δ| < 1 / 2) (γ : ℝ) : Real.sqrt 3 * |B δ γ| < A δ γ := by
  have h := sector_identity δ γ
  have h4 : 4 * δ ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg δ]
  nlinarith [sq_nonneg (|γ| - Real.sqrt 3 * |δ|)]

/-- The quartet response `1/(u+a+ib) + 1/(u+a−ib)` in real form. -/
noncomputable def mq (a b u : ℝ) : ℝ := 2 * (u + a) / ((u + a) ^ 2 + b ^ 2)

/-- Its first derivative. -/
noncomputable def d1 (a b u : ℝ) : ℝ := 2 * (b ^ 2 - (u + a) ^ 2) / ((u + a) ^ 2 + b ^ 2) ^ 2

/-- Its second derivative. -/
noncomputable def d2 (a b u : ℝ) : ℝ :=
  4 * (u + a) * ((u + a) ^ 2 - 3 * b ^ 2) / ((u + a) ^ 2 + b ^ 2) ^ 3

variable {a b u v : ℝ}

lemma hasDerivAt_N (a b u : ℝ) :
    HasDerivAt (fun u => (u + a) ^ 2 + b ^ 2) (2 * (u + a)) u := by
  have h := (hasDerivAt_add_const_iff (b ^ 2)).mpr
    (HasDerivAt.fun_pow (((hasDerivAt_add_const_iff a).mpr (hasDerivAt_id' u))) 2)
  exact h.congr_deriv (by norm_num)

theorem hasDerivAt_mq (hN : (u + a) ^ 2 + b ^ 2 ≠ 0) : HasDerivAt (mq a b) (d1 a b u) u := by
  have h1 : HasDerivAt (fun u => 2 * (u + a)) 2 u :=
    (HasDerivAt.const_mul 2 (((hasDerivAt_add_const_iff a).mpr (hasDerivAt_id' u)))).congr_deriv
      (by norm_num)
  have := HasDerivAt.fun_div h1 (hasDerivAt_N a b u) hN
  refine this.congr_deriv ?_
  unfold d1
  field_simp
  ring

theorem hasDerivAt_d1 (hN : (u + a) ^ 2 + b ^ 2 ≠ 0) : HasDerivAt (d1 a b) (d2 a b u) u := by
  have h1 : HasDerivAt (fun u => 2 * (b ^ 2 - (u + a) ^ 2)) (2 * (-(2 * (u + a)))) u :=
    (HasDerivAt.const_mul 2 (HasDerivAt.const_sub (b ^ 2)
      (HasDerivAt.fun_pow (((hasDerivAt_add_const_iff a).mpr (hasDerivAt_id' u))) 2))).congr_deriv
      (by norm_num)
  have h2 : HasDerivAt (fun u => ((u + a) ^ 2 + b ^ 2) ^ 2)
      (2 * ((u + a) ^ 2 + b ^ 2) * (2 * (u + a))) u :=
    (HasDerivAt.fun_pow (hasDerivAt_N a b u) 2).congr_deriv (by norm_num)
  have := HasDerivAt.fun_div h1 h2 (pow_ne_zero 2 hN)
  refine this.congr_deriv ?_
  unfold d2
  field_simp
  ring

lemma N_pos (hu : 0 < u + a) : 0 < (u + a) ^ 2 + b ^ 2 := by positivity

theorem mq_pos (hu : 0 < u + a) : 0 < mq a b u := by
  unfold mq
  have := N_pos (b := b) hu
  positivity

theorem d1_neg (hu : |b| < u + a) : d1 a b u < 0 := by
  have hu0 : 0 < u + a := (abs_nonneg b).trans_lt hu
  have hN := N_pos (b := b) hu0
  have hb : b ^ 2 < (u + a) ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ hu (abs_nonneg b) two_ne_zero
  unfold d1
  apply div_neg_of_neg_of_pos
  · linarith
  · positivity

theorem d2_pos (hu : Real.sqrt 3 * |b| < u + a) : 0 < d2 a b u := by
  have hs : 0 ≤ Real.sqrt 3 * |b| := by positivity
  have hu0 : 0 < u + a := hs.trans_lt hu
  have hN := N_pos (b := b) hu0
  have h3 : (Real.sqrt 3 * |b|) ^ 2 = 3 * b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hb : 3 * b ^ 2 < (u + a) ^ 2 := by
    rw [← h3]
    exact pow_lt_pow_left₀ hu hs two_ne_zero
  unfold d2
  apply div_pos
  · have : 0 < (u + a) ^ 2 - 3 * b ^ 2 := by linarith
    positivity
  · positivity

/-- **Sign pattern of one actual quartet.** If `|δ| < 1/2` and `u ≥ 0`, then
`m_q(u) > 0`, `m_q'(u) < 0` and `m_q''(u) > 0`. -/
theorem quartet_signs {δ : ℝ} (hδ : |δ| < 1 / 2) (γ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 < mq (A δ γ) (B δ γ) u ∧ d1 (A δ γ) (B δ γ) u < 0 ∧ 0 < d2 (A δ γ) (B δ γ) u := by
  have hs := sector_pos hδ γ
  have h1 : |B δ γ| ≤ Real.sqrt 3 * |B δ γ| := by
    have : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [abs_nonneg (B δ γ)]
  have h0 : 0 ≤ Real.sqrt 3 * |B δ γ| := by positivity
  refine ⟨mq_pos (by linarith), d1_neg (by linarith), d2_pos (by linarith)⟩

/-- Off-diagonal Loewner entry `−(m(u) − m(v))/(u − v)`. -/
noncomputable def loewner (a b u v : ℝ) : ℝ := -(mq a b u - mq a b v) / (u - v)

/-- `L_{uv} = 2(Re f_u Re f_v − Im f_u Im f_v)` with `f_u = 1/(u+a+ib)`. -/
theorem loewner_eq (hu : 0 < u + a) (hv : 0 < v + a) (huv : u ≠ v) :
    loewner a b u v =
      2 * ((u + a) * (v + a) - b ^ 2) / (((u + a) ^ 2 + b ^ 2) * ((v + a) ^ 2 + b ^ 2)) := by
  have hNu := (N_pos (b := b) hu).ne'
  have hNv := (N_pos (b := b) hv).ne'
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  unfold loewner mq
  field_simp
  ring

/-- **The two-node Loewner determinant**, with diagonal entries `−m_q'`. -/
theorem loewner_det (hu : 0 < u + a) (hv : 0 < v + a) (huv : u ≠ v) :
    (-d1 a b u) * (-d1 a b v) - loewner a b u v ^ 2 =
      -4 * b ^ 2 * (u - v) ^ 2 / (((u + a) ^ 2 + b ^ 2) ^ 2 * ((v + a) ^ 2 + b ^ 2) ^ 2) := by
  have hNu := (N_pos (b := b) hu).ne'
  have hNv := (N_pos (b := b) hv).ne'
  rw [loewner_eq hu hv huv]
  unfold d1
  field_simp
  ring

/-- **One off-axis quartet is never Stieltjes at two nodes.** -/
theorem loewner_det_neg (hu : 0 < u + a) (hv : 0 < v + a) (huv : u ≠ v) (hb : b ≠ 0) :
    (-d1 a b u) * (-d1 a b v) - loewner a b u v ^ 2 < 0 := by
  rw [loewner_det hu hv huv]
  have hNu := N_pos (b := b) hu
  have hNv := N_pos (b := b) hv
  have : 0 < b ^ 2 * (u - v) ^ 2 := by
    have := sub_ne_zero.mpr huv
    positivity
  apply div_neg_of_neg_of_pos
  · linarith
  · positivity

/-- Codex's rational control: `δ = 1/10`, `γ = 14`, `u = 1`, `v = 2`. -/
theorem loewner_control :
    (-d1 (A (1 / 10) 14) (B (1 / 10) 14) 1) * (-d1 (A (1 / 10) 14) (B (1 / 10) 14) 2) -
        loewner (A (1 / 10) 14) (B (1 / 10) 14) 1 2 ^ 2 =
      -313600000000000000 / 24112580462576659325698504730374801 := by
  rw [loewner_det (by norm_num [A]) (by norm_num [A]) (by norm_num)]
  norm_num [A, B]

section resolvent

variable {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]

/-- **Resolvent identity.** If `a_u = T + u` and `a_v = T + v` are invertible, then
`a_u⁻¹ − a_v⁻¹ = (v − u) • a_u⁻¹ a_v⁻¹`. -/
theorem resolvent_identity (T : 𝔸) (u v : ℝ) (au av : 𝔸ˣ) (hu : (au : 𝔸) = T + algebraMap ℝ 𝔸 u)
    (hv : (av : 𝔸) = T + algebraMap ℝ 𝔸 v) :
    (↑au⁻¹ : 𝔸) - ↑av⁻¹ = (v - u) • ((↑au⁻¹ : 𝔸) * ↑av⁻¹) := by
  calc (↑au⁻¹ : 𝔸) - ↑av⁻¹ = ↑au⁻¹ * ((av : 𝔸) - au) * ↑av⁻¹ := by
        simp [mul_sub, sub_mul, mul_assoc]
    _ = (v - u) • ((↑au⁻¹ : 𝔸) * ↑av⁻¹) := by
        rw [hu, hv, add_sub_add_left_eq_sub, ← map_sub, ← Algebra.commutes, Algebra.smul_def,
          mul_assoc]

/-- **The Loewner entry is a mixed resolvent amplitude.** If `m(u) = ℓ(R_u W)` with
`R_u = (T + u)⁻¹` acting on `V`, then `−(m(u) − m(v))/(u − v) = ℓ(R_u R_v W)`. -/
theorem loewner_mixed {V : Type*} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (u v : ℝ)
    (huv : u ≠ v) (au av : (Module.End ℝ V)ˣ) (hu : (au : Module.End ℝ V) = T + algebraMap ℝ _ u)
    (hv : (av : Module.End ℝ V) = T + algebraMap ℝ _ v) (ℓ : V →ₗ[ℝ] ℝ) (W : V) :
    -(ℓ ((↑au⁻¹ : Module.End ℝ V) W) - ℓ ((↑av⁻¹ : Module.End ℝ V) W)) / (u - v) =
      ℓ ((↑au⁻¹ : Module.End ℝ V) ((↑av⁻¹ : Module.End ℝ V) W)) := by
  have h := congrArg (fun R : Module.End ℝ V => ℓ (R W)) (resolvent_identity T u v au av hu hv)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sub,
    map_smul, smul_eq_mul] at h
  rw [h]
  have : u - v ≠ 0 := sub_ne_zero.mpr huv
  field_simp
  ring

end resolvent

end GppCompletedResolventSector
