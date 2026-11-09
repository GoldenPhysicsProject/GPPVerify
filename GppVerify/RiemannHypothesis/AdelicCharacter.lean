/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicFundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Circle


/-!
# The standard adelic character and self-duality of `ℚ` (GP-DUAL)

On the concrete adele carrier `AQ = ℝ × 𝔸_f`:

* `adeleChar : AddChar AQ Circle` is the standard character `ψ = ψ_∞ · ∏_p ψ_p`, with
  `ψ_∞(t) = e^{2πit}` and `ψ_p(y) = e^{-2πi\{y\}_p}`. It is written globally. By strong
  approximation every adele is `x = principal q + (t, z)` with `z ∈ ∏ ℤ_v`, and then
  `ψ(x) = e^{2πi(x_∞ - q)}`. That value does not depend on `q`, because two such `q` differ by
  an integer (`adeleChar_eq_of_isRep`).
* `continuous_adeleChar`: `ψ` is continuous.
* `adeleChar_principal`: `ψ` is trivial on `ℚ`; `adeleChar_integral`: its finite part is trivial
  on `∏ ℤ_v`; `adeleChar_nontrivial`: `ψ(1/2, 0) ≠ 1`.
* **GP-DUAL** (`forall_adeleChar_principal_mul_eq_one_iff`): `ℚ^⊥ = ℚ`. An adele `a` with
  `ψ(q a) = 1` for every `q ∈ ℚ` is principal. The proof uses `q = 1` to make the real part
  rational, then `q = p^{-k}` to force the finite part into `p^k ℤ_p` for every `k`.

Next: write `ψ` as the product of its local factors (the place-by-place form), then GP0.

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §4). Sequencing (GP-DUAL before GP0):
Turbo, GPP-bridge PR #11, 6732493269.
-/

open IsDedekindDomain GppIdeleQ Real

namespace GlobalTate.Poisson

/-- `e(t) = e^{2πit}` as a point of the circle. -/
noncomputable def e (t : ℝ) : Circle := Circle.exp (2 * π * t)

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  simp only [e, mul_add, Circle.exp_add]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_int (n : ℤ) : e n = 1 := Circle.exp_two_pi_mul_int n

theorem e_add_int (t : ℝ) (n : ℤ) : e (t + n) = e t := by rw [e_add, e_int, mul_one]

theorem e_eq_one_iff (t : ℝ) : e t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [e, Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by nlinarith [pi_pos]⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, by ring⟩

theorem continuous_e : Continuous e :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

/-- `q` represents the finite part of `x`: `x_f - q ∈ ∏ ℤ_v`. -/
def IsRep (x : AQ) (q : ℚ) : Prop :=
  ∀ v, x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ

theorem exists_isRep (x : AQ) : ∃ q, IsRep x q := exists_rat_sub_mem_integers x.2

/-- A rational integral at every place is an integer. -/
theorem eq_num_of_integral (q : ℚ)
    (h : ∀ v : HeightOneSpectrum ℤ,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ) :
    q = q.num := by
  have hd := den_eq_one_of_padicNorm_le_one q fun p hp => by
    obtain ⟨v, rfl⟩ := exists_pr_eq hp
    exact (algebraMap_mem_integers_iff v q).1 (h v)
  rw [← Rat.num_div_den q]; simp [hd]

/-- Two representatives differ by an integer. -/
theorem IsRep.exists_int {x : AQ} {q q' : ℚ} (h : IsRep x q) (h' : IsRep x q') :
    ∃ n : ℤ, q' = q + n := by
  have hn := eq_num_of_integral (q' - q) fun v => by
    have := sub_mem (h v) (h' v)
    have e : algebraMap ℚ (v.adicCompletion ℚ) (q' - q) =
        (x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q) -
          (x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q') := by rw [map_sub]; ring
    rw [e]; exact this
  exact ⟨(q' - q).num, by rw [← hn]; ring⟩

theorem IsRep.add_int {x : AQ} {q : ℚ} (h : IsRep x q) (n : ℤ) : IsRep x (q + n) := fun v => by
  have := sub_mem (h v) (intCast_mem_integers v n)
  have e : x.2 v - algebraMap ℚ (v.adicCompletion ℚ) (q + n) =
      (x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q) - algebraMap ℚ (v.adicCompletion ℚ) n := by
    rw [map_add]; ring
  rw [e]; exact this

theorem IsRep.add {x y : AQ} {q q' : ℚ} (h : IsRep x q) (h' : IsRep y q') :
    IsRep (x + y) (q + q') := fun v => by
  have := add_mem (h v) (h' v)
  have e : (x + y).2 v - algebraMap ℚ (v.adicCompletion ℚ) (q + q') =
      (x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q) +
        (y.2 v - algebraMap ℚ (v.adicCompletion ℚ) q') := by
    rw [map_add]; show x.2 v + y.2 v - _ = _; ring
  rw [e]; exact this

theorem isRep_principal (q : ℚ) : IsRep (principal q) q := fun v => by
  have e : (principal q).2 v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl
  rw [e, sub_self]
  exact zero_mem _

/-- A chosen representative. -/
noncomputable def rep (x : AQ) : ℚ := (exists_isRep x).choose

theorem isRep_rep (x : AQ) : IsRep x (rep x) := (exists_isRep x).choose_spec

/-- The standard character, as a function. -/
noncomputable def adeleCharFun (x : AQ) : Circle := e (x.1 - rep x)

theorem adeleCharFun_eq_of_isRep {x : AQ} {q : ℚ} (h : IsRep x q) :
    adeleCharFun x = e (x.1 - q) := by
  obtain ⟨n, hn⟩ := (isRep_rep x).exists_int h
  rw [adeleCharFun, hn]
  push_cast
  rw [show x.1 - (rep x + n) = x.1 - rep x + ((-n : ℤ) : ℝ) by push_cast; ring, e_add_int]

/-- **The standard additive character** `ψ = ψ_∞ · ∏ ψ_p` of `AQ`. -/
noncomputable def adeleChar : AddChar AQ Circle where
  toFun := adeleCharFun
  map_zero_eq_one' := by
    rw [adeleCharFun_eq_of_isRep (q := 0) (by simpa using isRep_principal 0)]
    simp [e_zero]
  map_add_eq_mul' x y := by
    rw [adeleCharFun_eq_of_isRep ((isRep_rep x).add (isRep_rep y)),
      adeleCharFun_eq_of_isRep (isRep_rep x), adeleCharFun_eq_of_isRep (isRep_rep y), ← e_add]
    congr 1
    simp only [Prod.fst_add, Rat.cast_add]
    ring

theorem adeleChar_eq_of_isRep {x : AQ} {q : ℚ} (h : IsRep x q) :
    adeleChar x = e (x.1 - q) := adeleCharFun_eq_of_isRep h

/-- `ψ` is trivial on the principal adeles. -/
theorem adeleChar_principal (q : ℚ) : adeleChar (principal q) = 1 := by
  rw [adeleChar_eq_of_isRep (isRep_principal q)]
  simp [principal, e_zero]

/-- At infinity, `ψ` is `e^{2πit}`. -/
theorem adeleChar_real (t : ℝ) : adeleChar ((t, 0) : AQ) = e t := by
  rw [adeleChar_eq_of_isRep (q := 0) (fun v => by
    show (0 : v.adicCompletion ℚ) - _ ∈ _; simp)]
  simp

/-- `ψ` is nontrivial: `ψ(1/2, 0) = -1 ≠ 1`. -/
theorem adeleChar_nontrivial : adeleChar ((1 / 2 : ℝ), (0 : Af)) ≠ 1 := by
  rw [adeleChar_real, Ne, e_eq_one_iff]
  rintro ⟨n, hn⟩
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have : 2 * n = 1 := by exact_mod_cast h2
  omega

/-- The finite part of `ψ` is trivial on `∏ ℤ_v`. -/
theorem adeleChar_integral {z : Af} (hz : z ∈ intBox) : adeleChar ((0 : ℝ), z) = 1 := by
  rw [adeleChar_eq_of_isRep (q := 0) (fun v => by simpa using hz v)]
  simp [e_zero]

theorem isOpen_setOf_isRep (q : ℚ) : IsOpen {x : AQ | IsRep x q} := by
  have : {x : AQ | IsRep x q} = (fun x : AQ => x.2 - algebraMap ℚ Af q) ⁻¹' intBox := by
    ext x; rfl
  rw [this]
  exact isOpen_intBox.preimage (continuous_snd.sub continuous_const)

/-- `ψ` is continuous. -/
theorem continuous_adeleChar : Continuous (adeleChar : AQ → Circle) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hev : (fun y : AQ => e (y.1 - rep x)) =ᶠ[nhds x] adeleChar := by
    filter_upwards [(isOpen_setOf_isRep (rep x)).mem_nhds (isRep_rep x)] with y hy
    exact (adeleChar_eq_of_isRep hy).symm
  exact ((continuous_e.comp (continuous_fst.sub continuous_const)).continuousAt).congr hev

/-- If `ψ(x) = 1` and `q` represents `x`, then `x_∞ - q` is an integer, so `x_∞` also
represents `x`'s finite part up to that integer. -/
theorem exists_int_of_adeleChar_eq_one {x : AQ} {q : ℚ} (h : IsRep x q) (h1 : adeleChar x = 1) :
    ∃ n : ℤ, x.1 = ((q + n : ℚ) : ℝ) := by
  rw [adeleChar_eq_of_isRep h, e_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  exact ⟨n, by push_cast; linarith⟩

/-- The local step: an element of `ℚ_v` lying in `p^k ℤ_v` for every `k` is zero. -/
theorem eq_zero_of_forall_pow_mul_mem (v : HeightOneSpectrum ℤ) (z : v.adicCompletion ℚ)
    (h : ∀ k : ℕ, algebraMap ℚ (v.adicCompletion ℚ) (((pr v : ℚ) ^ k)⁻¹) * z ∈
      v.adicCompletionIntegers ℚ) : z = 0 := by
  rw [← lnorm_eq_zero_iff]
  have hp : (1 : ℝ) < pr v := by exact_mod_cast (Fact.out : (pr v).Prime).one_lt
  have hbound : ∀ k : ℕ, lnorm v z ≤ ((pr v : ℝ)⁻¹) ^ k := by
    intro k
    have h1 := (mem_integers_iff v _).1 (h k)
    rw [lnorm_mul, lnorm_algebraMap] at h1
    have hn : ‖((((pr v : ℚ) ^ k)⁻¹ : ℚ) : ℚ_[pr v])‖ = (pr v : ℝ) ^ k := by
      push_cast
      rw [norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
    rw [hn] at h1
    have hpk : (0 : ℝ) < (pr v : ℝ) ^ k := by positivity
    rw [inv_pow, ← one_div, le_div_iff₀ hpk]
    linarith [mul_comm (lnorm v z) ((pr v : ℝ) ^ k)]
  by_contra hne
  have hpos : 0 < lnorm v z :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hp)
  exact absurd (hbound k) (not_le.mpr hk)

/-- **GP-DUAL: `ℚ^⊥ = ℚ`.** An adele `a` with `ψ(q a) = 1` for every `q ∈ ℚ` is principal,
and every principal adele has this property. -/
theorem forall_adeleChar_principal_mul_eq_one_iff (a : AQ) :
    (∀ q : ℚ, adeleChar (principal q * a) = 1) ↔ ∃ r : ℚ, a = principal r := by
  constructor
  · intro H
    obtain ⟨n, hn⟩ := exists_int_of_adeleChar_eq_one (isRep_rep a) (by simpa using H 1)
    set r : ℚ := rep a + n with hr_def
    refine ⟨r, Prod.ext (by simp [principal, hn]) ?_⟩
    apply RestrictedProduct.ext
    intro v
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_pow_mul_mem v
    intro k
    set q : ℚ := ((pr v : ℚ) ^ k)⁻¹
    have hrep := isRep_rep (principal q * a)
    obtain ⟨m, hm⟩ := exists_int_of_adeleChar_eq_one hrep (H q)
    have hqr : q * r = rep (principal q * a) + m := by
      have : ((q * r : ℚ) : ℝ) = ((rep (principal q * a) + m : ℚ) : ℝ) := by
        rw [← hm]; simp [principal, hn]
      exact_mod_cast this
    have hrep' : IsRep (principal q * a) (q * r) := by rw [hqr]; exact hrep.add_int m
    have h1 := hrep' v
    have e : (principal q * a).2 v - algebraMap ℚ (v.adicCompletion ℚ) (q * r) =
        algebraMap ℚ (v.adicCompletion ℚ) q *
          (a.2 v - (principal r).2 v) := by
      show algebraMap ℚ (v.adicCompletion ℚ) q * a.2 v - _ =
        _ * (a.2 v - algebraMap ℚ (v.adicCompletion ℚ) r)
      rw [map_mul]; ring
    rw [e] at h1
    exact h1
  · rintro ⟨r, rfl⟩ q
    rw [← map_mul]
    exact adeleChar_principal _

end GlobalTate.Poisson
