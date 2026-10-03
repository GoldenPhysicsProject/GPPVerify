import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic.NoncommRing

/-!
# The Hilbert–Pólya bounded-functional lemma, and exact unitary defect identities

Source: Codex, bridge `research/codex/` (bridge copy through `59bf0a2`):
* `2026-10-02_unitary_causal_completion.md` §§1, 4, 5, 7;
* `2026-10-02_causal_unitary_completion.md` §§5–6, 11.

These are the abstract algebraic cores of her ready-queue rows "Unitary block defect identity and
Hilbert–Pólya bounded functional lemma", "Unitary optical defect identity", and "Hardy block
defect of a unitary multiplier" (the algebraic parts).

## The one-line Hilbert–Pólya lemma

`hilbert_polya_lemma`: let `U_t` (`t ∈ ℝ`) be a family of linear isometries of a complex normed
space, and `ℓ ≠ 0` a bounded linear functional with `ℓ(U_t f) = e^{(ρ − ½) t} ℓ(f)` for all `t`
and `f`. Then `Re ρ = ½`. Only that each `U_t` is an isometry is used (the group law is not
needed), because boundedness of `ℓ` already forces `|e^{(ρ−½)t}| ≤ ‖ℓ‖‖f‖/|ℓ f|` for all real `t`.
This is the note's observation made precise; as the notes themselves stress, the hard theorem is
constructing the unitary group *and* showing nonzero bounded survival of every zero functional.

## Spectral-growth lower bound (norm-independent)

`growth_lower_bound`: if bounded operators `V_t` and a nonzero bounded functional `ℓ` satisfy
`ℓ(V_t x) = e^{(½−ρ)t} ℓ(x)`, then `‖V_t‖ ≥ e^{(½−Re ρ)t}` for every real `t` (so growth in positive
*and* negative time is bounded below). `type_lower_bound`: any two-sided exponential bound
`‖V_t‖ ≤ M e^{ω|t|}` forces `ω ≥ |Re ρ − ½|`. This is the abstract reason that engineering a norm
on a strip cannot by itself prove RH: any norm in which a retained zero functional exists has
exponential type at least `|Re ρ − ½|`. All zero-survival hypotheses stay outside the theorem.

## Blaschke transform of a unitary

In a `*`-algebra over `ℝ`, let `U` satisfy `U*U = 1`, let `r` be real, and let `V` invert
`1 − rU`. Put `B = (U − r) V`.

* `blaschke_isometry`: `B* B = 1`;
* `blaschke_defect`: if `X U = U X + ℓ U` for real `ℓ`, then
  `B* X B − X = ℓ (1 − r²) · V* V`. When `|r| < 1` and `ℓ ≥ 0` this is a positive multiple of
  `V* V`, hence positive;
* `defect_mul`: if `B₂*(B₁*XB₁ − X)B₂ = B₁*XB₁ − X`, the defects add:
  `(B₁B₂)* X (B₁B₂) − X = (B₁*XB₁ − X) + (B₂*XB₂ − X)`. The commutation hypothesis holds for
  translation operators at different primes, which commute.

## Optical identity

`optical_identity`: if `C*C + G*G = 1` (the first column of a unitary scattering block) and
`D₀ = C D`, then `D*D − D₀*D₀ = (G D)*(G D)`.

## The candidate contraction and its defect

`contraction_defect`: if `D₀ = C D` and `D W = 1`, then
`W* (D* D − D₀* D₀) W = 1 − C* C`, and `contraction_iff_defect_nonneg` (in a star-ordered ring,
with `D` having a right inverse) states `0 ≤ 1 − C*C ⟺ 0 ≤ D*D − D₀*D₀`. This is the note's
`‖C_L^{cand}‖ ≤ 1 ⟺ K_L ⪰ 0` with `K_L = D_ar* D_ar − D₀* D₀`, in the algebraic form `C*C ≤ 1`.

## Translation energy

`isometry_energy_identity`: for an isometry `T` of a complex inner product space,
`2 Re⟨f, T f⟩ = 2‖f‖² − ‖f − T f‖²`. For the translation `T_y` this is the note's
`q(f,f)(y) = 2 Re C_f(y) = 2‖f‖² − ‖f − T_y f‖²` (CCM translation-correlation identity), and it
shows the correlation kernel is a mass term minus a Dirichlet-type energy. The explicit constant
`κ_R(L)` in the note's Weil functional is not formalized.

## Scope and reading

Abstract `*`-ring algebra and one normed-space estimate. **Not formalized:** the Hilbert-space
realizations (the translation group on `L²(ℝ)`, the Hardy space, `T_Θ*T_Θ + H_Θ*H_Θ = I`
and the equivalences `RH ⟺ K_B = 0 ⟺ V_B` unitary). Those equivalences are statements of
operator theory about infinite-dimensional spaces and need the Hardy-space machinery Mathlib
lacks. One precision note: the displayed sum `B_P* X B_P − X = Σ_p Q_p` in the first note is correct
only because translations at different primes commute (this is exactly the hypothesis of
`defect_mul`); without commutation the defects are conjugated by the later factors. No RH claim.
-/

open Complex

namespace GppUnitaryCausal

/-- **The one-line Hilbert–Pólya lemma.** A nonzero bounded functional that is covariant with the
character `e^{(ρ − ½)t}` under a family of isometries forces `Re ρ = ½`. -/
theorem hilbert_polya_lemma {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : ℝ → E →ₗᵢ[ℂ] E) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (ρ : ℂ)
    (hcov : ∀ (t : ℝ) (f : E), ℓ (U t f) = Complex.exp ((ρ - 1 / 2) * (t : ℂ)) * ℓ f) :
    ρ.re = 1 / 2 := by
  obtain ⟨f, hf⟩ : ∃ f, ℓ f ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  set c : ℝ := ρ.re - 1 / 2 with hc
  have hnorm : ∀ t : ℝ, Real.exp (c * t) * ‖ℓ f‖ ≤ ‖ℓ‖ * ‖f‖ := by
    intro t
    have h1 := hcov t f
    have h2 : ‖ℓ (U t f)‖ ≤ ‖ℓ‖ * ‖U t f‖ := ℓ.le_opNorm _
    rw [LinearIsometry.norm_map] at h2
    rw [h1, norm_mul, Complex.norm_exp] at h2
    have : ((ρ - 1 / 2) * (t : ℂ)).re = c * t := by
      simp [hc, Complex.mul_re]
    rwa [this] at h2
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h; apply hne; linarith
  have hfn : 0 < ‖ℓ f‖ := norm_pos_iff.mpr hf
  have hf0 : f ≠ 0 := fun h => hf (by simp [h])
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hlpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  set K : ℝ := ‖ℓ‖ * ‖f‖ / ‖ℓ f‖ with hK
  have hKpos : 0 < K := by positivity
  have h := hnorm ((Real.log K + 1) / c)
  have e : c * ((Real.log K + 1) / c) = Real.log K + 1 := by field_simp
  rw [e, Real.exp_add, Real.exp_log hKpos] at h
  have h3 : K * Real.exp 1 * ‖ℓ f‖ ≤ ‖ℓ‖ * ‖f‖ := h
  have h4 : K * ‖ℓ f‖ = ‖ℓ‖ * ‖f‖ := by rw [hK]; field_simp
  have h5 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  nlinarith [mul_pos hKpos hfn]

/-- **Spectral-growth lower bound.** If `ℓ(V_t x) = e^{(½ − ρ)t} ℓ(x)` with `ℓ ≠ 0` bounded, then
`e^{(½ − Re ρ) t} ≤ ‖V_t‖` for all real `t`. -/
theorem growth_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ℝ → E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (ρ : ℂ)
    (hcov : ∀ (t : ℝ) (x : E), ℓ (V t x) = Complex.exp ((1 / 2 - ρ) * (t : ℂ)) * ℓ x) (t : ℝ) :
    Real.exp ((1 / 2 - ρ.re) * t) ≤ ‖V t‖ := by
  have hlpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  have hcomp : ℓ.comp (V t) = Complex.exp ((1 / 2 - ρ) * (t : ℂ)) • ℓ := by
    ext x; simp [hcov]
  have h1 : ‖ℓ.comp (V t)‖ ≤ ‖ℓ‖ * ‖V t‖ := ContinuousLinearMap.opNorm_comp_le _ _
  have hre : ((1 / 2 - ρ) * (t : ℂ)).re = (1 / 2 - ρ.re) * t := by
    simp [Complex.mul_re]
  have h2 : ‖ℓ.comp (V t)‖ = Real.exp ((1 / 2 - ρ.re) * t) * ‖ℓ‖ := by
    rw [hcomp, norm_smul, Complex.norm_exp, hre]
  rw [h2] at h1
  have h3 : Real.exp ((1 / 2 - ρ.re) * t) * ‖ℓ‖ ≤ ‖V t‖ * ‖ℓ‖ := by linarith
  exact le_of_mul_le_mul_right h3 hlpos

/-- **Exponential type is at least `|Re ρ − ½|`.** If `‖V_t‖ ≤ M e^{ω|t|}` for all real `t`
(with `M > 0`), then `|Re ρ − ½| ≤ ω`. -/
theorem type_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ℝ → E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ ≠ 0) (ρ : ℂ)
    (hcov : ∀ (t : ℝ) (x : E), ℓ (V t x) = Complex.exp ((1 / 2 - ρ) * (t : ℂ)) * ℓ x)
    (M ω : ℝ) (hM : 0 < M) (hbound : ∀ t : ℝ, ‖V t‖ ≤ M * Real.exp (ω * |t|)) :
    |ρ.re - 1 / 2| ≤ ω := by
  set c : ℝ := 1 / 2 - ρ.re with hc
  have hineq : ∀ t : ℝ, c * t ≤ Real.log M + ω * |t| := by
    intro t
    have h := (growth_lower_bound V ℓ hℓ ρ hcov t).trans (hbound t)
    have h' : Real.exp (c * t) ≤ Real.exp (Real.log M + ω * |t|) := by
      rw [Real.exp_add, Real.exp_log hM]; exact h
    exact Real.exp_le_exp.mp h'
  by_contra hlt
  push Not at hlt
  have hcabs : |c| = |ρ.re - 1 / 2| := by rw [hc, abs_sub_comm]
  have hgap : 0 < |c| - ω := by rw [hcabs]; linarith
  set s : ℝ := (|Real.log M| + 1) / (|c| - ω) with hs
  have hspos : 0 < s := by positivity
  -- Choose the sign of `t` so that `c * t = |c| * s`.
  have key : |c| * s ≤ Real.log M + ω * s := by
    rcases le_total 0 c with h | h
    · have := hineq s
      rw [abs_of_pos hspos] at this
      rw [abs_of_nonneg h]; exact this
    · have := hineq (-s)
      rw [abs_neg, abs_of_pos hspos] at this
      rw [abs_of_nonpos h]; nlinarith [this]
  have : (|c| - ω) * s = |Real.log M| + 1 := by rw [hs]; field_simp
  nlinarith [le_abs_self (Real.log M)]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]

/-- **The Blaschke transform of an isometry is an isometry.** If `U*U = 1` and `V` is a two-sided
inverse of `1 − rU`, then `B = (U − r) V` satisfies `B* B = 1`. -/
theorem blaschke_isometry (U V : R) (r : ℝ) (hU : star U * U = 1)
    (hV : (1 - r • U) * V = 1) :
    star ((U - r • (1 : R)) * V) * ((U - r • (1 : R)) * V) = 1 := by
  have hstar : star V * star (1 - r • U) = 1 := by
    rw [← star_mul, hV, star_one]
  have e : star (U - r • (1 : R)) * (U - r • 1) = star (1 - r • U) * (1 - r • U) := by
    simp only [star_sub, star_one, star_smul, star_trivial, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, hU]
    module
  calc star ((U - r • (1 : R)) * V) * ((U - r • (1 : R)) * V)
      = star V * (star (U - r • (1 : R)) * (U - r • 1)) * V := by
        simp only [star_mul, mul_assoc]
    _ = star V * (star (1 - r • U) * (1 - r • U)) * V := by rw [e]
    _ = (star V * star (1 - r • U)) * ((1 - r • U) * V) := by simp only [mul_assoc]
    _ = 1 := by rw [hstar, hV, one_mul]

/-- **The exact defect.** If `U*U = 1`, `V` inverts `1 − rU` on both sides, and `X U = U X + ℓ U`,
then `B* X B − X = ℓ (1 − r²) V* V` for `B = (U − r) V`. -/
theorem blaschke_defect (X U V : R) (r l : ℝ) (hU : star U * U = 1)
    (hV : (1 - r • U) * V = 1) (hX : X * U = U * X + l • U) :
    star ((U - r • (1 : R)) * V) * X * ((U - r • (1 : R)) * V) - X =
      (l * (1 - r ^ 2)) • (star V * V) := by
  have hstar : star V * star (1 - r • U) = 1 := by
    rw [← star_mul, hV, star_one]
  -- `X = V* (1 − rU*) X (1 − rU) V`.
  have hX' : X = star V * (star (1 - r • U) * X * (1 - r • U)) * V := by
    calc X = (star V * star (1 - r • U)) * X * ((1 - r • U) * V) := by rw [hstar, hV]; simp
      _ = _ := by simp only [mul_assoc]
  have hUXU : star U * X * U - X = l • (1 : R) := by
    calc star U * X * U - X = star U * (X * U) - X := by rw [mul_assoc]
      _ = star U * (U * X + l • U) - X := by rw [hX]
      _ = (star U * U) * X + l • (star U * U) - X := by
          simp only [mul_add, mul_smul_comm, ← mul_assoc]
      _ = l • (1 : R) := by rw [hU]; simp
  have hbr : star (U - r • (1 : R)) * X * (U - r • 1) - star (1 - r • U) * X * (1 - r • U) =
      (l * (1 - r ^ 2)) • (1 : R) := by
    have h1 : star (U - r • (1 : R)) * X * (U - r • 1) - star (1 - r • U) * X * (1 - r • U) =
        (1 - r ^ 2) • (star U * X * U - X) := by
      simp only [star_sub, star_one, star_smul, star_trivial, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub]
      module
    rw [h1, hUXU, smul_smul]; congr 1; ring
  calc star ((U - r • (1 : R)) * V) * X * ((U - r • (1 : R)) * V) - X
      = star V * (star (U - r • (1 : R)) * X * (U - r • 1)) * V -
          star V * (star (1 - r • U) * X * (1 - r • U)) * V := by
        rw [← hX']
        simp only [star_mul, mul_assoc]
    _ = star V * (star (U - r • (1 : R)) * X * (U - r • 1) -
          star (1 - r • U) * X * (1 - r • U)) * V := by
        rw [← sub_mul, ← mul_sub]
    _ = (l * (1 - r ^ 2)) • (star V * V) := by
        rw [hbr]; simp

omit [Algebra ℝ R] [StarModule ℝ R] in
/-- **Defects add** for commuting factors. If conjugation by `B₂` fixes the first
defect, then `(B₁B₂)* X (B₁B₂) − X = (B₁* X B₁ − X) + (B₂* X B₂ − X)`. -/
theorem defect_mul (X B₁ B₂ : R)
    (hcomm : star B₂ * (star B₁ * X * B₁ - X) * B₂ = star B₁ * X * B₁ - X) :
    star (B₁ * B₂) * X * (B₁ * B₂) - X =
      (star B₁ * X * B₁ - X) + (star B₂ * X * B₂ - X) := by
  have : star (B₁ * B₂) * X * (B₁ * B₂) = star B₂ * (star B₁ * X * B₁) * B₂ := by
    simp only [star_mul, mul_assoc]
  rw [this]
  have h3 : star B₂ * (star B₁ * X * B₁) * B₂ =
      star B₂ * (star B₁ * X * B₁ - X) * B₂ + star B₂ * X * B₂ := by
    simp only [mul_sub, sub_mul]; abel
  rw [h3, hcomm]
  abel

omit [Algebra ℝ R] [StarModule ℝ R] in
/-- **The optical identity.** If `C*C + G*G = 1` and `D₀ = C D`, then
`D*D − D₀*D₀ = (G D)*(G D)`. -/
theorem optical_identity (C G D D₀ : R) (h : star C * C + star G * G = 1) (hD : D₀ = C * D) :
    star D * D - star D₀ * D₀ = star (G * D) * (G * D) := by
  subst hD
  have : star D * D = star D * (star C * C + star G * G) * D := by rw [h]; simp
  calc star D * D - star (C * D) * (C * D)
      = star D * (star C * C + star G * G) * D - star (C * D) * (C * D) := by rw [← this]
    _ = star (G * D) * (G * D) := by
        simp only [star_mul, mul_add, add_mul, mul_assoc]; abel

omit [Algebra ℝ R] [StarModule ℝ R] in
/-- **The contraction defect.** If `D₀ = C D` and `D W = 1`, then
`W* (D* D − D₀* D₀) W = 1 − C* C`. -/
theorem contraction_defect (C D D₀ W : R) (hD₀ : D₀ = C * D) (hDW : D * W = 1) :
    star W * (star D * D - star D₀ * D₀) * W = 1 - star C * C := by
  subst hD₀
  have h1 : star W * (star D * D) * W = 1 := by
    calc star W * (star D * D) * W = star (D * W) * (D * W) := by
          simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hDW]; simp
  have h2 : star W * (star (C * D) * (C * D)) * W = star C * C := by
    calc star W * (star (C * D) * (C * D)) * W
        = star (C * (D * W)) * (C * (D * W)) := by simp only [star_mul, mul_assoc]
      _ = star C * C := by rw [hDW]; simp
  rw [mul_sub, sub_mul, h1, h2]

section Ordered

variable {S : Type*} [Ring S] [StarRing S] [PartialOrder S] [StarOrderedRing S]

/-- **`C*C ≤ 1` iff the defect is positive**, for `D₀ = C D` and `D` with a right inverse `W`. -/
theorem contraction_iff_defect_nonneg (C D D₀ W : S) (hD₀ : D₀ = C * D) (hDW : D * W = 1) :
    0 ≤ 1 - star C * C ↔ 0 ≤ star D * D - star D₀ * D₀ := by
  have key := contraction_defect C D D₀ W hD₀ hDW
  constructor
  · intro h
    have h' := star_left_conjugate_nonneg h D
    have : star D * (1 - star C * C) * D = star D * D - star D₀ * D₀ := by
      subst hD₀
      simp only [mul_sub, sub_mul, star_mul, mul_one, mul_assoc]
    rwa [this] at h'
  · intro h
    have h' := star_left_conjugate_nonneg h W
    rwa [key] at h'

end Ordered

/-- **Translation energy.** For an isometry `T` (`‖T f‖ = ‖f‖`):
`2 Re⟨f, T f⟩ = 2‖f‖² − ‖f − T f‖²`. -/
theorem isometry_energy_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗᵢ[ℂ] E) (f : E) :
    2 * (inner ℂ f (T f)).re = 2 * ‖f‖ ^ 2 - ‖f - T f‖ ^ 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) f (T f)
  simp only [RCLike.re_to_complex] at h
  rw [h, LinearIsometry.norm_map]
  ring

end GppUnitaryCausal
