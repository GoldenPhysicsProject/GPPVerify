import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The idèles of `ℚ` and Fujisaki's lemma: `𝔸¹/ℚˣ` is compact

The idèle group of `ℚ` is modelled as `ℝˣ × 𝔸_fˣ`, where `𝔸_f = FiniteAdeleRing ℤ ℚ` is
Mathlib's finite adele ring (restricted product of the `v`-adic completions over the
integral completions) and `𝔸_fˣ` carries the units topology (the topology induced by
`x ↦ (x, x⁻¹)`, which is the restricted-product idèle topology). The completion of `ℚ` at its
single infinite place is `ℝ`.

* `lnorm v` is the normalized absolute value at the finite place `v`, transported from
  `ℚ_p` along Mathlib's `adicCompletion.padicEquiv`.
* `exists_rat_norm`: every finite idèle has, place by place, the absolute values of a
  positive rational.
* `eq_one_or_neg_one`: a rational that is a `p`-adic unit for every `p` is `±1`.
* `finNorm_rat`, `ideleNorm_diag`: the **product formula** for `ℚ`.
* `isCompact_unitIdeles`: `∏_p ℤ_p^×` is compact in `𝔸_fˣ`.
* `exists_diag_mul`: `𝔸¹ = ℚˣ · ({±1} × ∏_p ℤ_p^×)`.
* `compactSpace_A1_quotient`: **Fujisaki's lemma for `ℚ`** — `𝔸¹/ℚˣ` is compact.
* `isFiniteMeasure_quotient`: every measure on `𝔸¹/ℚˣ` that is finite on compacts (in
  particular any Haar measure) is finite.
* `eq_one_of_near_one`, the `DiscreteTopology Qdiag` instance: `ℚˣ` is discrete, hence closed,
  in `𝔸¹`, so `𝔸¹/ℚˣ` is a compact Hausdorff group.
* `haarK1`, `exists_haar_probability`: the normalized Haar measure on `K¹ = 𝔸¹/ℚˣ` is a
  probability measure (`vol(K¹) = 1`).

**Scope.** `ℚ` only (not a general number field). Nothing here bears on the Riemann
Hypothesis, which remains open.

Daniel Toupin / Golden Physics Project, with AI assistance from Claude Code. Written to be
upstreamable to Mathlib.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

namespace GppIdeleQ

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The rational prime of a finite place of `ℚ`. -/
noncomputable abbrev pr (v : HeightOneSpectrum ℤ) : ℕ := (primesEquiv v : ℕ)

instance (v : HeightOneSpectrum ℤ) : Fact (pr v).Prime := ⟨(primesEquiv v).2⟩

/-- The normalized absolute value at the finite place `v`, transported from `ℚ_p`. -/
noncomputable def lnorm (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) : ℝ :=
  ‖(adicCompletion.padicEquiv v x : ℚ_[pr v])‖

lemma lnorm_mul (v : HeightOneSpectrum ℤ) (x y : v.adicCompletion ℚ) :
    lnorm v (x * y) = lnorm v x * lnorm v y := by
  simp [lnorm, map_mul]

lemma lnorm_algebraMap (v : HeightOneSpectrum ℤ) (q : ℚ) :
    lnorm v (algebraMap ℚ (v.adicCompletion ℚ) q) = ‖(q : ℚ_[pr v])‖ := by
  simp only [lnorm, eq_ratCast, map_ratCast]

lemma lnorm_eq_zero_iff (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    lnorm v x = 0 ↔ x = 0 := by
  simp [lnorm]

lemma mem_integers_iff (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ lnorm v x ≤ 1 := by
  have h := adicCompletion.padicEquiv_bijOn v
  constructor
  · intro hx; exact h.mapsTo hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := h.surjOn (show adicCompletion.padicEquiv v x ∈ PadicInt.subring (pr v) from hx)
    rwa [(adicCompletion.padicEquiv v).injective hyx] at hy

lemma lnorm_eq_one_of_valued (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ)
    (hx : Valued.v x = 1) : lnorm v x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h1 : lnorm v x ≤ 1 := (mem_integers_iff v x).1 ((mem_adicCompletionIntegers _ _ _).2 hx.le)
  have h2 : lnorm v x⁻¹ ≤ 1 := (mem_integers_iff v _).1
    ((mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hx, inv_one]))
  have hm : lnorm v x * lnorm v x⁻¹ = 1 := by rw [← lnorm_mul, mul_inv_cancel₀ hx0]; simp [lnorm]
  nlinarith [show (0:ℝ) ≤ lnorm v x from norm_nonneg _, show (0:ℝ) ≤ lnorm v x⁻¹ from norm_nonneg _]

lemma pr_injective : Function.Injective pr := fun _ _ h =>
  (primesEquiv (R := ℤ)).injective (Subtype.ext h)

open Classical in
lemma norm_pr (v w : HeightOneSpectrum ℤ) :
    ‖((pr v : ℚ) : ℚ_[pr w])‖ = if v = w then ((pr w : ℝ))⁻¹ else 1 := by
  split_ifs with h
  · subst h; rw [Rat.cast_natCast]; exact Padic.norm_p
  · rw [Rat.cast_natCast, Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out) (Fact.out)).2 (fun e => h (pr_injective e).symm)

/-- A positive rational in product form `∏_{v ∈ T} p_v^{n_v}`. -/
noncomputable def prodQ (T : Finset (HeightOneSpectrum ℤ)) (n : HeightOneSpectrum ℤ → ℤ) : ℚ :=
  ∏ v ∈ T, (pr v : ℚ) ^ n v

lemma prodQ_pos (T : Finset (HeightOneSpectrum ℤ)) (n : HeightOneSpectrum ℤ → ℤ) :
    0 < prodQ T n :=
  Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (Fact.out : (pr v).Prime).pos) _

open Classical in
lemma norm_prodQ (T : Finset (HeightOneSpectrum ℤ)) (n : HeightOneSpectrum ℤ → ℤ)
    (w : HeightOneSpectrum ℤ) :
    ‖((prodQ T n : ℚ) : ℚ_[pr w])‖ = if w ∈ T then (pr w : ℝ) ^ (-n w) else 1 := by
  rw [prodQ, Rat.cast_prod, norm_prod]
  simp_rw [Rat.cast_zpow, norm_zpow, norm_pr]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv => by simp [hv]]
    simp [zpow_neg]
  · exact Finset.prod_eq_one fun v hv => by simp [show v ≠ w from fun e => hw (e ▸ hv)]

/-- Every rational of the form `prodQ` with all `p`-adic norms equal to those of `x` ... -/
lemma exists_prodQ_norm (f : HeightOneSpectrum ℤ → ℝ) (T : Finset (HeightOneSpectrum ℤ))
    (hT : ∀ w ∉ T, f w = 1) (hf : ∀ w ∈ T, ∃ n : ℤ, f w = (pr w : ℝ) ^ (-n)) :
    ∃ n : HeightOneSpectrum ℤ → ℤ, ∀ w, ‖((prodQ T n : ℚ) : ℚ_[pr w])‖ = f w := by
  classical
  choose! n hn using hf
  exact ⟨n, fun w => by
    rw [norm_prodQ]; split_ifs with hw
    · exact (hn w hw).symm
    · exact (hT w hw).symm⟩

/-- The finite adeles of `ℚ`. -/
abbrev Af := FiniteAdeleRing ℤ ℚ

lemma unit_apply_ne_zero (a : Afˣ) (v : HeightOneSpectrum ℤ) : (a : Af) v ≠ 0 := by
  intro h
  have h1 : ((a : Af) * ((a⁻¹ : Afˣ) : Af)) v = (1 : Af) v := by rw [Units.mul_inv]
  rw [show ((a : Af) * ((a⁻¹ : Afˣ) : Af)) v = (a : Af) v * ((a⁻¹ : Afˣ) : Af) v from rfl, h,
    zero_mul] at h1
  exact zero_ne_one h1

lemma finite_ne_one (a : Afˣ) : {v | lnorm v ((a : Af) v) ≠ 1}.Finite := by
  have h := FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a
  refine (Filter.eventually_cofinite.1 h).subset fun v hv => ?_
  intro hv'
  exact hv (lnorm_eq_one_of_valued v _ hv')

/-- **Every finite idèle of `ℚ` has the absolute values of a positive rational.** -/
theorem exists_prodQ_eq (a : Afˣ) : ∃ (T : Finset (HeightOneSpectrum ℤ)) (n : HeightOneSpectrum ℤ → ℤ),
    ∀ w, ‖((prodQ T n : ℚ) : ℚ_[pr w])‖ = lnorm w ((a : Af) w) := by
  obtain ⟨n, hn⟩ := exists_prodQ_norm (fun w => lnorm w ((a : Af) w)) (finite_ne_one a).toFinset
    (fun w hw => by simpa using hw)
    (fun w _ => ⟨(adicCompletion.padicEquiv w ((a : Af) w)).valuation,
      Padic.norm_eq_zpow_neg_valuation (by simpa using unit_apply_ne_zero a w)⟩)
  exact ⟨_, n, hn⟩

theorem exists_rat_norm (a : Afˣ) :
    ∃ q : ℚ, 0 < q ∧ ∀ w, ‖(q : ℚ_[pr w])‖ = lnorm w ((a : Af) w) := by
  obtain ⟨T, n, h⟩ := exists_prodQ_eq a
  exact ⟨_, prodQ_pos T n, h⟩

lemma norm_rat_eq (p : ℕ) [Fact p.Prime] (x : ℚ) :
    ‖(x : ℚ_[p])‖ = ‖((x.num.natAbs : ℕ) : ℚ_[p])‖ / ‖((x.den : ℕ) : ℚ_[p])‖ := by
  have hx : (x : ℚ_[p]) = (x.num : ℚ_[p]) / (x.den : ℚ_[p]) := by
    conv_lhs => rw [← Rat.num_div_den x]
    push_cast; rfl
  rw [hx, norm_div]
  congr 1
  rcases Int.natAbs_eq x.num with h | h <;> rw [h] <;> simp

lemma norm_natCast_ne_one {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (h : p ∣ n) :
    ‖((n : ℕ) : ℚ_[p])‖ ≠ 1 := by
  rw [Ne, Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd hp.out]
  exact not_not.2 h

lemma dvd_of_norm_natCast_ne_one {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
    (h : ‖((n : ℕ) : ℚ_[p])‖ ≠ 1) : p ∣ n := by
  rw [Ne, Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd hp.out] at h
  exact not_not.1 h

lemma exists_pr_eq {m : ℕ} (hm : m.Prime) : ∃ w : HeightOneSpectrum ℤ, pr w = m :=
  ⟨(primesEquiv (R := ℤ)).symm ⟨m, hm⟩,
    congrArg Subtype.val ((primesEquiv (R := ℤ)).apply_symm_apply ⟨m, hm⟩)⟩

/-- **A rational number that is a `p`-adic unit for every prime `p` is `±1`.** -/
theorem eq_one_or_neg_one (x : ℚ) (hx : ∀ w : HeightOneSpectrum ℤ, ‖(x : ℚ_[pr w])‖ = 1) :
    x = 1 ∨ x = -1 := by
  have hden : x.den = 1 := by
    by_contra hd
    obtain ⟨w, hw⟩ := exists_pr_eq (Nat.minFac_prime hd)
    have hpd : pr w ∣ x.den := hw ▸ Nat.minFac_dvd _
    have h1 := hx w
    rw [norm_rat_eq, div_eq_one_iff_eq (by simp [x.den_ne_zero])] at h1
    have hpn : pr w ∣ x.num.natAbs :=
      dvd_of_norm_natCast_ne_one (h1 ▸ norm_natCast_ne_one hpd)
    exact (Fact.out : (pr w).Prime).ne_one (Nat.dvd_one.1 (x.reduced ▸ Nat.dvd_gcd hpn hpd))
  have hnum : x.num.natAbs = 1 := by
    by_contra hn
    obtain ⟨w, hw⟩ := exists_pr_eq (Nat.minFac_prime hn)
    have h1 := hx w
    rw [norm_rat_eq, hden] at h1
    simp only [Nat.cast_one, norm_one, div_one] at h1
    exact norm_natCast_ne_one (hw ▸ Nat.minFac_dvd _) h1
  have hxnum : x = x.num := (Rat.coe_int_num_of_den_eq_one hden).symm
  rcases Int.natAbs_eq_iff.1 hnum with h | h
  · left; rw [hxnum, h]; simp
  · right; rw [hxnum, h]; simp

open Classical in
lemma finprod_norm_prodQ (T : Finset (HeightOneSpectrum ℤ)) (n : HeightOneSpectrum ℤ → ℤ) :
    ∏ᶠ w, ‖((prodQ T n : ℚ) : ℚ_[pr w])‖ = ((prodQ T n : ℚ) : ℝ)⁻¹ := by
  simp_rw [norm_prodQ]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ fun w hw => by
    by_contra h; exact hw (if_neg h)]
  rw [Finset.prod_congr rfl fun w hw => if_pos hw, prodQ, Rat.cast_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg]

/-- The finite part of the idèle norm, `∏_p |a_p|_p`. -/
noncomputable def finNorm (a : Afˣ) : ℝ := ∏ᶠ v, lnorm v ((a : Af) v)

lemma finNorm_mul (a b : Afˣ) : finNorm (a * b) = finNorm a * finNorm b := by
  rw [finNorm, finNorm, finNorm, ← finprod_mul_distrib (finite_ne_one a) (finite_ne_one b)]
  exact finprod_congr fun v => lnorm_mul v _ _

lemma unitEmbedding_apply (q : ℚˣ) (v : HeightOneSpectrum ℤ) :
    ((FiniteAdeleRing.unitEmbedding ℤ ℚ q : Afˣ) : Af) v = algebraMap ℚ (v.adicCompletion ℚ) q :=
  rfl

/-- **Product formula for `ℚ`, finite part:** `∏_p |q|_p = |q|⁻¹`. -/
theorem finNorm_rat (q : ℚˣ) : finNorm (FiniteAdeleRing.unitEmbedding ℤ ℚ q) = |(q : ℚ)|⁻¹ := by
  obtain ⟨T, n, h⟩ := exists_prodQ_eq (FiniteAdeleRing.unitEmbedding ℤ ℚ q)
  simp_rw [unitEmbedding_apply, lnorm_algebraMap] at h
  have hq : (q : ℚ) ≠ 0 := q.ne_zero
  have hr : prodQ T n ≠ 0 := (prodQ_pos T n).ne'
  have hpm : (q : ℚ) / prodQ T n = 1 ∨ (q : ℚ) / prodQ T n = -1 := by
    refine eq_one_or_neg_one _ fun w => ?_
    rw [Rat.cast_div, norm_div, ← h w, div_self]
    rw [ne_eq, norm_eq_zero, Rat.cast_eq_zero]; exact hr
  have habs : |(q : ℚ)| = prodQ T n := by
    rcases hpm with e | e
    · rw [div_eq_one_iff_eq hr] at e; rw [e, abs_of_pos (prodQ_pos T n)]
    · rw [div_eq_iff hr] at e; rw [e, neg_one_mul, abs_neg, abs_of_pos (prodQ_pos T n)]
  rw [finNorm]
  simp_rw [unitEmbedding_apply, lnorm_algebraMap, ← h, finprod_norm_prodQ, ← habs]
  push_cast; rfl

lemma lnorm_one (v : HeightOneSpectrum ℤ) : lnorm v 1 = 1 := by simp [lnorm]

/-- The local unit sphere `{x : |x|_v = 1}` is compact. -/
lemma isCompact_sphere_v (v : HeightOneSpectrum ℤ) :
    IsCompact {x : v.adicCompletion ℚ | lnorm v x = 1} := by
  have : {x : v.adicCompletion ℚ | lnorm v x = 1} =
      (adicCompletion.padicEquiv v).symm '' Metric.sphere (0 : ℚ_[pr v]) 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, lnorm, Set.mem_image, mem_sphere_iff_norm, sub_zero]
    constructor
    · intro hx; exact ⟨_, hx, (adicCompletion.padicEquiv v).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [this]
  exact (isCompact_sphere _ _).image (adicCompletion.padicEquiv v).symm.continuous

/-- The local unit sphere, as a subset of the local integers. -/
lemma isCompact_sphere_integers (v : HeightOneSpectrum ℤ) :
    IsCompact {x : v.adicCompletionIntegers ℚ | lnorm v x = 1} := by
  rw [Subtype.isCompact_iff]
  convert isCompact_sphere_v v using 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, (mem_integers_iff v x).2 hx.le⟩, hx, rfl⟩

instance : T2Space Af :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Filter.cofinite))

/-- The norm-one finite adeles `∏_p ℤ_p^×` (as a submonoid of the finite adeles). -/
def unitBall : Submonoid Af where
  carrier := {a | ∀ v, lnorm v (a v) = 1}
  mul_mem' {a b} ha hb v := by
    rw [show (a * b) v = a v * b v from rfl, lnorm_mul, ha v, hb v, one_mul]
  one_mem' v := lnorm_one v

/-- The inclusion `∏_v O_v → 𝔸_f`. -/
def incl (x : (v : HeightOneSpectrum ℤ) → v.adicCompletionIntegers ℚ) : Af :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Filter.cofinite x

lemma continuous_incl : Continuous incl :=
  (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (A := fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (𝓕 := Filter.cofinite)).continuous

lemma incl_apply (x : (v : HeightOneSpectrum ℤ) → v.adicCompletionIntegers ℚ)
    (v : HeightOneSpectrum ℤ) : incl x v = x v := rfl

lemma isCompact_unitBall : IsCompact (unitBall : Set Af) := by
  have hP : IsCompact (Set.pi Set.univ fun v => {x : v.adicCompletionIntegers ℚ | lnorm v x = 1}) :=
    isCompact_univ_pi fun v => isCompact_sphere_integers v
  have heq : (unitBall : Set Af) = incl '' (Set.pi Set.univ fun v =>
      {x : v.adicCompletionIntegers ℚ | lnorm v x = 1}) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq,
      true_implies]
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, (mem_integers_iff v _).2 (ha v).le⟩, fun v => ha v, rfl⟩
    · rintro ⟨x, hx, rfl⟩ v
      rw [incl_apply]; exact hx v
  rw [heq]
  exact hP.image continuous_incl

/-- **`∏_p ℤ_p^×` is compact in the finite idèles.** -/
lemma isCompact_unitIdeles : IsCompact (unitBall.units : Set Afˣ) :=
  Submonoid.units_isCompact isCompact_unitBall

lemma finNorm_eq_one {u : Afˣ} (hu : ∀ v, lnorm v ((u : Af) v) = 1) : finNorm u = 1 := by
  rw [finNorm]; simp_rw [hu]; exact finprod_one

lemma finNorm_one : finNorm 1 = 1 := finNorm_eq_one fun v => lnorm_one v

lemma mem_units_of_lnorm {u : Afˣ} (hu : ∀ v, lnorm v ((u : Af) v) = 1) :
    u ∈ unitBall.units := by
  refine (Submonoid.mem_units_iff _ _).2 ⟨hu, fun v => ?_⟩
  have h1 : lnorm v ((u : Af) v) * lnorm v (((u⁻¹ : Afˣ) : Af) v) = 1 := by
    rw [← lnorm_mul, show (u : Af) v * ((u⁻¹ : Afˣ) : Af) v = ((u : Af) * ((u⁻¹ : Afˣ) : Af)) v
      from rfl, Units.mul_inv]
    exact lnorm_one v
  rwa [hu v, one_mul] at h1

lemma lnorm_of_mem_units {u : Afˣ} (hu : u ∈ unitBall.units) (v : HeightOneSpectrum ℤ) :
    lnorm v ((u : Af) v) = 1 :=
  ((Submonoid.mem_units_iff _ _).1 hu).1 v

/-! ## The idèles of `ℚ` and the norm-one idèle class group -/

/-- The idèle group of `ℚ`: `ℝˣ × 𝔸_fˣ` (the completion of `ℚ` at its one infinite place is
`ℝ`; the finite part carries Mathlib's restricted-product idèle topology on units). -/
abbrev Idele := ℝˣ × Afˣ

/-- The idèle norm `|x_∞| · ∏_p |x_p|_p`. -/
noncomputable def ideleNorm : Idele →* ℝ where
  toFun x := |(x.1 : ℝ)| * finNorm x.2
  map_one' := by simp [finNorm_one]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, abs_mul, finNorm_mul]
    ring

/-- The norm-one idèles `𝔸¹`. -/
noncomputable def A1 : Subgroup Idele := (MonoidHom.toHomUnits ideleNorm).ker

lemma mem_A1 {x : Idele} : x ∈ A1 ↔ ideleNorm x = 1 := by
  rw [A1, MonoidHom.mem_ker, Units.ext_iff]; rfl

/-- The diagonal embedding `ℚˣ → 𝔸ˣ`. -/
noncomputable def diag : ℚˣ →* Idele :=
  (Units.map (Rat.castHom ℝ : ℚ →* ℝ)).prod (FiniteAdeleRing.unitEmbedding ℤ ℚ)

/-- **Product formula for `ℚ`:** every principal idèle has norm one. -/
theorem ideleNorm_diag (q : ℚˣ) : ideleNorm (diag q) = 1 := by
  show |((q : ℚ) : ℝ)| * finNorm (FiniteAdeleRing.unitEmbedding ℤ ℚ q) = 1
  rw [finNorm_rat, Rat.cast_inv, Rat.cast_abs]
  exact mul_inv_cancel₀ (by simp)

/-- `ℚˣ` inside `𝔸¹`. -/
noncomputable def Qdiag : Subgroup A1 :=
  (diag.codRestrict A1 fun q => mem_A1.2 (ideleNorm_diag q)).range

/-- Norm-one idèles with unit components: `{±1} × ∏_p ℤ_p^×`. -/
def unitSet : Set Idele := {x : ℝˣ | |(x : ℝ)| = 1} ×ˢ (unitBall.units : Set Afˣ)

lemma isCompact_unitSet : IsCompact unitSet := by
  refine IsCompact.prod (Set.Finite.isCompact (((Set.finite_singleton (-1 : ℝˣ)).insert 1).subset ?_))
    isCompact_unitIdeles
  intro x hx
  rcases abs_eq (zero_le_one' ℝ) |>.1 hx with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

lemma unitSet_subset_A1 : unitSet ⊆ A1 := by
  rintro ⟨x, u⟩ ⟨hx, hu⟩
  rw [SetLike.mem_coe, mem_A1]
  show |(x : ℝ)| * finNorm u = 1
  rw [hx, finNorm_eq_one (lnorm_of_mem_units hu), one_mul]

/-- **Decomposition `𝔸¹ = ℚˣ · ({±1} × ∏_p ℤ_p^×)`.** -/
theorem exists_diag_mul (x : Idele) (hx : x ∈ A1) :
    ∃ q : ℚˣ, ∃ s ∈ unitSet, x = diag q * s := by
  obtain ⟨r, hr, hn⟩ := exists_rat_norm x.2
  set q : ℚˣ := Units.mk0 r hr.ne'
  have hq : ((q : ℚ)) = r := rfl
  set u : Afˣ := x.2 * (FiniteAdeleRing.unitEmbedding ℤ ℚ q)⁻¹
  have hu : ∀ w, lnorm w ((u : Af) w) = 1 := by
    intro w
    rw [show (u : Af) w = (x.2 : Af) w * (((FiniteAdeleRing.unitEmbedding ℤ ℚ q)⁻¹ : Afˣ) : Af) w
      from rfl, ← map_inv, unitEmbedding_apply, lnorm_mul, lnorm_algebraMap, ← hn w,
      Units.val_inv_eq_inv_val, hq, Rat.cast_inv, norm_inv]
    exact mul_inv_cancel₀ (by rw [ne_eq, norm_eq_zero, Rat.cast_eq_zero]; exact hr.ne')
  have hfin : finNorm x.2 = (r : ℝ)⁻¹ := by
    have : x.2 = FiniteAdeleRing.unitEmbedding ℤ ℚ q * u := by simp [u]
    rw [this, finNorm_mul, finNorm_rat, finNorm_eq_one hu, mul_one, hq, abs_of_pos hr]
    push_cast; rfl
  have hinf : |(x.1 : ℝ)| = r := by
    have h := mem_A1.1 hx
    change |(x.1 : ℝ)| * finNorm x.2 = 1 at h
    rw [hfin] at h
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (mul_inv_eq_one₀ hr').1 h
  refine ⟨q, ((diag q).1⁻¹ * x.1, u), ⟨?_, mem_units_of_lnorm hu⟩, ?_⟩
  · show |(((diag q).1⁻¹ * x.1 : ℝˣ) : ℝ)| = 1
    simp only [diag, MonoidHom.prod_apply, Units.val_mul, Units.coe_map_inv, abs_mul, hinf]
    simp [hq]
    rw [abs_of_pos (show (0:ℝ) < r by exact_mod_cast hr),
      inv_mul_cancel₀ (show (r:ℝ) ≠ 0 by exact_mod_cast hr.ne')]
  · ext
    · simp
    · simp [u, diag]

/-- **Fujisaki's lemma for `ℚ`: the norm-one idèle class group `𝔸¹/ℚˣ` is compact.** -/
theorem compactSpace_A1_quotient : CompactSpace (A1 ⧸ Qdiag) := by
  have hS : IsCompact (Subtype.val ⁻¹' unitSet : Set A1) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by
      rw [Subtype.range_coe]; exact unitSet_subset_A1)]
    exact isCompact_unitSet
  refine ⟨?_⟩
  have himg : (QuotientGroup.mk : A1 → A1 ⧸ Qdiag) '' (Subtype.val ⁻¹' unitSet) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨q, s, hs, hxs⟩ := exists_diag_mul x.1 x.2
    refine ⟨⟨s, unitSet_subset_A1 hs⟩, hs, ?_⟩
    rw [QuotientGroup.eq]
    refine ⟨q, Subtype.ext ?_⟩
    simp only [MonoidHom.codRestrict_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hxs]
    simp only [mul_comm, mul_left_comm]
    exact (mul_inv_cancel_left s (diag q)).symm
  rw [← himg]
  exact hS.image QuotientGroup.continuous_mk

/-- The norm-one idèle class group has finite volume: any measure on it that is finite on
compact sets (in particular any Haar measure) is a finite measure. -/
theorem isFiniteMeasure_quotient {m : MeasurableSpace (A1 ⧸ Qdiag)}
    (μ : MeasureTheory.Measure (A1 ⧸ Qdiag)) [MeasureTheory.IsFiniteMeasureOnCompacts μ] :
    MeasureTheory.IsFiniteMeasure μ := by
  have := compactSpace_A1_quotient
  infer_instance

/-! ## Discreteness of `ℚˣ` and the Haar probability measure on `K¹` -/

lemma isOpen_integers (v : HeightOneSpectrum ℤ) :
    IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (adicCompletion.padicEquiv v) ⁻¹' Metric.closedBall (0 : ℚ_[pr v]) 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_integers_iff, Set.mem_preimage, Metric.mem_closedBall,
      dist_zero_right, lnorm]
  rw [this]
  exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage
    (adicCompletion.padicEquiv v).continuous

/-- A rational that is a `p`-adic integer for every `p` is an integer. -/
lemma den_eq_one_of_norm_le (x : ℚ) (hx : ∀ w : HeightOneSpectrum ℤ, ‖(x : ℚ_[pr w])‖ ≤ 1) :
    x.den = 1 := by
  by_contra hd
  obtain ⟨w, hw⟩ := exists_pr_eq (Nat.minFac_prime hd)
  have hpd : pr w ∣ x.den := hw ▸ Nat.minFac_dvd _
  have h1 := hx w
  rw [norm_rat_eq] at h1
  have hnum : ‖((x.num.natAbs : ℕ) : ℚ_[pr w])‖ = 1 := by
    by_contra hne
    have hpn := dvd_of_norm_natCast_ne_one hne
    exact (Fact.out : (pr w).Prime).ne_one (Nat.dvd_one.1 (x.reduced ▸ Nat.dvd_gcd hpn hpd))
  have hden_lt : ‖((x.den : ℕ) : ℚ_[pr w])‖ < 1 :=
    lt_of_le_of_ne (by simpa using Padic.norm_int_le_one (p := pr w) (x.den : ℤ))
      (norm_natCast_ne_one hpd)
  have hden_pos : 0 < ‖((x.den : ℕ) : ℚ_[pr w])‖ := by
    rw [norm_pos_iff]; exact_mod_cast x.den_ne_zero
  rw [hnum, div_le_one hden_pos] at h1
  linarith

lemma eq_one_of_near_one (q : ℚˣ) (hinf : |((q : ℚ) : ℝ) - 1| < 1 / 2)
    (hf : ∀ v, ((FiniteAdeleRing.unitEmbedding ℤ ℚ q : Afˣ) : Af) v ∈ v.adicCompletionIntegers ℚ) :
    q = 1 := by
  have hden : (q : ℚ).den = 1 := den_eq_one_of_norm_le _ fun w => by
    have := (mem_integers_iff w _).1 (hf w)
    rwa [unitEmbedding_apply, lnorm_algebraMap] at this
  have hq : (q : ℚ) = ((q : ℚ).num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
  have hnum : (q : ℚ).num = 1 := by
    have h' : |(((q : ℚ).num : ℤ) : ℝ) - 1| < 1 / 2 := by
      rw [hq] at hinf; exact_mod_cast hinf
    have h2 : |(((q : ℚ).num - 1 : ℤ) : ℝ)| < 1 := by push_cast; linarith
    have h3 : |(q : ℚ).num - 1| < 1 := by exact_mod_cast h2
    have := abs_sub_lt_iff.1 h3
    omega
  exact Units.ext (by rw [hq, hnum]; simp)

/-- A neighbourhood of `1` in the idèles: `|x_∞ - 1| < 1/2` and every finite component integral. -/
def nbhdOne : Set Idele :=
  {x | |(x.1 : ℝ) - 1| < 1 / 2} ∩ {x | ∀ v, ((x.2 : Af) v) ∈ v.adicCompletionIntegers ℚ}

lemma isOpen_nbhdOne : IsOpen nbhdOne := by
  refine IsOpen.inter ?_ ?_
  · exact (isOpen_lt (continuous_abs.comp ((Units.continuous_val.comp continuous_fst).sub
      continuous_const)) continuous_const)
  · have hO : IsOpen {f : Af | ∀ v, f v ∈ v.adicCompletionIntegers ℚ} :=
      RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
        (A := fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
        fun v => isOpen_integers v
    exact hO.preimage (Units.continuous_val.comp continuous_snd)

lemma one_mem_nbhdOne : (1 : Idele) ∈ nbhdOne := by
  refine ⟨by simp, fun v => ?_⟩
  exact (v.adicCompletionIntegers ℚ).one_mem

instance : DiscreteTopology Qdiag := by
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set Qdiag) = (fun y : Qdiag => ((y : A1) : Idele)) ⁻¹' nbhdOne := by
    ext ⟨y, hy⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h; rw [show y = 1 from congrArg Subtype.val h]; exact one_mem_nbhdOne
    · intro h
      obtain ⟨q, rfl⟩ := hy
      have hq : q = 1 := eq_one_of_near_one q h.1 h.2
      subst hq
      apply Subtype.ext; apply Subtype.ext; simp
  rw [this]
  exact isOpen_nbhdOne.preimage (continuous_subtype_val.comp continuous_subtype_val)

/-- `ℚˣ` is closed in `𝔸¹`. -/
instance : IsClosed (Qdiag : Set A1) := Subgroup.isClosed_of_discrete

/-- The norm-one idèle class group is Hausdorff. -/
example : T2Space (A1 ⧸ Qdiag) := inferInstance

instance : CompactSpace (A1 ⧸ Qdiag) := compactSpace_A1_quotient

/-- The Borel σ-algebra on the norm-one idèle class group. -/
noncomputable instance : MeasurableSpace (A1 ⧸ Qdiag) := borel _

instance : BorelSpace (A1 ⧸ Qdiag) := ⟨rfl⟩

/-- The normalized Haar measure on `𝔸¹/ℚˣ`. -/
noncomputable def haarK1 : MeasureTheory.Measure (A1 ⧸ Qdiag) :=
  MeasureTheory.Measure.haarMeasure ⊤

instance : haarK1.IsHaarMeasure := by
  unfold haarK1; infer_instance

/-- **The Haar measure on `K¹ = 𝔸¹/ℚˣ` is a probability measure** (`vol(K¹) = 1`). -/
instance : MeasureTheory.IsProbabilityMeasure haarK1 := by
  constructor
  unfold haarK1
  simpa using MeasureTheory.Measure.haarMeasure_self
    (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (A1 ⧸ Qdiag)))

theorem exists_haar_probability :
    ∃ μ : MeasureTheory.Measure (A1 ⧸ Qdiag), μ.IsHaarMeasure ∧ MeasureTheory.IsProbabilityMeasure μ :=
  ⟨haarK1, inferInstance, inferInstance⟩

end GppIdeleQ
