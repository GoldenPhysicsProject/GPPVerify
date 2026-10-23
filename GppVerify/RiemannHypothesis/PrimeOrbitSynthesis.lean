import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# No bounded synthesis of the prime orbit from one continuous translation group

Source: Astra, `work/2026-10-22_astra_prime_packet_construction.md` §3 (GPP-bridge). Daniel
Toupin / Golden Physics Project, with AI assistance from Astra (statement and proof) and Claude Code
(formalization).

Let `T` be a strongly continuous group of linear isometries of a complex normed space `H`,
indexed by the additive reals. Astra's theorem says that the vectors `T(log n) g` cannot be the images of an
orthonormal sequence `e_n` under a bounded map unless `g = 0`. The proof averages `M` consecutive
indices: `T(−log N) ∑_{j<M} T(log(N+j)) g → M g`, while boundedness caps the norm by `C √M`.

* `eq_zero_of_orbit_sum_le`: if `‖∑_{j<M} T(log(N+j)) g‖ ≤ C √M` for all `N ≥ 1` and all `M`, then
  `g = 0`. Only continuity of `a ↦ T a g` at `0` is used.
* `orbit_synthesis_eq_zero`: a bounded `U : ℓ²(ℕ₊) → H` with `U e_n = T(log n) g` for every `n`
  forces `g = 0` and `U = 0`.
* `prime_intertwiner_eq_zero`: a bounded `U` with `U e_{pn} = T(log p) U e_n` for every prime `p`
  and every `n` is zero. This is Astra's corollary for `U S_p = T_{log p} U`. Unique factorization
  gives `U e_n = T(log n) U e_1`.

**Scope.** This is about bounded maps from the unweighted arithmetic `ℓ²` into a single continuous
unitary orbit. Astra notes, and this file does not contradict, that weighted synthesis, unbounded
maps on test spaces, distributional maps, and the compact prime-character (Hardy) model of her §4
are all untouched. The co-Poisson summation operator is also untouched, since it is not claimed to
be a bounded map of this kind. Her §1–§2 packet estimates and §4 model are not formalized here.
No claim about RH.
-/

open Filter Topology

namespace GppPrimeOrbitSynthesis

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

private lemma tendsto_log_shift (j : ℕ) :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + j) - Real.log N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => 1 + (j : ℝ) / N) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)).const_add 1
  have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp]
  rw [← Real.log_div (by positivity) hN'.ne']
  congr 1
  field_simp

/-- **Bounded averages of the orbit force `g = 0`.** -/
theorem eq_zero_of_orbit_sum_le (T : ℝ → H →ₗᵢ[ℂ] H)
    (hmul : ∀ a b x, T (a + b) x = T a (T b x)) (g : H)
    (hcont : Tendsto (fun a => T a g) (𝓝 0) (𝓝 g)) (C : ℝ)
    (hC : ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ,
      ‖∑ j ∈ Finset.range M, T (Real.log ((N : ℝ) + j)) g‖ ≤ C * Real.sqrt M) :
    g = 0 := by
  -- For each `M`, `M ‖g‖ ≤ C √M`.
  have key : ∀ M : ℕ, (M : ℝ) * ‖g‖ ≤ C * Real.sqrt M := by
    intro M
    set f : ℕ → H := fun N =>
      ∑ j ∈ Finset.range M, T (Real.log ((N : ℝ) + j) - Real.log N) g
    have hf : Tendsto f atTop (𝓝 ((M : ℂ) • g)) := by
      have : Tendsto f atTop (𝓝 (∑ _j ∈ Finset.range M, g)) :=
        tendsto_finsetSum _ fun j _ => hcont.comp (tendsto_log_shift j)
      simpa [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ] using this
    have hbound : ∀ᶠ N in atTop, ‖f N‖ ≤ C * Real.sqrt M := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have heq : T (Real.log N) (f N) =
          ∑ j ∈ Finset.range M, T (Real.log ((N : ℝ) + j)) g := by
        simp only [f, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hmul, add_sub_cancel]
      rw [← (T (Real.log N)).norm_map (f N), heq]
      exact hC N hN M
    have hlim := le_of_tendsto (continuous_norm.tendsto _ |>.comp hf) hbound
    simpa [norm_smul] using hlim
  by_contra hg
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  obtain ⟨M, hM⟩ := exists_nat_gt ((C / ‖g‖) ^ 2)
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (sq_nonneg _) hM
  have hsq : C / ‖g‖ < Real.sqrt M := Real.lt_sqrt_of_sq_lt hM
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have h1 := key M
  have hMeq : (M : ℝ) = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt hMpos.le).symm
  nth_rewrite 1 [hMeq] at h1
  rw [mul_assoc] at h1
  have h2 : Real.sqrt M * ‖g‖ ≤ C := le_of_mul_le_mul_left (by linarith) hs
  rw [div_lt_iff₀ hgpos] at hsq
  linarith

/-- The index `N + j` as a positive natural number. -/
private def idx (N : ℕ+) (j : ℕ) : ℕ+ := ⟨N + j, by positivity⟩

private lemma idx_injective (N : ℕ+) : Function.Injective (idx N) := by
  intro a b h
  have := congrArg PNat.val h
  simp only [idx, PNat.mk_coe] at this
  omega

/-- **Orbit synthesis is impossible.** A bounded `U : ℓ²(ℕ₊) → H` with `U e_n = T(log n) g` for
every `n` has `g = 0` and `U = 0`. -/
theorem orbit_synthesis_eq_zero (T : ℝ → H →ₗᵢ[ℂ] H)
    (hmul : ∀ a b x, T (a + b) x = T a (T b x)) (g : H)
    (hcont : Tendsto (fun a => T a g) (𝓝 0) (𝓝 g))
    (U : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] H)
    (hU : ∀ n : ℕ+, U (lp.single 2 n 1) = T (Real.log n) g) :
    g = 0 ∧ U = 0 := by
  have hg : g = 0 := by
    refine eq_zero_of_orbit_sum_le T hmul g hcont ‖U‖ fun N hN M => ?_
    set N' : ℕ+ := ⟨N, hN⟩
    set s := (Finset.range M).map ⟨idx N', idx_injective N'⟩
    have hsum : ∑ j ∈ Finset.range M, T (Real.log ((N : ℝ) + j)) g =
        U (∑ i ∈ s, lp.single 2 i (1 : ℂ)) := by
      rw [map_sum, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hU]; simp [idx, N']
    have hnorm : ‖∑ i ∈ s, lp.single 2 i (1 : ℂ)‖ = Real.sqrt M := by
      have h := lp.norm_sum_single (E := fun _ : ℕ+ => ℂ) (p := 2) (by norm_num)
        (fun _ => (1 : ℂ)) s
      simp only [norm_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one,
        ENNReal.toReal_ofNat] at h
      have h' : ‖∑ i ∈ s, lp.single 2 i (1 : ℂ)‖ ^ 2 = (s.card : ℝ) := by exact_mod_cast h
      rw [show s.card = M by simp [s]] at h'
      rw [← h', Real.sqrt_sq (norm_nonneg _)]
    rw [hsum]
    calc _ ≤ ‖U‖ * ‖∑ i ∈ s, lp.single 2 i (1 : ℂ)‖ := U.le_opNorm _
      _ = ‖U‖ * Real.sqrt M := by rw [hnorm]
  refine ⟨hg, ?_⟩
  have hT0 : ∀ a, T a 0 = 0 := fun a => map_zero _
  ext1 f
  have hs := (lp.hasSum_single (E := fun _ : ℕ+ => ℂ) (p := 2) ENNReal.ofNat_ne_top f).map U
    U.continuous
  have hzero : ∀ i : ℕ+, U (lp.single 2 i (f i)) = 0 := fun i => by
    have : lp.single 2 i (f i) = f i • lp.single (E := fun _ : ℕ+ => ℂ) 2 i 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, hU, hg, hT0, smul_zero]
  simp only [Function.comp_def, hzero] at hs
  simpa using hs.unique hasSum_zero

/-- **No bounded prime intertwiner.** A bounded `U : ℓ²(ℕ₊) → H` with
`U e_{pn} = T(log p) U e_n` for every prime `p` and every `n` is zero. -/
theorem prime_intertwiner_eq_zero (T : ℝ → H →ₗᵢ[ℂ] H)
    (hmul : ∀ a b x, T (a + b) x = T a (T b x))
    (hcont : ∀ x : H, Tendsto (fun a => T a x) (𝓝 0) (𝓝 x))
    (U : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] H)
    (hU : ∀ (p : ℕ) (hp : p.Prime) (n : ℕ+),
      U (lp.single 2 (⟨p, hp.pos⟩ * n) 1) = T (Real.log p) (U (lp.single 2 n 1))) :
    U = 0 := by
  have hT0 : ∀ x, T 0 x = x := fun x =>
    (T 0).injective (by rw [← hmul, add_zero])
  set g := U (lp.single 2 1 1)
  have horbit : ∀ n : ℕ+, U (lp.single 2 n 1) = T (Real.log n) g := by
    intro n
    induction n using PNat.strongInductionOn with
    | _ n ih =>
      by_cases h1 : n = 1
      · subst h1; simp [hT0, g]
      · have hn1 : (n : ℕ) ≠ 1 := fun h => h1 (PNat.coe_eq_one_iff.mp h)
        set p := (n : ℕ).minFac
        have hp : p.Prime := Nat.minFac_prime hn1
        have hdvd : p ∣ (n : ℕ) := Nat.minFac_dvd _
        set m : ℕ+ := ⟨(n : ℕ) / p, Nat.div_pos (Nat.minFac_le n.pos) hp.pos⟩
        have hnm : n = ⟨p, hp.pos⟩ * m := by
          apply PNat.eq
          simp only [m]
          exact (Nat.mul_div_cancel' hdvd).symm
        have hlt : m < n := by
          rw [← PNat.coe_lt_coe]
          exact Nat.div_lt_self n.pos hp.one_lt
        rw [hnm, hU p hp m, ih m hlt, ← hmul]
        have hc : ((⟨p, hp.pos⟩ * m : ℕ+) : ℕ) = p * m := PNat.mul_coe _ _
        rw [hc, Nat.cast_mul,
          Real.log_mul (by exact_mod_cast hp.pos.ne') (by exact_mod_cast m.pos.ne')]
  exact (orbit_synthesis_eq_zero T hmul g (hcont g) U horbit).2

end GppPrimeOrbitSynthesis
