import GppVerify.RiemannHypothesis.SU11PrimeBlaschke

/-!
# Local odd-transfer contraction and the cross-mode Krein obstruction

Source: Codex, GPPDiscovery2 `research/2026-09-27_local_odd_transfer_contraction_cross_mode_obstruction.md`,
§§1, 2, 4, 5.

Let `Ω_r = √(1−r²) Σ_n r^n e_n` be the SU(1,1) coherent state and `J e_n = (−1)^n e_n` occupation
parity, so `J Ω_r = Ω_{−r}`; put `P_± = (I ± J)/2`.

* `reflected_overlap`: `⟨Ω_r, J Ω_s⟩ = √((1−r²)(1−s²))/(1 + r s)`; at `s = r` this is
  `(1−r²)/(1+r²)`, the purity (`(p−1)/(p+1)` at `r² = 1/p`);
* `plus_sq_hasSum`, `minus_sq_hasSum`: `‖P_+ Ω_r‖² = 1/(1+r²)` and `‖P_- Ω_r‖² = r²/(1+r²)`;
* `odd_even_ratio`: hence `‖P_- Ω_r‖ / ‖P_+ Ω_r‖ = |r|` (for a prime, `p^{-1/2} < 1`): every
  *single* coherent mode has a strict odd/even contraction;
* `krein_det_neg`: for two distinct parameters `r ≠ s` in `(−1, 1)` the `2×2` Gram matrix of the
  reflection kernel `K_J(r,s) = ⟨Ω_r, J Ω_s⟩` has determinant
  `−(1−r²)(1−s²)(r−s)² / ((1+r²)(1+s²)(1+rs)²) < 0`, so the raw reflection form is **indefinite**
  on the span of two distinct coherent tilts. (With `r = tan α`, `s = tan β` this is the note's
  `−cos 2α cos 2β tan²(α − β)`.)

## Checks and scope

All claims check; the determinant is given here in the `r, s` variables where it is a rational
identity, which is equivalent to the note's trigonometric form under `r = tan α`. **Not
formalized:** the Archimedean Jacobi-transform picture (§3: even/odd exponential tilts in
`L²(sech(πx) dx)`) and the sharpened target of §6 (a positive frame `G` with `G^{1/2} J G^{1/2} ≥ 0`
on the physical subspace). The meaning for the RH programme is the note's: local prime
contractions are correct but cannot by themselves give a global contraction. No RH claim.
-/

open GppSU11Prime

namespace GppSU11Reflection

/-- **Reflected overlap** `⟨Ω_r, J Ω_s⟩`. -/
theorem reflected_overlap (r s : ℝ) (hr : |r| < 1) (hs : |s| < 1) :
    HasSum (fun m : ℕ => Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) * (-(r * s)) ^ m)
      (Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) / (1 + r * s)) := by
  have hs' : |-s| < 1 := by rwa [abs_neg]
  have h := coherent_overlap r (-s) hr hs'
  simp only [neg_sq, mul_neg, sub_neg_eq_add] at h
  exact h

/-- At `s = r` the reflected overlap is the purity `(1−r²)/(1+r²)`. -/
theorem reflected_purity (r : ℝ) (hr : |r| < 1) :
    Real.sqrt ((1 - r ^ 2) * (1 - r ^ 2)) / (1 + r * r) = (1 - r ^ 2) / (1 + r ^ 2) := by
  have h : 0 ≤ 1 - r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r, abs_lt.mp hr]
  rw [Real.sqrt_mul_self h]
  ring_nf

private lemma abs_r4 (r : ℝ) (hr : |r| < 1) : |r ^ 4| < 1 := by
  rw [abs_pow]
  have := abs_nonneg r
  exact (pow_lt_one₀ this hr (by norm_num : (4 : ℕ) ≠ 0))

private lemma one_sub_sq_pos (r : ℝ) (hr : |r| < 1) : 0 < 1 - r ^ 2 := by
  nlinarith [abs_lt.mp hr, sq_abs r]

/-- `‖P_+ Ω_r‖² = Σ_k (1−r²) r^{4k} = 1/(1+r²)`. -/
theorem plus_sq_hasSum (r : ℝ) (hr : |r| < 1) :
    HasSum (fun k : ℕ => (1 - r ^ 2) * (r ^ 4) ^ k) (1 / (1 + r ^ 2)) := by
  have hg := (hasSum_geometric_of_abs_lt_one (abs_r4 r hr)).mul_left (1 - r ^ 2)
  have h1 := (one_sub_sq_pos r hr).ne'
  have h2 : 1 + r ^ 2 ≠ 0 := by positivity
  have h3 : 1 - r ^ 4 = (1 - r ^ 2) * (1 + r ^ 2) := by ring
  have e : (1 - r ^ 2) * (1 - r ^ 4)⁻¹ = 1 / (1 + r ^ 2) := by
    rw [h3]; field_simp
  rwa [e] at hg

/-- `‖P_- Ω_r‖² = Σ_k (1−r²) r^{2(2k+1)} = r²/(1+r²)`. -/
theorem minus_sq_hasSum (r : ℝ) (hr : |r| < 1) :
    HasSum (fun k : ℕ => (1 - r ^ 2) * r ^ 2 * (r ^ 4) ^ k) (r ^ 2 / (1 + r ^ 2)) := by
  have hg := (plus_sq_hasSum r hr).mul_left (r ^ 2)
  have e : (fun k : ℕ => r ^ 2 * ((1 - r ^ 2) * (r ^ 4) ^ k)) =
      fun k => (1 - r ^ 2) * r ^ 2 * (r ^ 4) ^ k := by funext k; ring
  rw [e] at hg
  rwa [mul_one_div] at hg

/-- **Strict local odd/even contraction**: `‖P_- Ω_r‖ / ‖P_+ Ω_r‖ = |r|`. -/
theorem odd_even_ratio (r : ℝ) :
    Real.sqrt (r ^ 2 / (1 + r ^ 2)) / Real.sqrt (1 / (1 + r ^ 2)) = |r| := by
  have h : (0 : ℝ) < 1 + r ^ 2 := by positivity
  rw [← Real.sqrt_div (by positivity)]
  have : r ^ 2 / (1 + r ^ 2) / (1 / (1 + r ^ 2)) = r ^ 2 := by field_simp
  rw [this, Real.sqrt_sq_eq_abs]

/-- The reflection (Krein) kernel on coherent tilts. -/
noncomputable def krein (r s : ℝ) : ℝ := Real.sqrt ((1 - r ^ 2) * (1 - s ^ 2)) / (1 + r * s)

theorem krein_symm (r s : ℝ) : krein r s = krein s r := by
  unfold krein
  rw [mul_comm (1 - r ^ 2), mul_comm r]

theorem krein_diag (r : ℝ) (hr : |r| < 1) : krein r r = (1 - r ^ 2) / (1 + r ^ 2) :=
  reflected_purity r hr

/-- **The two-mode reflection Gram determinant is strictly negative.** -/
theorem krein_det_neg (r s : ℝ) (hr : |r| < 1) (hs : |s| < 1) (hne : r ≠ s) :
    krein r r * krein s s - krein r s * krein s r =
        -((1 - r ^ 2) * (1 - s ^ 2) * (r - s) ^ 2) /
          ((1 + r ^ 2) * (1 + s ^ 2) * (1 + r * s) ^ 2) ∧
      krein r r * krein s s - krein r s * krein s r < 0 := by
  have hr2 := one_sub_sq_pos r hr
  have hs2 := one_sub_sq_pos s hs
  have hrs : 0 < 1 + r * s := by
    have h1 : |r * s| < 1 := by
      rw [abs_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg r) hr hs.le
    have := neg_abs_le (r * s)
    linarith
  have h1 : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hdiag_r := krein_diag r hr
  have hdiag_s := krein_diag s hs
  have hoff : krein r s * krein s r = (1 - r ^ 2) * (1 - s ^ 2) / (1 + r * s) ^ 2 := by
    rw [← krein_symm s r, krein, div_mul_div_comm, ← sq (Real.sqrt _),
      Real.sq_sqrt (by positivity)]
    ring
  have key : krein r r * krein s s - krein r s * krein s r =
      -((1 - r ^ 2) * (1 - s ^ 2) * (r - s) ^ 2) /
        ((1 + r ^ 2) * (1 + s ^ 2) * (1 + r * s) ^ 2) := by
    rw [hdiag_r, hdiag_s, hoff]
    field_simp
    ring
  refine ⟨key, ?_⟩
  rw [key]
  have hrs' : (r - s) ^ 2 > 0 := by
    have : r - s ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have : 0 < (1 - r ^ 2) * (1 - s ^ 2) * (r - s) ^ 2 := by positivity
  have hden : 0 < (1 + r ^ 2) * (1 + s ^ 2) * (1 + r * s) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden

end GppSU11Reflection
