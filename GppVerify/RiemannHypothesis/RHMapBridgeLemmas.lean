import Mathlib.Analysis.Matrix.Order

/-!
# Elementary bridging lemmas from the unified RH map

Source: Claude (chat seat), GPP-bridge `CLAUDE_RH_MAP.md` §5, closed by a tactic sweep at the pinned
Mathlib (GPPDiscovery `lean_sweep/`).  Each statement is a small exact fact used by one of the RH routes:

* `fejer_nonneg`: the fixed-window weight `ℓ (sin(ℓγ/2)/(ℓγ/2))²` is nonnegative;
* `H_tail_identity`: `(2(cosh(ℓr) − 1)/(ℓ r²)) e^{−ℓr} = (1 − e^{−ℓr})²/(ℓ r²)` (the dyadic tail form);
* `two_box_algebra`: `‖f − g‖² = 2(‖f‖² − ⟨f,g⟩)` when `‖g‖ = ‖f‖` (the two-box energy);
* `cos_sum_le`: `Σ a_k cos(γ_k t) ≤ Σ a_k` for `a_k ≥ 0` (the on-line zero sum is bounded by `C(0)`);
* `unit_norm_one`, `unit_primes_235`: the golden-gain norm and the primes `p` with `(p−1) ∣ 4`, namely `2, 3, 5`;
* `growth_real_positive_coeffs`: positive coefficients and a one-sided bound on `Σ c_k e^{l_k s}` force every real `l_k ≤ 0`
  (the Landau real-axis step for a finite exponential sum);
* `residue_weight_identity`: `(L/π²) sin²(πt) = t² · L (sin(Lγ/2)/(Lγ/2))²` with `γ = 2πt/L`, the exact link
  between the CCM residue weight and the fixed-window weight;
* `hadamard_psd`: the Schur product of two positive semidefinite real matrices is positive semidefinite.

## Scope

Elementary algebra and analysis only.  Nothing here locates a zero of zeta and there is no RH claim.
-/

namespace GppRHMapBridge


theorem fejer_nonneg (l γ : ℝ) (hl : 0 ≤ l) : 0 ≤ l * (Real.sin (l * γ / 2) / (l * γ / 2)) ^ 2 := by
  positivity

theorem H_tail_identity (l r : ℝ) (hl : 0 < l) (hr : 0 < r) : (2 * (Real.cosh (l * r) - 1) / (l * r ^ 2)) * Real.exp (-(l * r)) = (1 - Real.exp (-(l * r))) ^ 2 / (l * r ^ 2) := by
  rw [Real.cosh_eq]
  have he : Real.exp (l * r) * Real.exp (-(l * r)) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith [he]

theorem two_box_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f g : E) (h : ‖g‖ = ‖f‖) : ‖f - g‖ ^ 2 = 2 * (‖f‖ ^ 2 - inner ℝ f g) := by
  rw [norm_sub_sq_real, h]; ring

theorem cos_sum_le (n : ℕ) (a γ : Fin n → ℝ) (t : ℝ) (ha : ∀ k, 0 ≤ a k) : ∑ k, a k * Real.cos (γ k * t) ≤ ∑ k, a k := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_of_le_one_right (ha k) (Real.cos_le_one _)

theorem unit_norm_one (p : ℝ) (hp : 0 ≤ p) : (p + 1 + 2 * Real.sqrt p) * (p + 1 - 2 * Real.sqrt p) = (p - 1) ^ 2 := by
  have := Real.sq_sqrt hp
  nlinarith [this]

theorem unit_primes_235 (p : ℕ) (hp : p.Prime) : (p - 1) ∣ 4 ↔ p = 2 ∨ p = 3 ∨ p = 5 := by
  constructor
  · intro h
    have h1 : p - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) h
    have h2 : 2 ≤ p := hp.two_le
    have h3 : p ≤ 5 := by omega
    interval_cases p <;> first | omega | (exfalso; revert hp; decide) | (revert h; decide)
  · rintro (rfl | rfl | rfl) <;> decide

theorem growth_real_positive_coeffs (n : ℕ) (c l : Fin n → ℝ) (M : ℝ) (hc : ∀ k, 0 < c k) (hM : ∀ s : ℝ, 0 ≤ s → ∑ k, c k * Real.exp (l k * s) ≤ M) : ∀ k, l k ≤ 0 := by
  intro k
  by_contra hpos
  rw [not_le] at hpos
  have hle : ∀ s : ℝ, 0 ≤ s → c k * Real.exp (l k * s) ≤ M := by
    intro s hs
    refine le_trans ?_ (hM s hs)
    exact Finset.single_le_sum (f := fun j => c j * Real.exp (l j * s)) (fun j _ => by have := hc j; positivity) (Finset.mem_univ k)
  set s := (|M| / c k) / l k with hsdef
  have hs0 : 0 ≤ s := by have := hc k; positivity
  have h1 := hle s hs0
  have h2 : l k * s = |M| / c k := by rw [hsdef]; field_simp
  rw [h2] at h1
  have h3 := Real.add_one_le_exp (|M| / c k)
  have hck := hc k
  have h4 : c k * (|M| / c k + 1) ≤ c k * Real.exp (|M| / c k) := mul_le_mul_of_nonneg_left h3 hck.le
  have h5 : c k * (|M| / c k + 1) = |M| + c k := by field_simp
  have := le_abs_self M
  linarith

theorem residue_weight_identity (L t : ℝ) (hL : L ≠ 0) (ht : t ≠ 0) : L / Real.pi ^ 2 * Real.sin (Real.pi * t) ^ 2 = t ^ 2 * (L * (Real.sin (L * (2 * Real.pi * t / L) / 2) / (L * (2 * Real.pi * t / L) / 2)) ^ 2) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : L * (2 * Real.pi * t / L) / 2 = Real.pi * t := by field_simp
  rw [h]
  field_simp

theorem hadamard_psd (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) : (A.hadamard B).PosSemidef := by
  exact hA.hadamard hB

end GppRHMapBridge
