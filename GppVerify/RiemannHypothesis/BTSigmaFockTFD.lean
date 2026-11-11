import GppVerify.RiemannHypothesis.BTSigmaLocalEuler

/-!
# BT-Σ, Fock direction: the local primon-gas purification of the vertex law

Port of GPPDiscovery5 `26184cb` (`lean/bt-sigma/BTSigmaFockTFD.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6802112580 §4: local Fock provenance PROVED, all 9 theorems standard
axioms; port requested as a module, scope header verbatim, no claim beyond diagonal weights).
Original task: comment 6801675837 §(b), exhibit the Fock construction or name its failing step.

**Space.** One bosonic mode per prime: `Γ_s(ℂ) ≅ ℓ²(ℕ)` with number operator `N`, and its
double `Γ_s(ℂ) ⊗ Γ_s(ℂ)`. The second-quantised vertex law at the unitary point is
`Γ(U_p(1/2)) = p^{-N/2} = q^N`, `q = p^{-1/2}`.

**Exponential vector.** `Ψ_p = exp(√q a†b†) Ω = Σ_n q^{n/2} |n⟩ ⊗ |n⟩` (the purification of
`q^N`). Its Fock norm is the Euler factor, `‖Ψ_p‖² = Σ_n q^n = L_p(1/2)` (`fockNorm_hasSum`), and
the `1/j` comes from the logarithm of this norm, `log ‖Ψ_p‖² = Σ_j q^j / j`
(`log_fockNorm_hasSum`). No `κ_p` and no `1/j` is put into any amplitude.

**Jump, computed.** In the unit vector `Ψ̂_p = Ψ_p / ‖Ψ_p‖` the occupation law is
`π_n = (1 − q) q^n` (`tfdWeight`, `tfdWeight_hasSum`). With the cut observable
`C_m = S^m H S^{*m} ⊗ 1`, `H = (log p) N`, `S` the isometric shift (diagonal value
`log p · (n − m)₊`, `cutObs`), the jump across the `(m+1)`-st cut is the projection
`log p · 1[N ≥ m+1]` (`cutObs_jump`), and its expectation in `Ψ̂_p` is exactly the cut weight
`Λ(p^{m+1})(p^{m+1})^{-1/2}` (`tfd_cut_jump`). The uncut energy is `κ_p` (`tfd_energy`):
the coupling is computed as the Gibbs energy at `s = 1/2`, not inserted. These are
sesquilinear (vector-state) matrix elements, so this route is outside the class refuted by
(V3): the cross term is `C_m = κ_p q^m` with `κ_p` produced by the state.

All of the above is PROVED (standard axioms). What it is **not**:
* the jump is a vector-state matrix element in the per-prime Fock space, not yet the Green-form
  trace jump of `T* = −i d/du` on `L²(ℝ; K ⊗ ⊕_p V_p)`: the embedding into the boundary triplet,
  with (P-COV) and (P-UNIT), is OPEN;
* globally the product `⊗_p Ψ̂_p` is the primon gas at inverse temperature `1/2`, below the
  Hagedorn point `1`: `∏_p ‖Ψ_p‖² = ζ(1/2)`-Euler product and `Σ_p κ_p` both diverge, which is
  the same growth as (P-LIM) (no-go 2). Local provenance does not give the limit.
(P-LOG) as an (NC2) provenance claim for the BT-Σ triplet, (P-θ), (P-LIM), (BT-Σ), ARP and RH
remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaFockTFD

open GppBTSigmaLocalEuler GppBTSigmaC1 ArithmeticFunction

theorem qp_lt_one {p : ℕ} (hp : 1 < p) : qp p < 1 := by
  unfold qp
  exact inv_lt_one_of_one_lt₀ (one_lt_sqrt hp)

theorem localFactor_half (p : ℕ) : localFactor p (1 / 2) = (1 - qp p)⁻¹ := by
  rw [localFactor, qp_eq_rpow]

/-- `‖Ψ_p‖² = Σ_n q^n = L_p(1/2)`. PROVED. -/
theorem fockNorm_hasSum {p : ℕ} (hp : 1 < p) :
    HasSum (fun n : ℕ => qp p ^ n) (localFactor p (1 / 2)) := by
  rw [localFactor_half]
  exact hasSum_geometric_of_lt_one (qp_pos hp).le (qp_lt_one hp)

/-- `log ‖Ψ_p‖² = Σ_{j ≥ 1} q^j / j`: the `1/j` is the log of the Fock norm. PROVED. -/
theorem log_fockNorm_hasSum {p : ℕ} (hp : 1 < p) :
    HasSum (fun j : ℕ => qp p ^ (j + 1) / (j + 1)) (Real.log (localFactor p (1 / 2))) := by
  rw [localFactor_half, Real.log_inv]
  have h : |qp p| < 1 := by rw [abs_of_pos (qp_pos hp)]; exact qp_lt_one hp
  exact Real.hasSum_pow_div_log_of_abs_lt_one h

/-- Occupation law of the unit vector `Ψ̂_p`: `π_n = (1 − q) q^n`. -/
noncomputable def tfdWeight (p n : ℕ) : ℝ := (1 - qp p) * qp p ^ n

theorem tfdWeight_hasSum {p : ℕ} (hp : 1 < p) : HasSum (tfdWeight p) 1 := by
  have h := (hasSum_geometric_of_lt_one (qp_pos hp).le (qp_lt_one hp)).mul_left (1 - qp p)
  have hne : 1 - qp p ≠ 0 := by linarith [qp_lt_one hp]
  rwa [mul_inv_cancel₀ hne] at h

/-- `⟨Ψ̂_p, 1[N ≥ j] Ψ̂_p⟩ = q^j`. PROVED. -/
theorem tail_prob {p : ℕ} (hp : 1 < p) (j : ℕ) :
    HasSum (fun n => if j ≤ n then tfdWeight p n else 0) (qp p ^ j) := by
  refine (hasSum_nat_add_iff' j).mp ?_
  have hz : ∑ i ∈ Finset.range j, (if j ≤ i then tfdWeight p i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [show ¬ j ≤ i by omega]
  rw [hz, sub_zero]
  have h := (tfdWeight_hasSum hp).mul_left (qp p ^ j)
  rw [mul_one] at h
  have e : (fun n => if j ≤ n + j then tfdWeight p (n + j) else 0) =
      fun n => qp p ^ j * tfdWeight p n := by
    funext n
    simp only [show j ≤ n + j by omega, if_true, tfdWeight]
    ring
  rw [e]
  exact h

/-- Diagonal value of the cut observable `S^m H S^{*m}`: `log p · (n − m)₊`. -/
noncomputable def cutObs (p m n : ℕ) : ℝ := Real.log p * ((n - m : ℕ) : ℝ)

/-- The jump of the cut observable is the projection `log p · 1[N ≥ m+1]`. PROVED. -/
theorem cutObs_jump (p m n : ℕ) :
    cutObs p m n - cutObs p (m + 1) n = if m + 1 ≤ n then Real.log p else 0 := by
  unfold cutObs
  split_ifs with h
  · have : n - m = (n - (m + 1)) + 1 := by omega
    rw [this]; push_cast; ring
  · rw [show n - m = 0 by omega, show n - (m + 1) = 0 by omega]; simp

/-- **Jump, computed.** The expectation of the cut jump in `Ψ̂_p` is the cut weight
`Λ(p^{m+1})(p^{m+1})^{-1/2}`. No coupling and no `1/j` inserted. PROVED. -/
theorem tfd_cut_jump {p : ℕ} (hp : p.Prime) (m : ℕ) :
    HasSum (fun n => tfdWeight p n * (cutObs p m n - cutObs p (m + 1) n))
      (halfWeight (p ^ (m + 1))) := by
  rw [halfWeight_primePow hp (by omega)]
  have h := (tail_prob hp.one_lt (m + 1)).mul_left (Real.log p)
  have e : (fun n => tfdWeight p n * (cutObs p m n - cutObs p (m + 1) n)) =
      fun n => Real.log p * if m + 1 ≤ n then tfdWeight p n else 0 := by
    funext n
    rw [cutObs_jump]
    split_ifs <;> ring
  rw [e]
  exact h

/-- **The coupling is the Gibbs energy.** `⟨Ψ̂_p, H Ψ̂_p⟩ = κ_p`. PROVED. -/
theorem tfd_energy {p : ℕ} (hp : 1 < p) :
    HasSum (fun n => tfdWeight p n * cutObs p 0 n) (kappa p) := by
  have hq0 := qp_pos hp
  have hq1 := qp_lt_one hp
  have hn : ‖qp p‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left ((1 - qp p) * Real.log p)
  have hne : 1 - qp p ≠ 0 := by linarith
  have hsq : Real.sqrt p * qp p = 1 := mul_inv_cancel₀ (sqrt_ne_zero' hp)
  have hne2 : Real.sqrt p - 1 ≠ 0 := by linarith [one_lt_sqrt hp]
  have hk : (1 - qp p) * Real.log p * (qp p / (1 - qp p) ^ 2) = kappa p := by
    rw [show kappa p = Real.log p / (Real.sqrt p - 1) from rfl]
    field_simp
    linear_combination (Real.log p) * hsq
  rw [hk] at h
  have e : (fun n => tfdWeight p n * cutObs p 0 n) =
      fun i : ℕ => (1 - qp p) * Real.log p * ((i : ℝ) * qp p ^ i) := by
    funext n
    simp only [tfdWeight, cutObs, Nat.sub_zero]
    ring
  rw [e]
  exact h

end GppBTSigmaFockTFD
