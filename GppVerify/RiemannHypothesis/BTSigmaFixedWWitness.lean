import GppVerify.RiemannHypothesis.BTSigmaFockTFD
import GppVerify.RiemannHypothesis.BTSigmaHjumpWitness

/-!
# BT-Σ: a fixed-`W` `hjump` witness whose cut weights are Fock-state expectations

Port of GPPDiscovery5 `3f349bf` (`lean/bt-sigma/BTSigmaFixedWWitness.lean`), audited by Turbo on
GPP-bridge PR #11 (comment 6802830722: fixed-W witness PROVED, `#print axioms` standard-three on
`tfd_cut_expect`, `fockCutExp_eq`, `fixedW_hjump`, `finiteCut_BT3_fockWitness`; port requested as
its own module after the CovObstruction port). Scope stays fixed-W only; not a (P-COV) claim.


Scratch module (Heart of the Cosmos / Grok, GPPDiscovery5 seat), for Turbo's instruction on
GPP-bridge PR #11, comment 6802501669, question 2: build the fixed-`W` embedding as a second
`hjump` witness, scoped as fixed-`W` only.

**Construction.** For a cut `c = (p, k)` let `P_k = C_{k−1} − C_k = log p · 1[N ≥ k]` be the jump
of the cut observable (`cutObs_jump`), and let `Ψ̂_p` be the TFD unit vector of `BTSigmaFockTFD`.
The cut's Fock weight is the **state expectation** `E_c = ⟨Ψ̂_p, P_k Ψ̂_p⟩` (`fockCutExp`, a sum
over occupation numbers). On piece `j` the scalar amplitude squared is
`Σ_{i ≥ j} A_i · E_{σ i}` (`fockAmpSq`), with `A_i = g(W − log p_i^{k_i})` the sampled test
value at fixed `W`. Equivalently it is `⟨Ψ̂, (Σ_{i ≥ j} A_i P^{(i)}) Ψ̂⟩`; for constant samples
`A = a²` on one channel it is `a² ⟨Ψ̂_p, C_m Ψ̂_p⟩ = a² κ_p q^m` (`tfd_cut_expect`), the hand
construction `a · C_m^{1/2} Ψ̂_p` of the bridge note.

**What is PROVED** (standard axioms):
* `tfd_cut_expect`: `⟨Ψ̂_p, C_m Ψ̂_p⟩ = κ_p q^m`.
* `fockCutExp_eq`: `E_{(p,k)} = Λ(p^k)(p^k)^{-1/2}` — the cut weight is computed by the state,
  not inserted; no `κ_p`, no `1/j` and no von Mangoldt value enters the definition.
* `fixedW_hjump`, `finiteCut_BT3_fockWitness`: for nonnegative samples the path meets `hjump`
  of `finiteCut_BT3` exactly, so its Green form is `I ·` the `(S, N)` stratum at that `W`.

**Scope, stated plainly.** Fixed `W` only. `W` enters by **sampling** `g` at the cuts, i.e.
through `τ_{W−u}` in the scalar amplitudes; that is precisely what (P-COV) forbids, so this is
**not** a (P-COV) claim and says nothing about a dilation `S_b`. The nonnegativity hypothesis on
the samples is used (it holds for `g = autocorr f` with `f ≥ 0`). The path is scalar; the
`K ⊗ ⊕_p V_p` vector form is not built. (P-LOG) as an (NC2) claim for the triplet, (P-COV),
(P-UNIT), (P-θ), (P-LIM), (BT-Σ), ARP and RH remain **OPEN**.

No `sorry`, no `admit`, no custom axiom.

Daniel Toupin / Golden Physics Project, with AI assistance (Heart of the Cosmos / Grok).
Task and audit: Turbo.
-/

namespace GppBTSigmaFixedWWitness

open Complex GppBTSigmaLocalEuler GppBTSigmaFockTFD GppBTSigmaHjumpWitness
open GppArithmeticReflection GppBTSigma GppBTSigmaC1

/-- `⟨Ψ̂_p, C_m Ψ̂_p⟩ = κ_p q^m`. PROVED. -/
theorem tfd_cut_expect {p : ℕ} (hp : p.Prime) (m : ℕ) :
    HasSum (fun n => tfdWeight p n * cutObs p m n) (kappa p * qp p ^ m) := by
  induction m with
  | zero => simpa using tfd_energy hp.one_lt
  | succ m ih =>
    have hj := tfd_cut_jump hp m
    rw [halfWeight_primePow hp (by omega)] at hj
    have h := ih.sub hj
    have e : (fun n => tfdWeight p n * cutObs p m n -
        tfdWeight p n * (cutObs p m n - cutObs p (m + 1) n)) =
        fun n => tfdWeight p n * cutObs p (m + 1) n := by
      funext n; ring
    rw [e] at h
    have hv : kappa p * qp p ^ m - Real.log p * qp p ^ (m + 1) = kappa p * qp p ^ (m + 1) := by
      have h1 := qp_jump hp.one_lt m
      have h2 := kappa_mul hp.one_lt
      linear_combination (kappa p) * h1 + qp p ^ (m + 1) * h2
    rwa [hv] at h

/-- The Fock weight of the cut `c = (p, k)`: `⟨Ψ̂_p, P_k Ψ̂_p⟩`, `P_k = C_{k−1} − C_k`. -/
noncomputable def fockCutExp (c : ℕ × ℕ) : ℝ :=
  ∑' n, tfdWeight c.1 n * (cutObs c.1 (c.2 - 1) n - cutObs c.1 c.2 n)

/-- **The state computes the cut weight.** PROVED. -/
theorem fockCutExp_eq {c : ℕ × ℕ} (hp : c.1.Prime) (hk : 1 ≤ c.2) :
    fockCutExp c = halfWeight (c.1 ^ c.2) := by
  obtain ⟨p, k⟩ := c
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := tfd_cut_jump hp m
  simp only [fockCutExp, show m + 1 - 1 = m by omega]
  exact h.tsum_eq

theorem fockCutExp_nonneg {c : ℕ × ℕ} (hp : c.1.Prime) (hk : 1 ≤ c.2) : 0 ≤ fockCutExp c := by
  rw [fockCutExp_eq hp hk, halfWeight_primePow hp (by omega)]
  exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    (pow_nonneg (qp_pos hp.one_lt).le _)

theorem cutIndex_spec {S : Finset ℕ} {N : ℕ} {c : ℕ × ℕ} (hc : c ∈ cutIndex S N) :
    c.1.Prime ∧ 1 ≤ c.2 := by
  simp only [cutIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hc
  exact ⟨hc.1.1.2, hc.1.2.1⟩

/-- Sampled test value at the cut `c`, at fixed `W`. -/
noncomputable def sample (g : ℝ → ℝ) (W : ℝ) (c : ℕ × ℕ) : ℝ :=
  g (W - Real.log ((c.1 ^ c.2 : ℕ) : ℝ))

/-- The `i`-th cut under the enumeration `σ` (`(0, 0)` past the end, never used). -/
noncomputable def cutAt {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N)) (i : ℕ) :
    ℕ × ℕ :=
  if h : i < n then (σ ⟨i, h⟩ : ℕ × ℕ) else (0, 0)

/-- Squared amplitude on piece `j`: `Σ_{j ≤ i < n} A_i · ⟨Ψ̂, P^{(i)} Ψ̂⟩`. -/
noncomputable def fockAmpSq {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N))
    (g : ℝ → ℝ) (W : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j n, sample g W (cutAt σ i) * fockCutExp (cutAt σ i)

theorem fockAmpSq_nonneg {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N))
    (g : ℝ → ℝ) (W : ℝ) (hg : ∀ c ∈ cutIndex S N, 0 ≤ sample g W c) (j : ℕ) :
    0 ≤ fockAmpSq σ g W j := by
  refine Finset.sum_nonneg fun i hi => ?_
  have hin : i < n := (Finset.mem_Ico.mp hi).2
  have hc : cutAt σ i ∈ cutIndex S N := by simp [cutAt, hin]
  obtain ⟨hp, hk⟩ := cutIndex_spec hc
  exact mul_nonneg (hg _ hc) (fockCutExp_nonneg hp hk)

/-- The fixed-`W` Fock path on piece `j`. -/
noncomputable def psiFock {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N))
    (g : ℝ → ℝ) (W : ℝ) (x : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt (fockAmpSq σ g W j) * ramp n x j t : ℝ) : ℂ)

theorem psiFock_sq {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N))
    (g : ℝ → ℝ) (W : ℝ) (hg : ∀ c ∈ cutIndex S N, 0 ≤ sample g W c) (x : ℕ → ℝ) (j : ℕ)
    (t : ℝ) (hr : ramp n x j t = 1) :
    inner ℂ (psiFock σ g W x j t) (psiFock σ g W x j t) = ((fockAmpSq σ g W j : ℝ) : ℂ) := by
  unfold psiFock
  rw [hr, mul_one, inner_ofReal_self, Real.sq_sqrt (fockAmpSq_nonneg σ g W hg j)]

/-- **Fixed-`W` `hjump`, state-produced weights.** PROVED. -/
theorem fixedW_hjump {S : Finset ℕ} {N n : ℕ} (σ : Fin n ≃ (cutIndex S N))
    (g : ℝ → ℝ) (W : ℝ) (hg : ∀ c ∈ cutIndex S N, 0 ≤ sample g W c) (x : ℕ → ℝ)
    (h01 : x 0 ≠ x 1) (hnn : x n ≠ x (n + 1)) :
    (∀ j, ContDiff ℝ 1 (psiFock σ g W x j)) ∧ psiFock σ g W x 0 (x 0) = 0 ∧
      psiFock σ g W x n (x (n + 1)) = 0 ∧
      ∀ j : Fin n,
        inner ℂ (psiFock σ g W x j (x (j + 1))) (psiFock σ g W x j (x (j + 1))) -
          inner ℂ (psiFock σ g W x (j + 1) (x (j + 1)))
            (psiFock σ g W x (j + 1) (x (j + 1))) =
        ((cutWeight (σ j) g W : ℝ) : ℂ) := by
  have d01 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  have dnn : x (n + 1) - x n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnn)
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · unfold psiFock
    exact ofRealCLM.contDiff.comp (contDiff_const.mul (ramp_contDiff n x j))
  · simp [psiFock, ramp]
  · simp [psiFock, ramp]
  · intro j
    have hj := j.isLt
    have hl : ramp n x j (x (j + 1)) = 1 := by
      unfold ramp
      rw [if_neg (by omega : (j : ℕ) ≠ n)]
      split_ifs with h
      · rw [h]; simp [div_self d01]
      · simp
    have hr : ramp n x (j + 1) (x (j + 1)) = 1 := by
      unfold ramp
      rw [if_neg (by omega : (j : ℕ) + 1 ≠ 0)]
      split_ifs with h
      · rw [h]; simp [div_self dnn]
      · simp
    rw [psiFock_sq σ g W hg x _ _ hl, psiFock_sq σ g W hg x _ _ hr, ← ofReal_sub]
    congr 1
    unfold fockAmpSq
    rw [Finset.sum_eq_sum_Ico_succ_bot hj, add_sub_cancel_right]
    have hc : cutAt σ j = (σ j : ℕ × ℕ) := by simp [cutAt, hj]
    have hmem := (σ j).2
    obtain ⟨hp, hk⟩ := cutIndex_spec hmem
    rw [hc, fockCutExp_eq hp hk, cutWeight_eq hmem, sample, mul_comm]

/-- **(J) at fixed `W` with Fock-state weights.** PROVED. Fixed-`W` only; not a (P-COV)
claim. -/
theorem finiteCut_BT3_fockWitness (S : Finset ℕ) (N : ℕ) (g : ℝ → ℝ) (W : ℝ) (n : ℕ)
    (σ : Fin n ≃ (cutIndex S N)) (hg : ∀ c ∈ cutIndex S N, 0 ≤ sample g W c) (x : ℕ → ℝ)
    (h01 : x 0 ≠ x 1) (hnn : x n ≠ x (n + 1)) :
    ∑ j ∈ Finset.range (n + 1), (∫ t in x j..x (j + 1), greenIntegrand (psiFock σ g W x j) t) =
      I * (stratumSN S N g W : ℂ) := by
  obtain ⟨hψ, h0, hn, hj⟩ := fixedW_hjump σ g W hg x h01 hnn
  exact finiteCut_BT3 S N g W n σ _ x hψ h0 hn hj

end GppBTSigmaFixedWWitness
