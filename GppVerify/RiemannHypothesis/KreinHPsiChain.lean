/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6823553961, "next exact question".

# The chain H_ψ ⇒ RH, Lean-typed: proved links cited by name, the rest named premises

`KreinHPsi.lean` labelled the chain "H_ψ ⇒ RH" as SKETCH. This file makes it exact. The
conclusion is Mathlib's `RiemannHypothesis`. Every link is either a theorem already in the tree
(cited by name) or a named premise `Prop` stated exactly. No premise is proved here.

Links:
1. `HPsi ⇒ AtMostOneNegSq Kpsi` — **PROVED** (`atMostOneNegSq_of_hPsi`): `hPsiEquiv`
   (KreinHPsiWeilData) turns `HPsi` into `HPsiWindows weilData`; `bridge` (KreinBridge) with the
   window fit `tau_fit` (from `fit_translates`, KreinBridge) gives "at most one negative square".
   Here `Kpsi` is the zero-free kernel (pole, primes, Γ) of KreinHPsi; the kernel identity
   `B (τ x) (τ y) = Kψ (x − y)` is the field `WeilData.hK`, not the explicit formula.
2. `AtMostOneNegSq Kpsi ⇒ ∃ Q, deg Q ≤ 1, pole transfer on the zeros` — **named premise**
   `PoleTransfer`. Its paper content: Weil's explicit formula on translates (`hEF`:
   `Kψ(d) = Σ_ρ m_ρ Ψ(γ)Ψ(−γ) e^{iγd}`, CHECKED secondary, NUMERICAL to 1.02e−8) + Krein's
   representation of `P_{≤1}` kernels (CHECKED via Stewart 1972 eq. (2), secondary; the
   Krein–Langer primary is still owed) + the Laplace identity (L) + the growth bound (G1) + the
   identity theorem (CHECKED on paper). NOT proved. `poleTransfer_of_RH` (PROVED) records that
   RH implies it (take `Q = X`), so this premise carries the analytic load of the chain.
3. Symmetries of the zero set `Zgamma` (`ρ = 1/2 + iγ`, `0 < Re ρ < 1`): `γ ↦ −γ` —
   **PROVED** (`Zgamma_neg`, Mathlib `riemannZeta_one_sub`); `γ ↦ −γ̄` — **PROVED**
   (`Zgamma_negconj`, Mathlib `riemannZeta_conj`); no zero on the imaginary `γ`-axis off `0` —
   PROVED from the **named premise** `NoRealZeroStrip` (`ζ(σ) ≠ 0` for real `0 < σ < 1`;
   classical via `(1 − 2^{1−σ}) ζ(σ) = η(σ) > 0`; not proved here).
4. Every `γ ∈ Zgamma` is real — **PROVED** from 1–3 by `tri_RH_of_pole_transfer`
   (KreinLaplaceAssembly) with the triangle `Ψ` (`tri_no_nonreal_zero`).
5. `RiemannHypothesis` — **PROVED** from 4 by `riemannZeta_ne_zero_of_one_le_re` (Mathlib) and
   `riemannHypothesis_of_ne_zero` (OneSidedPsiRH, functional equation).

Final statement: `hPsiChain : HPsi → PoleTransfer → NoRealZeroStrip → RiemannHypothesis`,
PROVED. It is conditional: `HPsi` (H_ψ) is OPEN, `PoleTransfer` and `NoRealZeroStrip` are named
premises. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.KreinHPsiWeilData
import GppVerify.RiemannHypothesis.KreinLaplaceAssembly
import GppVerify.RiemannHypothesis.OneSidedPsiRH

namespace GppKreinHPsiChain

open GppKreinBridge GppKreinHPsi ComplexConjugate

/-! ## Link 1: H_ψ ⇒ at most one negative square (PROVED) -/

/-- Every finite family of triangle translates lies in one windowed space `S_ψ L`. -/
theorem tau_fit (n : ℕ) (x : Fin n → ℝ) : ∃ L, ∀ i, tau (x i) ∈ Spsi L := by
  obtain ⟨L, hL⟩ := fit_translates GppKreinHPsi.triPsi 1
    (fun t ht => triPsi_eq_zero_of_one_le ht.le) n x
  refine ⟨L, fun i => ?_⟩
  show tau (x i) ∈ Fpsi ⊓ window L
  exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨x i, rfl⟩, hL i⟩

/-- **Link 1.** `H_ψ ⇒ Kψ ∈ P_{≤1}(ℝ)`. -/
theorem atMostOneNegSq_of_hPsi (h : HPsi) : AtMostOneNegSq Kpsi :=
  bridge weilData.B Spsi (fun _ => weilData.lc) (fun _ => weilData.ls)
    ((hPsiEquiv weilData).2 h) tau Kpsi weilData.hK tau_fit

/-! ## The zero set in the `γ` variable -/

/-- `ρ(γ) = 1/2 + iγ`. -/
noncomputable def rho (γ : ℂ) : ℂ := 1 / 2 + Complex.I * γ

/-- Zeros of `ζ` in the open critical strip, in the `γ` variable. -/
def Zgamma : Set ℂ := {γ | riemannZeta (rho γ) = 0 ∧ 0 < (rho γ).re ∧ (rho γ).re < 1}

theorem rho_re (γ : ℂ) : (rho γ).re = 1 / 2 - γ.im := by
  simp [rho, Complex.mul_re]; ring

theorem rho_neg (γ : ℂ) : rho (-γ) = 1 - rho γ := by
  unfold rho; ring

theorem rho_negconj (γ : ℂ) : rho (-conj γ) = conj (rho γ) := by
  unfold rho
  simp [map_add, map_mul, Complex.conj_I, map_ofNat]

/-! ## Link 2: named premises (NOT proved) -/

/-- **Named premise (pole transfer).** If `Kψ` has at most one negative square, there is a
nonzero `Q` with `deg Q ≤ 1` such that every zero `γ` with `Im γ < 0` and `Ψ γ ≠ 0` is a root of
`Q` or of `Q̄`. Paper content: hEF + Krein (P_{≤1}) + (L) + (G1) + identity theorem. -/
def PoleTransfer : Prop :=
  AtMostOneNegSq Kpsi → ∃ Q : Polynomial ℂ, Q ≠ 0 ∧ Q.natDegree ≤ 1 ∧
    ∀ γ ∈ Zgamma, γ.im < 0 → GppKreinLaplace.triPsi γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ)

/-- **Named premise.** `ζ` has no real zero in `(0, 1)` (classical; not proved here). -/
def NoRealZeroStrip : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0

/-! ## Link 3: symmetries of `Zgamma` (PROVED) -/

theorem Zgamma_neg {γ : ℂ} (h : γ ∈ Zgamma) : -γ ∈ Zgamma := by
  obtain ⟨hz, h0, h1⟩ := h
  have hn : ∀ n : ℕ, rho γ ≠ -n := fun n hn => by
    have := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1' : rho γ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; linarith
  have hfe := riemannZeta_one_sub hn h1'
  rw [hz, mul_zero] at hfe
  refine ⟨by rw [rho_neg]; exact hfe, ?_, ?_⟩ <;>
    rw [rho_neg, Complex.sub_re, Complex.one_re] <;> linarith

theorem Zgamma_negconj {γ : ℂ} (h : γ ∈ Zgamma) : -conj γ ∈ Zgamma := by
  obtain ⟨hz, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [rho_negconj, riemannZeta_conj, hz, map_zero]
  · rw [rho_negconj, Complex.conj_re]; exact h0
  · rw [rho_negconj, Complex.conj_re]; exact h1

theorem Zgamma_re_ne_zero (hN : NoRealZeroStrip) {γ : ℂ} (h : γ ∈ Zgamma) : γ.re ≠ 0 := by
  intro hre
  obtain ⟨hz, h0, h1⟩ := h
  have hr : rho γ = ((1 / 2 - γ.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [rho, Complex.mul_re, hre]; ring
    · simp [rho, Complex.mul_im, hre]
  rw [rho_re] at h0 h1
  exact hN (1 / 2 - γ.im) h0 h1 (by rw [← hr]; exact hz)

/-! ## Link 4: every zero in the strip is real in `γ` (PROVED from the premises) -/

theorem Zgamma_real (hP : AtMostOneNegSq Kpsi) (hPT : PoleTransfer) (hN : NoRealZeroStrip) :
    ∀ γ ∈ Zgamma, γ.im = 0 := by
  obtain ⟨Q, hQ, hdeg, hpt⟩ := hPT hP
  exact GppKreinLaplace.tri_RH_of_pole_transfer Zgamma Q hQ hdeg (fun _ h => Zgamma_neg h)
    (fun _ h => Zgamma_negconj h) (fun _ h _ => Zgamma_re_ne_zero hN h) hpt

/-! ## Link 5 and the full chain (PROVED, conditional) -/

theorem rho_of_s (s : ℂ) : rho (-Complex.I * (s - 1 / 2)) = s := by
  unfold rho
  linear_combination (-(s - 1 / 2)) * Complex.I_sq

/-- **The chain.** `H_ψ` + pole transfer + no real zero in `(0, 1)` ⇒ `RiemannHypothesis`. -/
theorem riemannHypothesis_of_hPsi (h : HPsi) (hPT : PoleTransfer) (hN : NoRealZeroStrip) :
    RiemannHypothesis := by
  have hZ := Zgamma_real (atMostOneNegSq_of_hPsi h) hPT hN
  refine GppOneSidedRH.riemannHypothesis_of_ne_zero fun s hs hzero => ?_
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hzero
  · have hmem : -Complex.I * (s - 1 / 2) ∈ Zgamma :=
      ⟨by rw [rho_of_s]; exact hzero, by rw [rho_of_s]; linarith, by rw [rho_of_s]; exact h1⟩
    have him := hZ _ hmem
    have hre := rho_re (-Complex.I * (s - 1 / 2))
    rw [rho_of_s, him] at hre
    linarith

/-- The chain as one statement. -/
def HPsiChain : Prop := HPsi → PoleTransfer → NoRealZeroStrip → RiemannHypothesis

theorem hPsiChain : HPsiChain := riemannHypothesis_of_hPsi

/-- **Honesty check.** RH implies `PoleTransfer` (take `Q = X`): the premise is not free. -/
theorem poleTransfer_of_RH (hRH : RiemannHypothesis) : PoleTransfer := by
  intro _
  refine ⟨Polynomial.X, Polynomial.X_ne_zero, by rw [Polynomial.natDegree_X], ?_⟩
  intro γ hγ him _
  exfalso
  obtain ⟨hz, h0, h1⟩ := hγ
  have htriv : ¬∃ n : ℕ, rho γ = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    rw [hn] at h0
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1' : rho γ ≠ 1 := fun e => by rw [e, Complex.one_re] at h1; linarith
  have := hRH (rho γ) hz htriv h1'
  rw [rho_re] at this
  linarith

end GppKreinHPsiChain

#print axioms GppKreinHPsiChain.atMostOneNegSq_of_hPsi
#print axioms GppKreinHPsiChain.Zgamma_neg
#print axioms GppKreinHPsiChain.Zgamma_negconj
#print axioms GppKreinHPsiChain.Zgamma_re_ne_zero
#print axioms GppKreinHPsiChain.Zgamma_real
#print axioms GppKreinHPsiChain.riemannHypothesis_of_hPsi
#print axioms GppKreinHPsiChain.hPsiChain
#print axioms GppKreinHPsiChain.poleTransfer_of_RH
