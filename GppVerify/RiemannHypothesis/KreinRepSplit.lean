/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Heart of the Cosmos (Grok, GPPDiscovery5 seat). Turbo PR #11 6824338259, item 1 (refinement).

# `KreinRep` refined: Krein decomposition + spectral matching

`KreinPoleSplit.lean` stated `KreinRep` as one bundled premise (Krein's representation + (L) +
(G1) + identity theorem). Krein's representation alone does **not** give the root property: the
located extra step is spectral matching (two exponential representations of `Kψ` must share
their lower-half-plane frequencies). This file separates the two.

* `KreinDecomp` (named premise, NOT proved): a `P_{≤1}` kernel `Kψ` is `h + r`, `h` solving
  `Q̄(−i d/dx) Q(−i d/dx) h = 0` for some `Q ≠ 0`, `deg Q ≤ 1` (`ExpPart`, a superset allowing the
  double-root case), and `r` continuous with `|r(d)| ≤ C(1 + d²)` ((G1), `PolyBounded`).
  Paper: Stewart 1972 eq. (2) and Thm 3.4, CHECKED secondary; Krein–Langer primary still owed.
* `SpectralMatching` (named premise, NOT proved): if a multiplicity-weighted exponential zero
  sum with coefficients `a` equals `h + r` as above, every zero `γ`, `Im γ < 0`, `a γ ≠ 0`, is a
  root of `Q` or `Q̄`. Paper: Laplace transforms on `Re s > 1/2` ((L)): the zero sum has a simple
  pole at `iγ` with residue `m_γ a(γ) ≠ 0`; `h` has poles only at `iβ, iβ̄`; `r` is analytic on
  `Re s > 0`; identity theorem. CHECKED on paper.

PROVED: `kreinRep_of_decomp_matching : KreinDecomp → SpectralMatching → KreinRep`, honesty
check `spectralMatching_of_RH`, and the chain
`hPsiFineChain : HPsi → HEF → KreinDecomp → SpectralMatching → RiemannHypothesis`
(`NoRealZeroStrip` discharged by `GppNoRealZeroStrip.noRealZeroStrip`).
Converses are not claimed. H_ψ: OPEN. ARP: OPEN. RH: OPEN.
-/
import GppVerify.RiemannHypothesis.NoRealZeroStrip

namespace GppKreinRepSplit

open GppKreinBridge GppKreinHPsi GppKreinHPsiChain GppKreinPoleSplit ComplexConjugate

/-- Solutions of `Q̄(−i d/dx) Q(−i d/dx) h = 0` for `deg Q ≤ 1` (superset allowing a double
root): zero, or quasi-exponentials at a root `β` of `Q` and at `β̄`. -/
def ExpPart (Q : Polynomial ℂ) (h : ℝ → ℂ) : Prop :=
  h = 0 ∨ ∃ β : ℂ, Q.IsRoot β ∧ ∃ c₀ c₁ c₂ c₃ : ℂ, ∀ d : ℝ,
    h d = (c₀ + c₁ * d) * Complex.exp (Complex.I * β * d) +
      (c₂ + c₃ * d) * Complex.exp (Complex.I * conj β * d)

/-- At most quadratic growth: the (G1) bound on Krein's integral term. -/
def PolyBounded (r : ℝ → ℂ) : Prop := ∃ C : ℝ, ∀ d : ℝ, ‖r d‖ ≤ C * (1 + d ^ 2)

/-- **Named premise `KreinDecomp`** (Krein's representation + (G1)). -/
def KreinDecomp : Prop :=
  AtMostOneNegSq Kpsi → ∃ Q : Polynomial ℂ, Q ≠ 0 ∧ Q.natDegree ≤ 1 ∧
    ∃ h r : ℝ → ℂ, ExpPart Q h ∧ Continuous r ∧ PolyBounded r ∧
      ∀ d : ℝ, ((Kpsi d : ℝ) : ℂ) = h d + r d

/-- **Named premise `SpectralMatching`** ((L) + identity theorem). -/
def SpectralMatching : Prop :=
  ∀ (a : ℂ → ℂ) (Q : Polynomial ℂ) (h r : ℝ → ℂ), Q ≠ 0 → Q.natDegree ≤ 1 → ExpPart Q h →
    Continuous r → PolyBounded r →
    (∀ d : ℝ, ZeroSummable (fun γ => a γ * expTerm d γ) ∧
      zeroSum (fun γ => a γ * expTerm d γ) = h d + r d) →
    ∀ γ ∈ Zgamma, γ.im < 0 → a γ ≠ 0 → Q.IsRoot γ ∨ Q.IsRoot (conj γ)

/-- **Recombination.** `KreinDecomp → SpectralMatching → KreinRep` (this direction only). -/
theorem kreinRep_of_decomp_matching (hD : KreinDecomp) (hM : SpectralMatching) : KreinRep := by
  intro a hexp hP
  obtain ⟨Q, hQ, hdeg, h, r, hh, hrc, hrb, hrep⟩ := hD hP
  exact ⟨Q, hQ, hdeg, hM a Q h r hQ hdeg hh hrc hrb
    fun d => ⟨(hexp d).1, (hexp d).2.symm.trans (hrep d)⟩⟩

/-- Under RH no zero of the strip has `Im γ < 0`. -/
theorem no_lower_zero_of_RH (hRH : RiemannHypothesis) {γ : ℂ} (hγ : γ ∈ Zgamma)
    (him : γ.im < 0) : False := by
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

/-- **Honesty check.** RH implies `SpectralMatching` (no lower zeros): the premise is not free. -/
theorem spectralMatching_of_RH (hRH : RiemannHypothesis) : SpectralMatching := by
  intro _ _ _ _ _ _ _ _ _ _ γ hγ him _
  exact (no_lower_zero_of_RH hRH hγ him).elim

/-- The chain with the finer split and `NoRealZeroStrip` discharged. -/
def HPsiFineChain : Prop := HPsi → HEF → KreinDecomp → SpectralMatching → RiemannHypothesis

theorem hPsiFineChain : HPsiFineChain := fun h hE hD hM =>
  GppNoRealZeroStrip.hPsiReducedChain h hE (kreinRep_of_decomp_matching hD hM)

end GppKreinRepSplit

#print axioms GppKreinRepSplit.kreinRep_of_decomp_matching
#print axioms GppKreinRepSplit.no_lower_zero_of_RH
#print axioms GppKreinRepSplit.spectralMatching_of_RH
#print axioms GppKreinRepSplit.hPsiFineChain
