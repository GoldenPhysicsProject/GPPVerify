/-
Copyright (c) 2026 GoldenPhysicsProject. Released under the project license.
Daniel Toupin / Golden Physics Project. This seat: Heart of the Cosmos / Grok (GPPDiscovery5).
Audit: Turbo. Branch heart/weilgram (based on heart/hpsi-plan 20050db).

# WeilIsGram, semilocal form: H_ψ is exactly the S-local Weil positivity on matched windows

Connes' semilocal picture (Selecta Math. 5 (1999), S-local trace formula) works with a finite set
`S` of places and keeps only the primes `p ∈ S`. For the triangle test function `g = ψ ⋆ ψ`
(support `[−2, 2]`), a window-`L` configuration only evaluates `Kψ(d)` at `|d| ≤ L`, where only
`n < e^{2+L}` contribute. So the semilocal kernel `KS S` with `S ⊇ {p < e^{2+L}}` agrees with `Kψ`
on the window, and the `S → ∞` limit is reached at a finite stage: there is no separate
uniformity-in-`S` problem for a fixed window (PROVED below, `kS_eq_Kpsi`).

* PROVED: `primeTermS_eq`, `kS_eq_Kpsi` (semilocal stabilisation), `hPsiWindow_iff_semilocalPos`,
  `hPsi_of_allWindows`, `hPsi_iff_semilocalWeilIsGram`.
* Named Prop (OPEN, RH-strength, *equivalent* to H_ψ): `SemilocalWeilIsGram` — for every `L > 0`,
  positivity of the `S_L`-local Weil form on window-`L` configurations in `ker ℓ_c`, where
  `S_L = {p prime : p < e^{2+L}}`.

So all RH-strength content of WeilIsGram sits in `SemilocalWeilIsGram`; nothing is reduced to a
known theorem here. Connes' S-local trace formula is a theorem (literature, CHECKED) but it is an
identity, not a positivity statement; its positivity after cutoff is equivalent to RH.
H_ψ, ARP, RH: OPEN.
-/
import GppVerify.RiemannHypothesis.HPsiPlan

namespace GppWeilGram

open GppKreinBridge GppKreinHPsi GppHPsiPlan

/-- Prime term restricted to the finite set of primes `S` (`n` kept iff `n.minFac ∈ S`; since
`Λ(n) ≠ 0` only at prime powers, this keeps exactly the powers of primes in `S`). -/
noncomputable def primeTermS (S : Finset ℕ) (d : ℝ) : ℝ :=
  ∑' n : ℕ, if n.minFac ∈ S then ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (triG (Real.log n + d) + triG (-Real.log n + d)) else 0

/-- The `S`-local translate kernel: pole − `S`-primes + archimedean. -/
noncomputable def KS (S : Finset ℕ) (d : ℝ) : ℝ := poleTerm d - primeTermS S d + archTerm d

/-- `S` contains every prime `p < e^{2+L}`. -/
def Covers (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) < Real.exp (2 + L) → p ∈ S

/-- The matched finite set `S_L = {p prime : p < e^{2+L}}`. -/
noncomputable def primesBelowExp (L : ℝ) : Finset ℕ :=
  (Finset.range ⌈Real.exp (2 + L)⌉₊).filter Nat.Prime

theorem covers_primesBelowExp (L : ℝ) : Covers (primesBelowExp L) L := by
  intro p hp hlt
  simp only [primesBelowExp, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_ceil.mpr hlt, hp⟩

/-- **PROVED**: on `|d| ≤ L`, the `S`-local prime term equals the full prime term once `S` covers
`L`. -/
theorem primeTermS_eq {S : Finset ℕ} {L : ℝ} (hS : Covers S L) {d : ℝ} (hd : |d| ≤ L) :
    primeTermS S d = primeTerm d := by
  unfold primeTermS primeTerm
  refine tsum_congr fun n => ?_
  split_ifs with h
  · rfl
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
      have hge : Real.exp (2 + L) ≤ (n.minFac : ℝ) := by
        by_contra hlt
        exact h (hS _ hp (lt_of_not_ge hlt))
      have hn' : Real.exp (2 + L) ≤ (n : ℝ) := hge.trans (by exact_mod_cast hle)
      have hlog : 2 + L ≤ Real.log n := by
        have := Real.log_le_log (Real.exp_pos _) hn'
        rwa [Real.log_exp] at this
      have hd1 := neg_abs_le d
      have hd2 := le_abs_self d
      have h1 : triG (Real.log n + d) = 0 :=
        triG_eq_zero (le_abs.mpr (Or.inl (by linarith)))
      have h2 : triG (-Real.log n + d) = 0 :=
        triG_eq_zero (le_abs.mpr (Or.inr (by linarith)))
      rw [h1, h2]
      ring

/-- **PROVED (semilocal stabilisation)**: `KS S = Kψ` on the window `|d| ≤ L` when `S` covers `L`. -/
theorem kS_eq_Kpsi {S : Finset ℕ} {L : ℝ} (hS : Covers S L) {d : ℝ} (hd : |d| ≤ L) :
    KS S d = Kpsi d := by
  unfold KS Kpsi
  rw [primeTermS_eq hS hd]

/-- `S`-local Weil positivity on window-`L` configurations in `ker ℓ_c` (**OPEN** in general). -/
def SemilocalPos (S : Finset ℕ) (L : ℝ) : Prop :=
  ∀ (n : ℕ) (x c : Fin n → ℝ), (∀ i j, |x i - x j| ≤ L) →
    ∑ i, c i * Real.cosh (x i / 2) = 0 → 0 ≤ kform (KS S) x c

theorem kform_congr_window {K K' : ℝ → ℝ} {L : ℝ} (hK : ∀ d, |d| ≤ L → K d = K' d) {n : ℕ}
    (x c : Fin n → ℝ) (hx : ∀ i j, |x i - x j| ≤ L) : kform K x c = kform K' x c := by
  unfold kform
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hK _ (hx i j)]

/-- **PROVED**: `HPsiWindow L ↔ SemilocalPos S L` for any `S` covering `L`. -/
theorem hPsiWindow_iff_semilocalPos {S : Finset ℕ} {L : ℝ} (hS : Covers S L) :
    HPsiWindow L ↔ SemilocalPos S L := by
  constructor
  · intro h n x c hx hc
    rw [kform_congr_window (fun d hd => kS_eq_Kpsi hS hd) x c hx]
    exact h n x c hx hc
  · intro h n x c hx hc
    rw [← kform_congr_window (fun d hd => kS_eq_Kpsi hS hd) x c hx]
    exact h n x c hx hc

/-- **PROVED**: positivity on all windows gives H_ψ. -/
theorem hPsi_of_allWindows (h : ∀ L > 0, HPsiWindow L) : HPsi := by
  intro n x c hc
  set T : ℝ := ∑ i, ∑ j, |x i - x j|
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine h (T + 1) (by linarith) n x c (fun i j => ?_) hc
  have h1 : |x i - x j| ≤ ∑ j', |x i - x j'| :=
    Finset.single_le_sum (fun j' _ => abs_nonneg (x i - x j')) (Finset.mem_univ j)
  have h2 : ∑ j', |x i - x j'| ≤ T :=
    Finset.single_le_sum (f := fun i' => ∑ j', |x i' - x j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

/-- **Named Prop (OPEN, RH-strength)**: semilocal WeilIsGram on matched windows. For each
`L > 0`, the `S_L`-local Weil form is positive on window-`L` configurations in `ker ℓ_c`. -/
def SemilocalWeilIsGram : Prop := ∀ L > 0, SemilocalPos (primesBelowExp L) L

/-- **PROVED**: H_ψ is *equivalent* to `SemilocalWeilIsGram` (a reformulation, not a reduction). -/
theorem hPsi_iff_semilocalWeilIsGram : HPsi ↔ SemilocalWeilIsGram := by
  constructor
  · intro h L _
    exact (hPsiWindow_iff_semilocalPos (covers_primesBelowExp L)).1 (hPsiWindow_of_hPsi h L)
  · intro h
    exact hPsi_of_allWindows fun L hL =>
      (hPsiWindow_iff_semilocalPos (covers_primesBelowExp L)).2 (h L hL)

end GppWeilGram

#print axioms GppWeilGram.primeTermS_eq
#print axioms GppWeilGram.kS_eq_Kpsi
#print axioms GppWeilGram.hPsiWindow_iff_semilocalPos
#print axioms GppWeilGram.hPsi_iff_semilocalWeilIsGram
