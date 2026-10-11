import Mathlib.Tactic

/-!
# Detector: the Cayley 2×2 gap test sees an off-axis quartet that every 2-node real Pick test misses

Codex (GPP-bridge PR #11, 2026-10-11). With `H(z) = F((2+z)/(1−z)) = ∑ aₙ zⁿ`, `F = ξ'/ξ`, RH is
equivalent (classical: Carathéodory one way, radius of convergence + reflection the other; **not
formalised here**) to `|aₙ| ≤ 2a₀` for all `n ≥ 1`, i.e. every 2×2 *gap-n Toeplitz* matrix
`[[2a₀, aₙ],[aₙ, 2a₀]]` is PSD. This file certifies the exact finite part for Astra's synthetic quartet
(spectral zeros `½ ± 1/5 ± 14i`), which passes **all** 2-node real Pick tests
(`GppNoGo.TwoNodePick.twoNode_pos`).

* `Hsyn_eq`: the synthetic `H(z)` (its two conjugate pairs written in real form) equals `P(z)/Q(z)` with
  `P = 11892600 − 23245200z + 23245200z³ − 11892600z⁴`,
  `Q = 393185641 − 1537064764z + 2288568246z² − 1537064764z³ + 393185641z⁴`.
* `gap44_noGo`: **any** sequence `b` with `Q·b = P` coefficientwise up to index 44 (i.e. the Taylor
  coefficients of `P/Q`) satisfies `|bₙ| ≤ 2b₀` for `1 ≤ n ≤ 43` and `b₄₄ < −2b₀`.

The 44-step rational recurrence is evaluated by the kernel (`decide +kernel`, no extra axioms), so no
387-digit literal appears. Independently reproduced in exact Python `Fraction` arithmetic (first failure
at `n = 44`, `|a₄₄|/(2a₀) = 1.00817`).

**Reading / hint.** The Cayley gap test is a *different finite projection* of the same RH-equivalent
positivity: it detects this quartet at gap 44 where 2-node real Pick tests cannot. It does not make
RH easier: an unconditional bound `sup |aₙ| ≤ 2a₀` for `ξ` is RH-strength (via `aₙ = Aₙ − Eₙ`, the
pole-cancelled Laguerre prime sums). The link "Taylor coefficients of `P/Q` = the sequence with `Q·b = P`"
is standard power-series uniqueness and is used here as the definition.
-/

namespace GppNoGo.CayleyGap44

def Qc : ℕ → ℚ
  | 0 => 393185641 | 1 => -1537064764 | 2 => 2288568246 | 3 => -1537064764 | 4 => 393185641 | _ => 0
def Pc : ℕ → ℚ
  | 0 => 11892600 | 1 => -23245200 | 2 => 0 | 3 => 23245200 | 4 => -11892600 | _ => 0

/-- state `(aₙ, aₙ₋₁, aₙ₋₂, aₙ₋₃)` -/
def st : ℕ → ℚ × ℚ × ℚ × ℚ
  | 0 => (Pc 0 / Qc 0, 0, 0, 0)
  | n + 1 =>
    let (a, b, c, d) := st n
    ((Pc (n + 1) - (Qc 1 * a + Qc 2 * b + Qc 3 * c + Qc 4 * d)) / Qc 0, a, b, c)

def a (n : ℕ) : ℚ := (st n).1

/-- Convolution `∑_{k ≤ min n 4} Q_k a_{n-k}`. -/
def conv (b : ℕ → ℚ) (n : ℕ) : ℚ := ∑ k ∈ Finset.range (min n 4 + 1), Qc k * b (n - k)

theorem a_conv : ∀ n ∈ Finset.range 45, conv a n = Pc n := by decide +kernel
theorem fail44 : a 44 < -2 * a 0 := by decide +kernel
theorem ok43 : ∀ n ∈ Finset.Icc 1 43, |a n| ≤ 2 * a 0 := by decide +kernel

theorem conv_succ (b : ℕ → ℚ) (n : ℕ) :
    conv b n = ∑ k ∈ Finset.range (min n 4), Qc (k + 1) * b (n - (k + 1)) + Qc 0 * b n := by
  unfold conv
  rw [Finset.sum_range_succ']
  simp

theorem unique_upto (b c : ℕ → ℚ) (N : ℕ) (hb : ∀ n ≤ N, conv b n = Pc n)
    (hc : ∀ n ≤ N, conv c n = Pc n) : ∀ n ≤ N, b n = c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h1 := hb n hn
    have h2 := hc n hn
    rw [conv_succ] at h1 h2
    have hsum : ∑ k ∈ Finset.range (min n 4), Qc (k + 1) * b (n - (k + 1))
        = ∑ k ∈ Finset.range (min n 4), Qc (k + 1) * c (n - (k + 1)) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < min n 4 := Finset.mem_range.mp hk
      have : k + 1 ≤ n := by omega
      rw [ih (n - (k + 1)) (by omega) (by omega)]
    have hQ : Qc 0 ≠ 0 := by decide
    have : Qc 0 * b n = Qc 0 * c n := by linarith
    exact mul_left_cancel₀ hQ this

theorem gap44_noGo (b : ℕ → ℚ) (hb : ∀ n ≤ 44, conv b n = Pc n) :
    b 44 < -2 * b 0 ∧ ∀ n ∈ Finset.Icc 1 43, |b n| ≤ 2 * b 0 := by
  have hab : ∀ n ≤ 44, b n = a n :=
    unique_upto b a 44 hb (fun n hn => a_conv n (Finset.mem_range.mpr (by omega)))
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hab 44 le_rfl, hab 0 (by norm_num)]; exact fail44
  · have hn' := Finset.mem_Icc.mp hn
    rw [hab n (by omega), hab 0 (by norm_num)]; exact ok43 n hn

/-- The synthetic Cayley-transformed log-derivative equals `P/Q` (real `z ≠ 1`). -/
theorem Hsyn_eq (z : ℝ) (hz : z ≠ 1) :
    2 * ((2 + z) / (1 - z) - 7 / 10) / (((2 + z) / (1 - z) - 7 / 10) ^ 2 + 196)
      + 2 * ((2 + z) / (1 - z) - 3 / 10) / (((2 + z) / (1 - z) - 3 / 10) ^ 2 + 196)
      = (11892600 - 23245200 * z + 23245200 * z ^ 3 - 11892600 * z ^ 4)
        / (393185641 - 1537064764 * z + 2288568246 * z ^ 2 - 1537064764 * z ^ 3 + 393185641 * z ^ 4) := by
  set s := (2 + z) / (1 - z) with hs
  have h1 : (1 : ℝ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  set D1 := (s - 7 / 10) ^ 2 + 196
  set D2 := (s - 3 / 10) ^ 2 + 196
  have hd1 : D1 ≠ 0 := by positivity
  have hd2 : D2 ≠ 0 := by positivity
  have eQ : (1 - z) ^ 4 * (D1 * D2)
      = (393185641 - 1537064764 * z + 2288568246 * z ^ 2 - 1537064764 * z ^ 3 + 393185641 * z ^ 4) / 10000 := by
    simp only [D1, D2, hs]; field_simp; ring
  have eP : (1 - z) ^ 4 * (2 * (s - 7 / 10) * D2 + 2 * (s - 3 / 10) * D1)
      = (11892600 - 23245200 * z + 23245200 * z ^ 3 - 11892600 * z ^ 4) / 10000 := by
    simp only [D1, D2, hs]; field_simp; ring
  have h4 : (1 - z) ^ 4 ≠ 0 := pow_ne_zero 4 h1
  rw [div_add_div _ _ hd1 hd2, ← mul_div_mul_left _ (D1 * D2) h4]
  have hnum : 2 * (s - 7 / 10) * D2 + D1 * (2 * (s - 3 / 10)) = 2 * (s - 7 / 10) * D2 + 2 * (s - 3 / 10) * D1 := by ring
  rw [hnum, eP, eQ]
  have hQ : (393185641 - 1537064764 * z + 2288568246 * z ^ 2 - 1537064764 * z ^ 3 + 393185641 * z ^ 4 : ℝ) ≠ 0 := by
    intro h0
    have : (1 - z) ^ 4 * (D1 * D2) = 0 := by rw [eQ, h0]; norm_num
    exact mul_ne_zero h4 (mul_ne_zero hd1 hd2) this
  field_simp

end GppNoGo.CayleyGap44
