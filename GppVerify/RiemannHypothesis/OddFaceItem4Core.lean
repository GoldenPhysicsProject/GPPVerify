import GppVerify.RiemannHypothesis.OddFaceItem4Data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# OddFace(0.5), item 4: integer certificate definitions and the bridge to `ℝ`

The kernel-checked part of the bordered-floor certificate (Flint run 15, Turbo-audited
`BANKED` as verified: bridge `df1ec9d`, export audit `b086cf4`). Everything here is finite integer
arithmetic on the data of `OddFaceItem4Data.lean`; the entry enclosures themselves (the integrals) are
**not** proved in Lean and enter `OddFaceItem4Floor.lean` as hypotheses.

`resInt i j` is the exact integer residual of the rounded factorisation, in units of
`1 / (Qq · 2^384)`:

  `Nm_ij = Nnum_ij / Qq`,   `Σ_k L_ik D_k L_jk = Sint_ij / 2^384`,   `δ = 2⁻⁶⁰ = twoPow324 / twoPow384`,

  `resInt i j = Nnum_ij · 2^384 − Qq · Sint_ij − [i = j] · Qq · 2^324`.

`rowOk i` checks `|resInt i j| ≤ EE` for all `j < 73`; the shard files discharge it by
`decide +kernel` over row ranges. `check_real` turns that into the real-number residual hypothesis of
`Matrix.le_quadForm_of_ldl_residual`.
-/

namespace GppOddFaceItem4

open Finset

/-! ### Decoding the packed data -/

/-- `2^159`, the offset, via `Nat.pow` (GMP-accelerated in the kernel). -/
def OFF : ℤ := ((2 ^ 159 : ℕ) : ℤ)

/-- The `j`-th signed 160-bit entry of a packed natural number. -/
def unpack (row : ℕ) (j : ℕ) : ℤ := (((row / 2 ^ (160 * j)) % 2 ^ 160 : ℕ) : ℤ) - OFF

/-- Entry `(i, j)` of a packed matrix. -/
def ent (M : List ℕ) (i j : ℕ) : ℤ := unpack (M.getD i 0) j

/-- Entry `k` of a packed vector. -/
def vent (v : ℕ) (k : ℕ) : ℤ := unpack v k

/-! ### The integer check -/

/-- Structural sum `Σ_{k<n} f k`, kernel-friendly. -/
def ssum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => ssum f n + f n

theorem ssum_eq (f : ℕ → ℤ) (n : ℕ) : ssum f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [ssum]
  | succ n ih => rw [ssum, ih, sum_range_succ]

/-- Row sum of the radii (the diagonal charge `r_i`), over `2^100`. -/
def rsum (i : ℕ) : ℤ := ssum (fun j => ent radD i j) 73

/-- `Qq · Nm_ij`, where `Nm = C − diag(r) − (13/10) P`, `P = 1` on positions `≥ 61` (the `E₁₂` block). -/
def Nnum (i j : ℕ) : ℤ :=
  10 * ent cenD i j - (if i = j then 10 * rsum i + (if 61 ≤ i then chargeNum else 0) else 0)

/-- `2^384 · Σ_k L_ik D_k L_jk`. -/
def Sint (i j : ℕ) : ℤ := ssum (fun k => ent lD i k * vent dD k * ent lD j k) 73

/-- The exact integer residual. -/
def resInt (i j : ℕ) : ℤ :=
  Nnum i j * twoPow384 - Qq * Sint i j - (if i = j then Qq * twoPow324 else 0)

def resOk (i j : ℕ) : Bool := decide (resInt i j ≤ EE ∧ -EE ≤ resInt i j)

def rowOk (i : ℕ) : Bool := (List.range 73).all (resOk i)

/-- Every `D_k` is nonnegative. -/
def dOk : Bool := (List.range 73).all fun k => decide (0 ≤ vent dD k)

/-- The margin: `73 · EE < Qq · 2^324` (i.e. `n ε < δ`, over the common denominator `Qq · 2^384`,
since `δ = 2⁻⁶⁰ ↔ Qq · 2^324`). -/
def marginOk : Bool := decide (73 * EE < Qq * twoPow324)

/-! ### Bridge to the reals -/

noncomputable def Nmr (i j : ℕ) : ℝ := (Nnum i j : ℝ) / (Qq : ℝ)
noncomputable def Lr (i k : ℕ) : ℝ := (ent lD i k : ℝ) / 2 ^ 128
noncomputable def Dr (k : ℕ) : ℝ := (vent dD k : ℝ) / 2 ^ 128
/-- The shift `δ = 2⁻⁶⁰`. -/
noncomputable def δr : ℝ := 1 / 2 ^ 60
/-- The residual bound `ε = EE / (Qq · 2^384)`. -/
noncomputable def εr : ℝ := (EE : ℝ) / ((Qq : ℝ) * (twoPow384 : ℝ))

theorem twoPow384_eq : (twoPow384 : ℝ) = 2 ^ 128 * 2 ^ 128 * 2 ^ 128 := by
  unfold twoPow384; norm_num

theorem twoPow324_eq : (twoPow384 : ℝ) = (twoPow324 : ℝ) * 2 ^ 60 := by
  unfold twoPow384 twoPow324; norm_num

theorem Qq_pos : (0 : ℝ) < (Qq : ℝ) := by unfold Qq; norm_num

theorem twoPow384_pos : (0 : ℝ) < (twoPow384 : ℝ) := by unfold twoPow384; norm_num

theorem sum_LDL (i j : ℕ) :
    ∑ k ∈ range 73, Lr i k * Dr k * Lr j k = (Sint i j : ℝ) / (twoPow384 : ℝ) := by
  unfold Sint
  rw [ssum_eq, twoPow384_eq]
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun k _ => ?_
  unfold Lr Dr
  ring

theorem check_real {i j : ℕ} (h : rowOk i = true) (hj : j < 73) :
    |Nmr i j - ((if i = j then δr else 0) + ∑ k ∈ range 73, Lr i k * Dr k * Lr j k)| ≤ εr := by
  have hr : resOk i j = true := by
    unfold rowOk at h
    rw [List.all_eq_true] at h
    exact h j (List.mem_range.mpr hj)
  unfold resOk at hr
  have hr' := of_decide_eq_true hr
  have key : Nmr i j - ((if i = j then δr else 0) + ∑ k ∈ range 73, Lr i k * Dr k * Lr j k)
      = (resInt i j : ℝ) / ((Qq : ℝ) * (twoPow384 : ℝ)) := by
    rw [sum_LDL]
    have hQ := Qq_pos.ne'
    have hT := twoPow384_pos.ne'
    have hT2 : (twoPow324 : ℝ) ≠ 0 := by unfold twoPow324; norm_num
    unfold Nmr resInt δr
    by_cases hij : i = j
    · simp only [hij, if_true]
      push_cast
      rw [twoPow324_eq]
      field_simp
      ring
    · simp only [hij, if_false]
      push_cast
      field_simp
      ring
  rw [key, abs_div, abs_of_pos (mul_pos Qq_pos twoPow384_pos)]
  unfold εr
  refine div_le_div_of_nonneg_right ?_ (mul_pos Qq_pos twoPow384_pos).le
  rw [abs_le]
  constructor
  · have := hr'.2; exact_mod_cast (by linarith : -(EE : ℤ) ≤ resInt i j)
  · exact_mod_cast hr'.1

end GppOddFaceItem4
