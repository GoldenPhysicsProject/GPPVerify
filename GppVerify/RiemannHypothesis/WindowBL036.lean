import GppVerify.RiemannHypothesis.WindowL036
import GppVerify.RiemannHypothesis.WindowBCheck0L036
import GppVerify.RiemannHypothesis.WindowBCheck1L036
import GppVerify.RiemannHypothesis.WindowBCheck2L036
import GppVerify.RiemannHypothesis.WindowBCheck3L036
import GppVerify.RiemannHypothesis.WindowBCheck4L036
import GppVerify.RiemannHypothesis.WindowBCheck5L036
import GppVerify.RiemannHypothesis.WindowBCheck6L036
import GppVerify.RiemannHypothesis.WindowBCheck7L036
import GppVerify.RiemannHypothesis.WindowBCheck8L036
import GppVerify.RiemannHypothesis.WindowBCheck9L036

/-!
# The first prime-visible window, unconditionally

Input (b) of the `ℓ = 9/25`, `T = 25` window certificate, discharged:

* `mfun_le_symbol`: the piecewise-polynomial minorant satisfies `mfun r ≤ Ψ₂(r) - β₂(25)` on
  `[-25, 25]`;
* `abs_mfun_le`: `|mfun r| ≤ 8` there.

Route: `mfun r = mpos |r|`; on the piece `[i/4, (i+1)/4]` containing `|r|`,
`mpos ≤ G_80` and `|mpos| ≤ 8` by the kernel check `checkPieceOf (pieceQ i) i = true`
(`WindowBCheck{0..9}L036`, through `GppWindowBPiece.piece_bound`); `G_80` is even, and
`G_80 ≤ Ψ₂ - β₂(25)` everywhere (`GppWindowGM.GM_le`, from the staged vertical digamma bounds).

With these, `GppWindowL036.weilForm_autocorr_nonneg_l036` loses its two hypotheses:

**`weilForm_autocorr_nonneg_l036_unconditional`**: for every real test function `g` vanishing outside
`[-9/25, 9/25]`, `weilForm (autocorr g) ≥ 0`.

This is one window. `2 · 9/25 = 0.72 > log 2`, so the prime `2` contributes to the form; the
window stops below `log 3`, so no other prime does. It says nothing about the zeros of `ζ` and
nothing about larger windows; Weil positivity for all test functions stays OPEN.
No `sorry`, no axioms beyond the standard three.
-/

namespace GppWindowBL036

open Set MeasureTheory GppMeyerSpectralWeil GppArithmeticReflection GppWeilLadder
  GppRungOneReductionTwo GppWindowGM GppWindowBPiece GppWindowMinorantL036 GppWindowPolyBasis

theorem all_ok : ∀ i < 100, checkPieceOf (pieceQ i) i = true := by
  intro i hi
  interval_cases i
  exacts [piece_ok_0, piece_ok_1, piece_ok_2, piece_ok_3, piece_ok_4, piece_ok_5, piece_ok_6,
    piece_ok_7, piece_ok_8, piece_ok_9, piece_ok_10, piece_ok_11, piece_ok_12, piece_ok_13,
    piece_ok_14, piece_ok_15, piece_ok_16, piece_ok_17, piece_ok_18, piece_ok_19, piece_ok_20,
    piece_ok_21, piece_ok_22, piece_ok_23, piece_ok_24, piece_ok_25, piece_ok_26, piece_ok_27,
    piece_ok_28, piece_ok_29, piece_ok_30, piece_ok_31, piece_ok_32, piece_ok_33, piece_ok_34,
    piece_ok_35, piece_ok_36, piece_ok_37, piece_ok_38, piece_ok_39, piece_ok_40, piece_ok_41,
    piece_ok_42, piece_ok_43, piece_ok_44, piece_ok_45, piece_ok_46, piece_ok_47, piece_ok_48,
    piece_ok_49, piece_ok_50, piece_ok_51, piece_ok_52, piece_ok_53, piece_ok_54, piece_ok_55,
    piece_ok_56, piece_ok_57, piece_ok_58, piece_ok_59, piece_ok_60, piece_ok_61, piece_ok_62,
    piece_ok_63, piece_ok_64, piece_ok_65, piece_ok_66, piece_ok_67, piece_ok_68, piece_ok_69,
    piece_ok_70, piece_ok_71, piece_ok_72, piece_ok_73, piece_ok_74, piece_ok_75, piece_ok_76,
    piece_ok_77, piece_ok_78, piece_ok_79, piece_ok_80, piece_ok_81, piece_ok_82, piece_ok_83,
    piece_ok_84, piece_ok_85, piece_ok_86, piece_ok_87, piece_ok_88, piece_ok_89, piece_ok_90,
    piece_ok_91, piece_ok_92, piece_ok_93, piece_ok_94, piece_ok_95, piece_ok_96, piece_ok_97,
    piece_ok_98, piece_ok_99]

/-- `G_M` is even. -/
theorem GM_abs (M : ℕ) (r : ℝ) : GM M |r| = GM M r := by
  rcases abs_choice r with h | h <;> rw [h]
  unfold GM primeTwoCos
  simp only [neg_div, neg_sq, neg_mul, Real.cos_neg]

/-- On `[0, 25]`, the minorant lies below `G_80` and is bounded by `8`. -/
theorem mpos_bound {r : ℝ} (h0 : 0 ≤ r) (h25 : r ≤ 25) : mpos r ≤ GM 80 r ∧ |mpos r| ≤ 8 := by
  set i := ⌈4 * r⌉₊ - 1 with hi_def
  have key : i < 100 ∧ r ∈ Icc ((i : ℝ) / 4) (((i : ℝ) + 1) / 4) := by
    rcases h0.eq_or_lt with h | h
    · subst h
      simp [hi_def]
    · have hpos : 0 < ⌈4 * r⌉₊ := Nat.ceil_pos.mpr (by linarith)
      have hle : ⌈4 * r⌉₊ ≤ 100 := Nat.ceil_le.mpr (by push_cast; linarith)
      have hcast : (i : ℝ) + 1 = (⌈4 * r⌉₊ : ℝ) := by
        rw [hi_def, Nat.cast_sub (by omega)]; push_cast; ring
      have hc1 := Nat.le_ceil (4 * r)
      have hc2 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 4 * r)
      refine ⟨by omega, ?_, ?_⟩ <;> linarith
  have := piece_bound (pieceQ i) i (all_ok i key.1) key.2
  exact this

/-- **Input (b), validity.** -/
theorem mfun_le_symbol : ∀ r ∈ Icc (-25 : ℝ) 25, mfun r ≤ symbolTwo r - betaTwo 25 := by
  intro r hr
  have h := (mpos_bound (abs_nonneg r) (abs_le.mpr ⟨by linarith [hr.1], hr.2⟩)).1
  unfold mfun
  rw [GM_abs] at h
  exact h.trans (GM_le 80 r)

/-- **Input (b), size.** -/
theorem abs_mfun_le : ∀ r ∈ Icc (-25 : ℝ) 25, |mfun r| ≤ 8 := by
  intro r hr
  unfold mfun
  exact (mpos_bound (abs_nonneg r) (abs_le.mpr ⟨by linarith [hr.1], hr.2⟩)).2

/-- **The first prime-visible window.** For every real test function `g` vanishing outside
`[-9/25, 9/25]`, the Weil form of its autocorrelation is nonnegative. -/
theorem weilForm_autocorr_nonneg_l036_unconditional {g : ℝ → ℝ} (hg : IsTestFunction g)
    (hs : HasSupportIn g (9 / 25)) : 0 ≤ weilForm (autocorr g) :=
  GppWindowL036.weilForm_autocorr_nonneg_l036 mfun_le_symbol abs_mfun_le hg hs

end GppWindowBL036

#print axioms GppWindowBL036.mfun_le_symbol
#print axioms GppWindowBL036.abs_mfun_le
#print axioms GppWindowBL036.weilForm_autocorr_nonneg_l036_unconditional
