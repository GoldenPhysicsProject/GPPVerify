import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The conductor Hamiltonian on the compact sector has gap `log 3`

Source: Codex, GPP-bridge PR #11 comment 6123987713 (2026-10-12), building on Daniel Toupin's
observation that Peter–Weyl quantizes the compact part `K ≅ Ẑ^×` of the idele class group into
Dirichlet characters.

Codex's model Hamiltonian on `L²(K)` is `H_cond χ = log(cond χ) · χ`. Its exact spectral facts:
* `conductor_eq_one_iff`: the trivial character is the unique vacuum (conductor `1`, energy `0`);
* `conductor_ne_two`: no character has conductor `2`, because `(ZMod 2)ˣ` is trivial;
* `three_le_conductor`, `log_three_le`: every nontrivial character has conductor `≥ 3`, so energy
  `≥ log 3`. The gap is exactly `log 3`, attained by the character mod 3.

Assigning energy `log cond` is a model choice: it is an intrinsic arithmetic filtration, not a
derived dynamics. It gaps only the discrete label `χ`, not the continuous Mellin variable `τ`
(see `GppNoGo.CompactCommutingMixing`). **No RH or Yang–Mills claim.**
-/

namespace GppConductorGap

open DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

/-- Every Dirichlet character of level `2` is trivial. -/
lemma level_two (χ : DirichletCharacter R 2) : χ = 1 := by
  have hu : ∀ a : (ZMod 2)ˣ, a = 1 := by decide
  ext a
  rw [hu a]
  simp

/-- **No character has conductor `2`.** -/
theorem conductor_ne_two {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) : conductor χ ≠ 2 := by
  intro h2
  obtain ⟨h', χ₀, hχ⟩ := factorsThrough_conductor χ
  have key : ∀ d : ℕ, d = 2 → ∀ ψ : DirichletCharacter R d, ψ = 1 := by
    rintro d rfl ψ
    exact level_two ψ
  have hχ₀ : χ₀ = 1 := key _ h2 χ₀
  have : χ = 1 := by rw [hχ, hχ₀, changeLevel_one]
  rw [eq_one_iff_conductor_eq_one] at this
  omega

/-- The trivial character is the unique vacuum. -/
theorem conductor_eq_one_iff {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) :
    conductor χ = 1 ↔ χ = 1 :=
  eq_one_iff_conductor_eq_one.symm

/-- **Every nontrivial character has conductor at least `3`.** -/
theorem three_le_conductor {n : ℕ} [NeZero n] {χ : DirichletCharacter R n} (hχ : χ ≠ 1) :
    3 ≤ conductor χ := by
  have h0 := conductor_ne_zero χ
  have h1 : conductor χ ≠ 1 := fun h => hχ ((conductor_eq_one_iff χ).mp h)
  have h2 := conductor_ne_two χ
  omega

/-- **The gap `log 3`.** -/
theorem log_three_le {n : ℕ} [NeZero n] {χ : DirichletCharacter R n} (hχ : χ ≠ 1) :
    Real.log 3 ≤ Real.log (conductor χ) := by
  have := three_le_conductor hχ
  exact Real.log_le_log (by norm_num) (by exact_mod_cast this)

/-- The vacuum has energy `0`. -/
theorem log_conductor_one {n : ℕ} [NeZero n] :
    Real.log (conductor (1 : DirichletCharacter R n)) = 0 := by
  simp [conductor_one]

end GppConductorGap
