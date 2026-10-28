import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# The affine current algebra of abelian currents (level `k`)

The level-`k` centrally extended loop algebra of `d` abelian (`u(1)`)
currents — the Heisenberg / free-boson current algebra — constructed as an
explicit `LieAlgebra ℂ`: elements are finitely supported mode sequences
`ℤ →₀ (Fin d → ℂ)` plus a central coordinate; the bracket is the
antisymmetrized pairing `k/2 · (Σ_m m·⟨x_m, y_{−m}⟩ − Σ_m m·⟨y_m, x_{−m}⟩)`
in the central coordinate and zero on modes.

On current modes `J^a_m` this gives the Kac–Moody commutation relation
`[J^a_m, J^b_n] = k·m·δ^{ab}·δ_{m+n,0}·C`
(`AffineCurrentAlgebra.kac_moody_commutator`): the level `k` appears in
the commutator exactly as the coefficient of the central term. This is
the construction `YangMills/MassGap.lean`'s stub
`open_kac_moody_level_appears_in_commutator` recorded as missing ("the
currents `J^a_m` are not constructed here and there is no bracket to
compute"); it is the abelian case, where the central term is the whole
commutator. The Jacobi identity is short because every bracket is
central and brackets against central elements vanish.
-/

/-- The level-`k` affine current algebra of `d` abelian currents, as a type:
    finitely supported modes `ℤ →₀ (Fin d → ℂ)` plus a central coordinate. -/
def AffineCurrentAlgebra (d : ℕ) (k : ℂ) : Type :=
  (ℤ →₀ (Fin d → ℂ)) × ℂ

namespace AffineCurrentAlgebra

variable {d : ℕ} {k : ℂ}

noncomputable instance : AddCommGroup (AffineCurrentAlgebra d k) :=
  inferInstanceAs (AddCommGroup ((ℤ →₀ (Fin d → ℂ)) × ℂ))

noncomputable instance : Module ℂ (AffineCurrentAlgebra d k) :=
  inferInstanceAs (Module ℂ ((ℤ →₀ (Fin d → ℂ)) × ℂ))

theorem eq_of_components {u v : AffineCurrentAlgebra d k}
    (h1 : u.1 = v.1) (h2 : u.2 = v.2) : u = v :=
  Prod.ext h1 h2

theorem add_fst (u v : AffineCurrentAlgebra d k) :
    (u + v).1 = u.1 + v.1 := rfl

theorem add_snd (u v : AffineCurrentAlgebra d k) :
    (u + v).2 = u.2 + v.2 := rfl

theorem smul_fst (r : ℂ) (u : AffineCurrentAlgebra d k) :
    (r • u).1 = r • u.1 := rfl

theorem smul_snd (r : ℂ) (u : AffineCurrentAlgebra d k) :
    (r • u).2 = r • u.2 := rfl

/-- The raw central pairing on modes (before antisymmetrization):
    `Σ_m m · ⟨x_m, y_{−m}⟩`. -/
def rawPairing (x y : ℤ →₀ (Fin d → ℂ)) : ℂ :=
  x.sum fun m xm => (m : ℂ) * ∑ a, xm a * y (-m) a

/-- The antisymmetrized level-`k` pairing. Antisymmetrizing by construction
    makes the bracket antisymmetric; on modes it evaluates to `k·m·δ`
    because `(m − (−m))/2 = m`. -/
noncomputable def pairingB (k : ℂ) (x y : ℤ →₀ (Fin d → ℂ)) : ℂ :=
  k / 2 * (rawPairing x y - rawPairing y x)

theorem rawPairing_add_left (x x' y : ℤ →₀ (Fin d → ℂ)) :
    rawPairing (x + x') y = rawPairing x y + rawPairing x' y := by
  unfold rawPairing
  rw [Finsupp.sum_add_index']
  · intro m
    simp
  · intro m u v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem rawPairing_add_right (x y y' : ℤ →₀ (Fin d → ℂ)) :
    rawPairing x (y + y') = rawPairing x y + rawPairing x y' := by
  unfold rawPairing
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro m _
  simp only [Finsupp.add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rawPairing_smul_left (c : ℂ) (x y : ℤ →₀ (Fin d → ℂ)) :
    rawPairing (c • x) y = c * rawPairing x y := by
  have h0 : ∀ m : ℤ, (m : ℂ) * ∑ a, (0 : Fin d → ℂ) a * y (-m) a = 0 := by
    intro m
    simp
  have hfun : (fun (m : ℤ) (xm : Fin d → ℂ) => (m : ℂ) * ∑ a, (c • xm) a * y (-m) a)
      = (fun (m : ℤ) (xm : Fin d → ℂ) => c * ((m : ℂ) * ∑ a, xm a * y (-m) a)) := by
    funext m xm
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  unfold rawPairing
  rw [Finsupp.sum_smul_index' h0, hfun]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]

theorem rawPairing_smul_right (c : ℂ) (x y : ℤ →₀ (Fin d → ℂ)) :
    rawPairing x (c • y) = c * rawPairing x y := by
  have hfun : (fun (m : ℤ) (xm : Fin d → ℂ) => (m : ℂ) * ∑ a, xm a * (c • y) (-m) a)
      = (fun (m : ℤ) (xm : Fin d → ℂ) => c * ((m : ℂ) * ∑ a, xm a * y (-m) a)) := by
    funext m xm
    have pa : ∀ a : Fin d, xm a * (c • y) (-m) a
        = c * (xm a * y (-m) a) := by
      intro a
      simp only [Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun a _ => pa a), ← Finset.mul_sum]
    ring
  unfold rawPairing
  rw [hfun]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]

theorem rawPairing_zero_left (y : ℤ →₀ (Fin d → ℂ)) :
    rawPairing 0 y = 0 := by
  simp [rawPairing]

theorem rawPairing_zero_right (x : ℤ →₀ (Fin d → ℂ)) :
    rawPairing x 0 = 0 := by
  simp [rawPairing]

theorem pairingB_add_left (x x' y : ℤ →₀ (Fin d → ℂ)) :
    pairingB k (x + x') y = pairingB k x y + pairingB k x' y := by
  simp only [pairingB, rawPairing_add_left, rawPairing_add_right]
  ring

theorem pairingB_add_right (x y y' : ℤ →₀ (Fin d → ℂ)) :
    pairingB k x (y + y') = pairingB k x y + pairingB k x y' := by
  simp only [pairingB, rawPairing_add_right, rawPairing_add_left]
  ring

theorem pairingB_smul_left (c : ℂ) (x y : ℤ →₀ (Fin d → ℂ)) :
    pairingB k (c • x) y = c * pairingB k x y := by
  simp only [pairingB, rawPairing_smul_left, rawPairing_smul_right]
  ring

theorem pairingB_smul_right (c : ℂ) (x y : ℤ →₀ (Fin d → ℂ)) :
    pairingB k x (c • y) = c * pairingB k x y := by
  simp only [pairingB, rawPairing_smul_right, rawPairing_smul_left]
  ring

theorem pairingB_zero_left (y : ℤ →₀ (Fin d → ℂ)) :
    pairingB k 0 y = 0 := by
  simp [pairingB, rawPairing_zero_left, rawPairing_zero_right]

theorem pairingB_zero_right (x : ℤ →₀ (Fin d → ℂ)) :
    pairingB k x 0 = 0 := by
  simp [pairingB, rawPairing_zero_left, rawPairing_zero_right]

theorem pairingB_self (x : ℤ →₀ (Fin d → ℂ)) :
    pairingB k x x = 0 := by
  simp [pairingB]

noncomputable instance :
    Bracket (AffineCurrentAlgebra d k) (AffineCurrentAlgebra d k) :=
  ⟨fun u v => (0, pairingB k u.1 v.1)⟩

theorem bracket_fst (u v : AffineCurrentAlgebra d k) : ⁅u, v⁆.1 = 0 := rfl

theorem bracket_snd (u v : AffineCurrentAlgebra d k) :
    ⁅u, v⁆.2 = pairingB k u.1 v.1 := rfl

noncomputable instance : LieRing (AffineCurrentAlgebra d k) where
  add_lie := by
    intro x y z
    apply eq_of_components
    · simp only [add_fst, bracket_fst, add_zero]
    · simp only [bracket_snd, add_snd, add_fst]
      exact pairingB_add_left x.1 y.1 z.1
  lie_add := by
    intro x y z
    apply eq_of_components
    · simp only [add_fst, bracket_fst, add_zero]
    · simp only [bracket_snd, add_snd, add_fst]
      exact pairingB_add_right x.1 y.1 z.1
  lie_self := by
    intro x
    apply eq_of_components
    · show ⁅x, x⁆.1 = 0
      exact bracket_fst x x
    · simp only [bracket_snd]
      exact pairingB_self x.1
  leibniz_lie := by
    intro x y z
    apply eq_of_components
    · simp only [add_fst, bracket_fst, add_zero]
    · simp only [bracket_snd, bracket_fst, add_snd,
        pairingB_zero_left, pairingB_zero_right, add_zero]

noncomputable instance : LieAlgebra ℂ (AffineCurrentAlgebra d k) where
  lie_smul := by
    intro r x y
    apply eq_of_components
    · simp only [bracket_fst, smul_fst, smul_zero]
    · simp only [bracket_snd, smul_fst, smul_snd, smul_eq_mul]
      exact pairingB_smul_right r x.1 y.1

/-- The `a`-th current at mode `m`: `J^a_m`. -/
noncomputable def mode (a : Fin d) (m : ℤ) : AffineCurrentAlgebra d k :=
  (Finsupp.single m (Pi.single a (1 : ℂ)), 0)

/-- The central element `C`. -/
def central : AffineCurrentAlgebra d k := (0, 1)

theorem mode_fst (a : Fin d) (m : ℤ) :
    (mode (k := k) a m).1 = Finsupp.single m (Pi.single a (1 : ℂ)) := rfl

theorem central_snd : (central : AffineCurrentAlgebra d k).2 = 1 := rfl

theorem central_fst :
    (central : AffineCurrentAlgebra d k).1 = 0 := rfl

theorem single_inner (a b : Fin d) :
    ∑ i, (Pi.single a (1 : ℂ) : Fin d → ℂ) i * (Pi.single b (1 : ℂ) : Fin d → ℂ) i
      = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp [Pi.single_eq_same]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_mul]
    · simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i = a
    · subst hi
      rw [Pi.single_eq_of_ne hab, mul_zero]
    · rw [Pi.single_eq_of_ne hi, zero_mul]

theorem rawPairing_mode (a b : Fin d) (m n : ℤ) :
    rawPairing (Finsupp.single m (Pi.single a (1 : ℂ)))
        (Finsupp.single n (Pi.single b (1 : ℂ)))
      = (m : ℂ) * (if m + n = 0 then (if a = b then 1 else 0) else 0) := by
  have h0 : (m : ℂ) * ∑ i, (0 : Fin d → ℂ) i
      * (Finsupp.single n (Pi.single b (1 : ℂ) : Fin d → ℂ)) (-m) i = 0 := by
    simp
  unfold rawPairing
  rw [Finsupp.sum_single_index h0]
  by_cases h : m + n = 0
  · have hn : n = -m := by omega
    rw [if_pos h, hn, Finsupp.single_apply, if_pos rfl, single_inner]
  · have hn : n ≠ -m := by
      intro he
      apply h
      rw [he, add_neg_cancel]
    rw [if_neg h, Finsupp.single_apply, if_neg hn]
    simp

/-- **The Kac–Moody commutation relation at level `k`**: in the affine
    current algebra of `d` abelian currents, the commutator of two modes is
    purely central, with central charge `k · m · δ^{ab} · δ_{m+n,0}` — the
    level `k` appears in the commutator exactly as the coefficient of the
    central term. -/
theorem kac_moody_commutator (a b : Fin d) (m n : ℤ) :
    ⁅mode (k := k) a m, mode (k := k) b n⁆
      = (k * (m : ℂ) * (if a = b then 1 else 0)
        * (if m + n = 0 then 1 else 0)) • (central : AffineCurrentAlgebra d k) := by
  apply eq_of_components
  · simp only [bracket_fst, smul_fst, central_fst, smul_zero]
  · simp only [bracket_snd, mode_fst, smul_snd, central_snd,
      smul_eq_mul, mul_one]
    rw [pairingB, rawPairing_mode, rawPairing_mode]
    by_cases h : m + n = 0
    · have hn : n = -m := by omega
      have hnm : n + m = 0 := by omega
      simp only [h, hnm, if_true]
      rw [hn]
      by_cases hab : a = b
      · subst hab
        simp only [eq_self_iff_true, if_true, Int.cast_neg]
        ring
      · simp only [if_neg hab, if_neg (Ne.symm hab)]
        ring
    · have hnm : n + m ≠ 0 := by omega
      simp only [h, hnm, if_false]
      ring

end AffineCurrentAlgebra
