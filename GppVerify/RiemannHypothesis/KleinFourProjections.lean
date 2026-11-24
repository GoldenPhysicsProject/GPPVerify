import GppVerify.RiemannHypothesis.PrimeCapLegendre

/-!
# Klein-four spectral projections of two commuting involutions

Generic algebra (no number-theoretic names; upstreamable): in a real algebra `A`, for two commuting
involutions `X, J` (`X² = J² = 1`, `XJ = JX`) and signs `c, j ∈ {±1}`, the elements

`Π(c, j) = ¼ (1 + c X)(1 + j J)`

are mutually orthogonal idempotents summing to `1`, with `X Π(c,j) = c Π(c,j)` and `J Π(c,j) = j Π(c,j)`,
hence `(JX) Π(c,j) = (c j) Π(c,j)`. This is the Klein-four sector decomposition used for the prime-cap
operators in Turbo's relay `bfbdb91` (unit (ii)): the prime sign is `−v c` while the global parity is
`r = c j`, so fixing the parity does not fix the prime sign.

**Scope.** Algebra only.

No `sorry`, no axiom.
-/

noncomputable section

namespace GppKleinFour

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- `Π(c, j) = ¼ (1 + c X)(1 + j J)`. -/
def proj (X J : A) (c j : ℝ) : A := (1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J))

theorem commute_one_add_smul {X J : A} (h : Commute X J) (j : ℝ) : Commute X (1 + j • J) :=
  (Commute.one_right X).add_right (h.smul_right j)

theorem commute_proj {X J : A} (h : Commute X J) (c j : ℝ) : Commute X (proj X J c j) :=
  (((Commute.one_right X).add_right ((Commute.refl X).smul_right c)).mul_right
    (commute_one_add_smul h j)).smul_right _

theorem commute_proj_J {X J : A} (h : Commute X J) (c j : ℝ) : Commute J (proj X J c j) := by
  unfold proj
  have h1 : Commute J (1 + c • X) :=
    (Commute.one_right J).add_right (h.symm.smul_right c)
  have h2 : Commute J (1 + j • J) := (Commute.one_right J).add_right ((Commute.refl J).smul_right j)
  exact (h1.mul_right h2).smul_right _

/-- `X Π(c, j) = c Π(c, j)` for `c = ±1`. -/
theorem X_mul_proj {X J : A} (hX : X * X = 1) {c : ℝ} (j : ℝ) (hc1 : c * c = 1) :
    X * proj X J c j = c • proj X J c j := by
  unfold proj
  have : X * ((1 + c • X) * (1 + j • J)) = c • ((1 + c • X) * (1 + j • J)) := by
    have e : X * (1 + c • X) = c • (1 + c • X) := by
      rw [mul_add, mul_smul_comm, hX, mul_one, smul_add, smul_smul, hc1]
      rw [add_comm]; simp
    rw [← mul_assoc, e, smul_mul_assoc]
  rw [mul_smul_comm, this, smul_comm]

/-- `J Π(c, j) = j Π(c, j)` for `j = ±1`. -/
theorem J_mul_proj {X J : A} (hJ : J * J = 1) (h : Commute X J) (c : ℝ) {j : ℝ}
    (hj1 : j * j = 1) : J * proj X J c j = j • proj X J c j := by
  unfold proj
  have hJX : J * (1 + c • X) = (1 + c • X) * J := (Commute.one_right J |>.add_right
    (h.symm.smul_right c)).eq
  have e : J * (1 + j • J) = j • (1 + j • J) := by
    rw [mul_add, mul_smul_comm, hJ, mul_one, smul_add, smul_smul, hj1]
    rw [add_comm]; simp
  have : J * ((1 + c • X) * (1 + j • J)) = j • ((1 + c • X) * (1 + j • J)) := by
    rw [← mul_assoc, hJX, mul_assoc, e, mul_smul_comm]
  rw [mul_smul_comm, this, smul_comm]

/-- Right action: `Π(c, j) X = c Π(c, j)`. -/
theorem proj_mul_X {X J : A} (hX : X * X = 1) (h : Commute X J) {c : ℝ} (j : ℝ)
    (hc1 : c * c = 1) : proj X J c j * X = c • proj X J c j := by
  rw [← (commute_proj h c j).eq, X_mul_proj hX j hc1]

/-- Right action: `Π(c, j) J = j Π(c, j)`. -/
theorem proj_mul_J {X J : A} (hJ : J * J = 1) (h : Commute X J) (c : ℝ) {j : ℝ}
    (hj1 : j * j = 1) : proj X J c j * J = j • proj X J c j := by
  rw [← (commute_proj_J h c j).eq, J_mul_proj hJ h c hj1]

/-- **Idempotent:** `Π(c, j)² = Π(c, j)` for `c, j = ±1`. -/
theorem proj_idem {X J : A} (hX : X * X = 1) (hJ : J * J = 1) (h : Commute X J) {c j : ℝ}
    (hc1 : c * c = 1) (hj1 : j * j = 1) : proj X J c j * proj X J c j = proj X J c j := by
  have e1 : (1 + c • X) * proj X J c j = (2 : ℝ) • proj X J c j := by
    rw [add_mul, one_mul, smul_mul_assoc, X_mul_proj hX j hc1, smul_smul, hc1, one_smul, two_smul]
  have e2 : (1 + j • J) * proj X J c j = (2 : ℝ) • proj X J c j := by
    rw [add_mul, one_mul, smul_mul_assoc, J_mul_proj hJ h c hj1, smul_smul, hj1, one_smul, two_smul]
  have hP : proj X J c j = (1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J)) := rfl
  calc proj X J c j * proj X J c j
      = ((1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J))) * proj X J c j := by rw [← hP]
    _ = (1 / 4 : ℝ) • ((1 + c • X) * ((1 + j • J) * proj X J c j)) := by
        rw [smul_mul_assoc, mul_assoc]
    _ = proj X J c j := by
        rw [e2, mul_smul_comm, e1, smul_smul, smul_smul]; norm_num

/-- **Orthogonality in the `X`-sign:** `Π(c, j) Π(−c, j') = 0`. -/
theorem proj_mul_proj_X {X J : A} (hX : X * X = 1) (h : Commute X J) {c : ℝ} (hc1 : c * c = 1)
    (j j' : ℝ) : proj X J c j * proj X J (-c) j' = 0 := by
  have e : proj X J c j * (1 + (-c) • X) = 0 := by
    rw [mul_add, mul_one, mul_smul_comm, proj_mul_X hX h j hc1, smul_smul]
    rw [neg_mul, neg_smul, mul_comm, hc1, one_smul, add_neg_cancel]
  unfold proj at *
  rw [show ((1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J))) *
      ((1 / 4 : ℝ) • ((1 + (-c) • X) * (1 + j' • J))) =
      (1 / 4 : ℝ) • (((1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J))) *
        (((1 + (-c) • X) * (1 + j' • J)))) by rw [mul_smul_comm, smul_mul_assoc]]
  rw [← mul_assoc, show ((1 / 4 : ℝ) • ((1 + c • X) * (1 + j • J))) * (1 + (-c) • X) = 0 from e]
  simp

theorem proj_swap {X J : A} (h : Commute X J) (c j : ℝ) :
    proj X J c j = (1 / 4 : ℝ) • ((1 + j • J) * (1 + c • X)) := by
  have hc : Commute (1 + c • X) (1 + j • J) :=
    (Commute.one_left _).add_left ((commute_one_add_smul h j).smul_left c)
  unfold proj
  rw [hc.eq]

/-- **Orthogonality in the `J`-sign:** `Π(c, j) Π(c', −j) = 0`. -/
theorem proj_mul_proj_J {X J : A} (hJ : J * J = 1) (h : Commute X J) {j : ℝ} (hj1 : j * j = 1)
    (c c' : ℝ) : proj X J c j * proj X J c' (-j) = 0 := by
  have e : proj X J c j * (1 + (-j) • J) = 0 := by
    rw [mul_add, mul_one, mul_smul_comm, proj_mul_J hJ h c hj1, smul_smul]
    rw [neg_mul, neg_smul, mul_comm, hj1, one_smul, add_neg_cancel]
  rw [proj_swap h c' (-j), mul_smul_comm, ← mul_assoc, e]
  simp

/-- The four projections sum to `1`. -/
theorem proj_sum {X J : A} :
    proj X J 1 1 + proj X J 1 (-1) + proj X J (-1) 1 + proj X J (-1) (-1) = 1 := by
  unfold proj
  simp only [neg_smul, one_smul]
  have e : (1 + X) * (1 + J) + (1 + X) * (1 + -J) + (1 + -X) * (1 + J) + (1 + -X) * (1 + -J) =
      (4 : ℝ) • (1 : A) := by
    simp only [mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul]
    module
  rw [← smul_add, ← smul_add, ← smul_add, e, smul_smul]
  norm_num

/-- **Parity:** the global reflection `R = J X` acts on `Π(c, j)` by `c j`. -/
theorem refl_mul_proj {X J : A} (hX : X * X = 1) (hJ : J * J = 1) (h : Commute X J) {c j : ℝ}
    (hc1 : c * c = 1) (hj1 : j * j = 1) : (J * X) * proj X J c j = (c * j) • proj X J c j := by
  rw [mul_assoc, X_mul_proj hX j hc1, mul_smul_comm, J_mul_proj hJ h c hj1, smul_smul, mul_comm]

end GppKleinFour

#print axioms GppKleinFour.proj_idem
#print axioms GppKleinFour.proj_sum
#print axioms GppKleinFour.refl_mul_proj
#print axioms GppKleinFour.proj_mul_proj_X
#print axioms GppKleinFour.proj_mul_proj_J
