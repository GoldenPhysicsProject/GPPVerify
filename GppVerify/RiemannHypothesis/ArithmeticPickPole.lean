import Mathlib.Tactic

/-!
# Arithmetic Pick kernel: finite two-node determinant and Euler-pole obstruction

Astra's Pick matrix for real Euler-region inputs has entries
`(F(sᵢ) + F(sⱼ)) / (sᵢ+sⱼ-1)`.
With centered parameters `a=sᵢ-1/2`, `b=sⱼ-1/2`,
it becomes `(f(a)+f(b))/(a+b)`.

This module proves the exact two-node determinant identity. It also proves
that the isolated simple Euler pole `1/(s-1)`, expressed as
`f(a)=1/(a-1/2)`, has *negative* Pick determinant at every pair of
distinct Euler-real nodes. Therefore the finite-prime approximation
(which retains that pole) cannot be certified term by term: the actual
infinite prime contribution must cancel the singular pole.

NO RH proof, NO assumption that the entire completed arithmetic kernel is
positive, and NO assertion about arbitrary Pick-matrix sizes.
-/

namespace GppArithmeticPickPole

noncomputable section

/-- The two-by-two Pick determinant with diagonal entries `u/a`, `v/b`
    and off-diagonal entry `(u+v)/(a+b)`. -/
def twoNodeDet (a b u v : ℝ) : ℝ :=
  u / a * (v / b) - ((u + v) / (a + b)) ^ 2

/-- Exact rational two-node determinant identity for arbitrary real data. -/
theorem twoNodeDet_identity {a b u v : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    twoNodeDet a b u v =
      ((a - b) ^ 2 * u * v - a * b * (u - v) ^ 2) /
        (a * b * (a + b) ^ 2) := by
  unfold twoNodeDet
  field_simp
  ring

/-- The isolated boundary pole has an explicit sign-definite determinant. -/
theorem poleDet_identity {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hac : a - c ≠ 0) (hbc : b - c ≠ 0) :
    twoNodeDet a b (1 / (a - c)) (1 / (b - c)) =
      (a - b) ^ 2 * c * (c - a - b) /
        (a * b * (a + b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2) := by
  unfold twoNodeDet
  field_simp
  ring

/-- A pole at positive `c` has negative two-point Pick determinant
    for every distinct `a,b>c`: the gamma/pole term cannot be
    declared positive without the infinite Euler prime contribution. -/
theorem poleDet_neg {a b c : ℝ}
    (hc : 0 < c) (hca : c < a) (hcb : c < b) (hneq : a ≠ b) :
    twoNodeDet a b (1 / (a - c)) (1 / (b - c)) < 0 := by
  have ha : 0 < a := lt_trans hc hca
  have hb : 0 < b := lt_trans hc hcb
  have hab : 0 < a + b := add_pos ha hb
  have hac : 0 < a - c := sub_pos.mpr hca
  have hbc : 0 < b - c := sub_pos.mpr hcb
  rw [poleDet_identity ha.ne' hb.ne' hab.ne' hac.ne' hbc.ne']
  have hab2 : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
  have hneg : c - a - b < 0 := by linarith
  have hn : (a - b) ^ 2 * c * (c - a - b) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hab2 hc) hneg
  have hd : 0 < a * b * (a + b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 := by
    positivity
  exact div_neg_of_neg_of_pos hn hd

/-- The real Euler pole `1/(s-1)` alone violates the Pick condition
    even on arbitrarily close distinct real inputs `s,t>1`. -/
theorem eulerPole_twoNodeDet_neg {s t : ℝ}
    (hs : 1 < s) (ht : 1 < t) (hne : s ≠ t) :
    twoNodeDet (s - 1 / 2) (t - 1 / 2)
      (1 / (s - 1)) (1 / (t - 1)) < 0 := by
  have hne' : s - (1 / 2 : ℝ) ≠ t - 1 / 2 := sub_ne_sub_right hne _
  have h := poleDet_neg (a := s - 1 / 2) (b := t - 1 / 2)
    (c := 1 / 2) (by norm_num) (by linarith) (by linarith) hne'
  convert h using 1 <; ring

/-- The exact rational imaginary logarithmic derivative of Astra's even
    quartet polynomial
    `((k-14)^2+(1/5)^2)*((k+14)^2+(1/5)^2)`,
    evaluated at the imaginary input `k=i*y`.
    Here `y=s-1/2>1/2`, so `s>1`. -/
def quartetValue (y : ℚ) : ℚ :=
  2 * ((y - 1 / 5) / (14 ^ 2 + (y - 1 / 5) ^ 2) +
       (y + 1 / 5) / (14 ^ 2 + (y + 1 / 5) ^ 2))

/-- The rational Pick kernel restricted to real Euler inputs. -/
def quartetPick (a b : ℚ) : ℚ :=
  (quartetValue a + quartetValue b) / (a + b)

/-- Explicit three-by-three symmetric determinant. -/
def symmetricDet3 (a b c d e f : ℚ) : ℚ :=
  a * (d * f - e ^ 2) -
  b * (b * f - c * e) +
  c * (b * e - c * d)

/-- Exact synthetic quartet Pick determinant at the three REAL Euler nodes
    `s=11/10, 3/2, 5/2`, i.e. centered inputs `3/5,1,2`.
    This closes Astra's real-node adversarial witness without zeros or
    numerical tolerance. The result is explicitly negative. -/
theorem quartet_real_euler_three_node_negative :
    symmetricDet3
      (quartetPick (3 / 5) (3 / 5))
      (quartetPick (3 / 5) 1)
      (quartetPick (3 / 5) 2)
      (quartetPick 1 1)
      (quartetPick 1 2)
      (quartetPick 2 2) < 0 := by
  norm_num [symmetricDet3, quartetPick, quartetValue]

/-- The exact determinant is a negative rational, with a stated value
    independently checked by symbolic fraction arithmetic. -/
theorem quartet_real_euler_det_value :
    symmetricDet3
      (quartetPick (3 / 5) (3 / 5))
      (quartetPick (3 / 5) 1)
      (quartetPick (3 / 5) 2)
      (quartetPick 1 1)
      (quartetPick 1 2)
      (quartetPick 2 2) =
      -(176434183789130859375 / 664385955512796181542237813770638196 : ℚ) := by
  norm_num [symmetricDet3, quartetPick, quartetValue]

/-- Direct arithmetic quadratic form of the three-real-node Pick matrix.
    The six entries are computed independently from the off-axis quartet,
    and the argument is the test vector `(u,v,w)`. -/
def quartetQuadratic (u v w : ℚ) : ℚ :=
  u ^ 2 * quartetPick (3 / 5) (3 / 5) +
  v ^ 2 * quartetPick 1 1 +
  w ^ 2 * quartetPick 2 2 +
  2 * u * v * quartetPick (3 / 5) 1 +
  2 * u * w * quartetPick (3 / 5) 2 +
  2 * v * w * quartetPick 1 2

/-- A short, exact, integer-coefficient NEGATIVE witness against the
    synthetic off-line quartet at real Euler-region nodes. -/
theorem quartet_integer_vector_exact :
    quartetQuadratic (-4909) 6895 (-2000) =
      -(36832026069825 / 11625303092480009 : ℚ) := by
  norm_num [quartetQuadratic, quartetPick, quartetValue]

theorem quartet_integer_vector_negative :
    quartetQuadratic (-4909) 6895 (-2000) < 0 := by
  rw [quartet_integer_vector_exact]
  norm_num

/-- On-line control (displacement zero): the same rational test vector lies
    in the nullspace of the rank-two on-line Gram form, exactly. -/
def onLineQuartetValue (y : ℚ) : ℚ :=
  4 * y / (14 ^ 2 + y ^ 2)

def onLineQuartetPick (a b : ℚ) : ℚ :=
  (onLineQuartetValue a + onLineQuartetValue b) / (a + b)

def onLineQuartetQuadratic (u v w : ℚ) : ℚ :=
  u ^ 2 * onLineQuartetPick (3 / 5) (3 / 5) +
  v ^ 2 * onLineQuartetPick 1 1 +
  w ^ 2 * onLineQuartetPick 2 2 +
  2 * u * v * onLineQuartetPick (3 / 5) 1 +
  2 * u * w * onLineQuartetPick (3 / 5) 2 +
  2 * v * w * onLineQuartetPick 1 2

theorem onLineQuartet_integer_null :
    onLineQuartetQuadratic (-4909) 6895 (-2000) = 0 := by
  norm_num [onLineQuartetQuadratic, onLineQuartetPick, onLineQuartetValue]

/-- The real-node logarithmic derivative of one symmetric quartet, written
    in the folded spectral variables `h=γ²-δ²`, `w=4γ²δ²`. -/
def foldedQuartetDen (h w a : ℝ) : ℝ :=
  (a ^ 2 + h) ^ 2 + w

def foldedQuartetValue (h w a : ℝ) : ℝ :=
  4 * a * (a ^ 2 + h) / foldedQuartetDen h w a

/-- Complete two-point Pick determinant factorization, without assuming
    that a complex quartet lies on the principal line. -/
theorem foldedQuartetDet_factor {a b h w : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hDa : foldedQuartetDen h w a ≠ 0)
    (hDb : foldedQuartetDen h w b ≠ 0) :
    twoNodeDet a b (foldedQuartetValue h w a)
      (foldedQuartetValue h w b) =
      16 * (a - b) ^ 2 *
        ((a ^ 2 + h) * (b ^ 2 + h) - w) *
        (h * (a ^ 2 + h) * (b ^ 2 + h) +
          w * (h + a ^ 2 + b ^ 2)) /
        ((foldedQuartetDen h w a) ^ 2 *
          (foldedQuartetDen h w b) ^ 2) := by
  unfold twoNodeDet foldedQuartetValue foldedQuartetDen at *
  field_simp
  ring

/-- Even an OFF-LINE quartet has strictly positive *all* two-point real
    Pick determinants when its ordinate dominates the horizontal
    displacement. Hence testing only order-two minors cannot certify RH. -/
theorem foldedQuartet_twoPoint_pos {a b h w : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hw : 0 ≤ w) (hlarge : w ≤ h ^ 2)
    (hab : a ≠ b) :
    0 < twoNodeDet a b (foldedQuartetValue h w a)
      (foldedQuartetValue h w b) := by
  have hda : 0 < foldedQuartetDen h w a := by
    unfold foldedQuartetDen
    positivity
  have hdb : 0 < foldedQuartetDen h w b := by
    unfold foldedQuartetDen
    positivity
  rw [foldedQuartetDet_factor ha.ne' hb.ne' (add_pos ha hb).ne'
      hda.ne' hdb.ne']
  have hsq : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have habpos : 0 < a ^ 2 + b ^ 2 := by positivity
  have hdiff : 0 ≤ h ^ 2 - w := sub_nonneg.mpr hlarge
  have hA : 0 < (a ^ 2 + h) * (b ^ 2 + h) - w := by
    calc
      (a ^ 2 + h) * (b ^ 2 + h) - w =
          a ^ 2 * b ^ 2 + h * (a ^ 2 + b ^ 2) + (h ^ 2 - w) := by ring
      _ > 0 := by positivity
  have hB : 0 <
      h * (a ^ 2 + h) * (b ^ 2 + h) +
        w * (h + a ^ 2 + b ^ 2) := by
    positivity
  have hden : 0 <
      (foldedQuartetDen h w a) ^ 2 *
        (foldedQuartetDen h w b) ^ 2 := by positivity
  positivity

end

end GppArithmeticPickPole

#check @GppArithmeticPickPole.twoNodeDet_identity
#check @GppArithmeticPickPole.poleDet_identity
#check @GppArithmeticPickPole.poleDet_neg
#check @GppArithmeticPickPole.eulerPole_twoNodeDet_neg
