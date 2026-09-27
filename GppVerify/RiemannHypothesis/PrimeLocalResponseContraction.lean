import GppVerify.RiemannHypothesis.GlobalPrimePoissonBound
import Mathlib.Tactic

/-!
# Local prime-response contractions and finite local-to-global products

Each radial prime-Poisson kernel is even and positive type, hence its absolute
value is bounded by its zero-frequency value.  Normalizing by `1 + W_p(a,0)`
therefore gives a canonical scalar contraction for each local prime component.
Finite products of these local contractions remain contractive.  This is a
local-to-global structural bridge only; no identification with the completed
Weil transfer operator or RH claim is made.
-/

namespace GppPrimeLocalResponseContraction

open GppCutkoskyWeil GppPrimePoissonRadial
open GppPrimePoissonRadialPositiveType
open GppPositiveTypeEvenBound
open GppGlobalPrimePoissonBound

/-- A local prime-Poisson response is bounded by its zero-frequency value. -/
theorem abs_WpA_le_zero {p a : ℝ} (hp : 1 < p) (ha : 0 < a) (t : ℝ) :
    |WpA p a t| ≤ WpA p a 0 := by
  exact abs_le_at_zero_of_even_positiveType
    (WpA_positiveType hp ha) (fun u => WpA_neg p a u) t

/-- In particular the local zero-frequency response is nonnegative. -/
theorem WpA_zero_nonneg {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    0 ≤ WpA p a 0 := by
  have h := abs_WpA_le_zero hp ha 0
  exact abs_le_self_iff.mp h

/-- Canonically normalized local arithmetic transfer factor. -/
noncomputable def localTransfer (p a t : ℝ) : ℝ :=
  WpA p a t / (1 + WpA p a 0)

/-- Every local transfer factor is contractive. -/
theorem abs_localTransfer_le_one {p a : ℝ} (hp : 1 < p) (ha : 0 < a) (t : ℝ) :
    |localTransfer p a t| ≤ 1 := by
  have h0 : 0 ≤ WpA p a 0 := WpA_zero_nonneg hp ha
  have hden : 0 < 1 + WpA p a 0 := by linarith
  have ht : |WpA p a t| ≤ WpA p a 0 := abs_WpA_le_zero hp ha t
  unfold localTransfer
  rw [abs_div, abs_of_pos hden]
  exact (div_le_one hden).2 (le_trans ht (by linarith))

/-- Finite product of local prime transfer factors. -/
noncomputable def finiteLocalTransfer (S : Finset ℕ) (a t : ℝ) : ℝ :=
  ∏ p ∈ S, localTransfer (p : ℝ) a t

/-- Finite local-to-global products remain scalar contractions. -/
theorem abs_finiteLocalTransfer_le_one
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |finiteLocalTransfer S a t| ≤ 1 := by
  classical
  unfold finiteLocalTransfer
  rw [abs_prod]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hS
      rw [Finset.prod_insert hp]
      have hp1 : |localTransfer (p : ℝ) a t| ≤ 1 :=
        abs_localTransfer_le_one (by exact_mod_cast hS.1) ha t
      have hS1 : |∏ q ∈ S, localTransfer (q : ℝ) a t| ≤ 1 := by
        apply ih hS.2
      have hp0 : 0 ≤ |localTransfer (p : ℝ) a t| := abs_nonneg _
      have hprod0 : 0 ≤ |∏ q ∈ S, localTransfer (q : ℝ) a t| := abs_nonneg _
      nlinarith [mul_le_mul hp1 hS1 hp0 hprod0]

end GppPrimeLocalResponseContraction

#print axioms GppPrimeLocalResponseContraction.abs_WpA_le_zero
#print axioms GppPrimeLocalResponseContraction.abs_localTransfer_le_one
#print axioms GppPrimeLocalResponseContraction.abs_finiteLocalTransfer_le_one
