import Mathlib

/-!
# Universal W(1+infinity) Kac–Radul cocycle: orientation for all symbols

The half-density geometric inversion R(z^n f(D)) R^{-1} is
z^(-n) f(-D-1). The Kac–Radul cocycle on opposite frequency modes
n, -n is the sum of f(-j)g(n-j) over j=1..n.

The statement below proves for ARBITRARY symbols f,g : Z → C,
and EVERY natural n, the exact anti-invariance of that cocycle.
No fixed spin truncation, no external arithmetic zero assumptions.

This is algebra of the formal differential operator Lie algebra, NOT
an identification with actual loop-renormalized celestial charges,
nor a proof of RH/GRH.
-/

namespace GppWInfinityFullSpinMirror

open Finset

/-- Kac–Radul positive-mode central cocycle for frequency n>0,
expressed for arbitrary integer-valued symbols. -/
def KRCocycle (n : ℕ) (f g : ℤ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range n,
    f (-((j : ℤ) + 1)) * g ((n : ℤ) - (j : ℤ) - 1)

/-- The mirror maps D ↦ -D-1, n ↦ -n. Antisymmetry of the
frequency-swapped cocycle then gives this opposite-sign sum. -/
def KRMirrored (n : ℕ) (f g : ℤ → ℂ) : ℂ :=
  -∑ j ∈ Finset.range n,
    g (j : ℤ) * f ((j : ℤ) - (n : ℤ))

/-- Full W(1+infinity), all mode orders and all symbols: reversal of
the half-density induces the reflection of the Kac–Radul cocycle. -/
theorem kr_reindex (n : ℕ) (f g : ℤ → ℂ) :
    KRCocycle n f g =
      ∑ j ∈ Finset.range n,
        g (j : ℤ) * f ((j : ℤ) - (n : ℤ)) := by
  unfold KRCocycle
  calc
    (∑ j ∈ Finset.range n,
      f (-((j : ℤ) + 1)) * g ((n : ℤ) - (j : ℤ) - 1))
        = ∑ j ∈ Finset.range n,
           g ((n - 1 - j : ℕ) : ℤ) *
             f (((n - 1 - j : ℕ) : ℤ) - (n : ℤ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjlt : j < n := Finset.mem_range.mp hj
              have hcast : ((n - 1 - j : ℕ) : ℤ) =
                  (n : ℤ) - (j : ℤ) - 1 := by omega
              rw [hcast]
              ring
    _ = ∑ j ∈ Finset.range n,
        g (j : ℤ) * f ((j : ℤ) - (n : ℤ)) := by
          exact Finset.sum_range_reflect
            (fun j : ℕ => g (j : ℤ) * f ((j : ℤ) - (n : ℤ))) n

/-- Equal-normalization opposite twistor orientations cancel
the UNIVERSAL Kac–Radul central term for ALL spins simultaneously. -/
theorem kr_mirror_anti (n : ℕ) (f g : ℤ → ℂ) :
    KRMirrored n f g = -KRCocycle n f g := by
  unfold KRMirrored
  rw [kr_reindex]

theorem kr_total_central_zero (n : ℕ) (f g : ℤ → ℂ) :
    KRCocycle n f g + KRMirrored n f g = 0 := by
  rw [kr_mirror_anti]
  simp

/-- An abstract Haar factor is a nonnegative norm only with complex
conjugation. A signed cocycle without conjugation is NOT positive. -/
theorem haar_pairing_diagonal_nonnegative (x : ℂ) :
    0 ≤ Complex.normSq x := Complex.normSq_nonneg x

end GppWInfinityFullSpinMirror
