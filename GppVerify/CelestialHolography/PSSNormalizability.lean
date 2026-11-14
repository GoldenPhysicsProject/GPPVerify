import GppVerify.CelestialHolography.PSSRadialPairing

/-!
# PSS File 4: delta-normalisability iff principal series (radial form)

Pasterski–Shao, arXiv:1705.01027, (4.7)–(4.9) and §3, paragraph after (3.11). The KG pairing of
two massless conformal primaries `Δ_j = c + iν_j` is an angular delta times the radial integral
`∫_0^∞ ω^{2c − d + i(ν₁−ν₂) − 1} dω`. This is delta-function normalisable, i.e. a multiple of
`δ(ν₁ − ν₂)`, exactly on the principal series `Re Δ = d/2`.

## The definition (radial form)

`RadialDeltaNormalisable d Δ` has two parts. For the dimension `Δ` (real part `c = Re Δ`), the
family of truncated radial integrals `ν ↦ radialTrunc ((2c − d) + iν) R`, `ν = ν₁ − ν₂`, must:

1. stay bounded as `R → ∞` at every off-diagonal point `ν ≠ 0`; and
2. converge to `2π δ(ν)` against every continuous integrable test function with integrable
   Fourier transform, a class containing every Schwartz function.

## Results

* `radialDeltaNormalisable_iff`: `RadialDeltaNormalisable d Δ ↔ Δ.re = d/2`. Both directions
  are proved. (⇒) comes from part 1 alone (`radial_offDiagonalBounded_iff`); (⇐) is the
  distributional identity (4.8) (`tendsto_smeared_radialTrunc`). `c` is a free real parameter
  throughout: the criterion selects the line, it does not assume it.
* `radialDeltaNormalisable_iff_principal`: the same, as `∃ ν : ℝ, Δ = d/2 + iν`.
* `not_radialDeltaNormalisable_discrete`: **the discrete series** `Δ = d/2 + k`, `k ≥ 1`, is not
  delta-normalisable. This is the radial form of the §3 statement; the paper's own argument goes
  through the hyperboloid integral (3.12), which is not formalised here.
* `mellinPacket_critical_iff`: in the full-pairing form of File 3 (`kgPairing_mellinPacket`,
  conditional on the named OPEN obligation `PSSPacketPlancherel`), the radial exponent of the
  packet pairing lies on `Re = 0` iff `c = d/2`. The pairing statement itself (4.9) is therefore
  available only conditionally on that obligation; this file does not assert it.

The wall: imports only PSS File 3 (hence Files 1–2 and Mathlib). No arithmetic object appears.
-/

namespace GppPSSNormalizability

open Complex MeasureTheory Set Filter Topology FourierTransform
open GppPSSRadialPairing

/-- **Delta-normalisability, radial form.** For `c = Re Δ`, the truncated radial integrals with
exponent `(2c − d) + iν` are bounded off the diagonal and converge to `2π δ(ν)` on the test class
(continuous, integrable, integrable Fourier transform). -/
def RadialDeltaNormalisable (d : ℕ) (Δ : ℂ) : Prop :=
  OffDiagonalBounded (2 * Δ.re - d) ∧
    ∀ ψ : ℝ → ℂ, Continuous ψ → Integrable ψ → Integrable (𝓕 ψ) →
      Tendsto (fun R : ℝ => ∫ ν, ψ ν * radialTrunc (((2 * Δ.re - d : ℝ) : ℂ) + ν * I) R)
        atTop (𝓝 (2 * Real.pi * ψ 0))

/-- **PSS (4.7)–(4.9), radial form: delta-normalisable iff principal series.** -/
theorem radialDeltaNormalisable_iff (d : ℕ) (Δ : ℂ) :
    RadialDeltaNormalisable d Δ ↔ Δ.re = d / 2 := by
  constructor
  · rintro ⟨hb, -⟩
    exact (radial_offDiagonalBounded_iff Δ.re d).mp hb
  · intro h
    have h0 : (2 * Δ.re - d : ℝ) = 0 := by rw [h]; ring
    refine ⟨(radial_offDiagonalBounded_iff Δ.re d).mpr h, fun ψ hc hi hF => ?_⟩
    rw [h0]
    simpa using tendsto_smeared_radialTrunc hc hi hF

/-- **Principal-series form.** `RadialDeltaNormalisable d Δ ↔ ∃ ν : ℝ, Δ = d/2 + iν`. -/
theorem radialDeltaNormalisable_iff_principal (d : ℕ) (Δ : ℂ) :
    RadialDeltaNormalisable d Δ ↔ ∃ ν : ℝ, Δ = (d : ℂ) / 2 + ν * I := by
  rw [radialDeltaNormalisable_iff]
  constructor
  · intro h
    refine ⟨Δ.im, ?_⟩
    apply Complex.ext <;> simp [h]
  · rintro ⟨ν, rfl⟩
    simp

/-- **The discrete series is not delta-normalisable** (radial form). For every `k ≥ 1`,
`Δ = d/2 + k` fails the criterion. -/
theorem not_radialDeltaNormalisable_discrete (d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ¬ RadialDeltaNormalisable d ((d : ℂ) / 2 + k) := by
  rw [radialDeltaNormalisable_iff]
  intro h
  have hre : ((d : ℂ) / 2 + k).re = d / 2 + k := by simp
  rw [hre] at h
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- **Full-pairing form, conditional.** In File 3's reduction (`kgPairing_mellinPacket`, which
assumes the named OPEN obligation `PSSPacketPlancherel`), the radial exponent
`(2c − d) + i(ν₁ − ν₂)` has real part `0` iff `c = d/2`. -/
theorem mellinPacket_critical_iff (d : ℕ) (c ν₁ ν₂ : ℝ) :
    ((((2 * c - d : ℝ) : ℂ) + (ν₁ - ν₂ : ℝ) * I).re = 0) ↔ c = d / 2 := by
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  constructor <;> intro h <;> linarith

end GppPSSNormalizability

#print axioms GppPSSNormalizability.radialDeltaNormalisable_iff
#print axioms GppPSSNormalizability.radialDeltaNormalisable_iff_principal
#print axioms GppPSSNormalizability.not_radialDeltaNormalisable_discrete
#print axioms GppPSSNormalizability.mellinPacket_critical_iff
