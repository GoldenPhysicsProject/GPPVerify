import GppVerify.RiemannHypothesis.OddFaceSineAtoms
import GppVerify.RiemannHypothesis.KreinHPsi
import GppVerify.RiemannHypothesis.WeilHAFiniteRange
import GppVerify.RiemannHypothesis.WeilHRho

/-!
# The odd-face semilocal frame `𝔽_L` as Lean definitions, and UB stated in it

Build order (i)–(ii) of Turbo's funded-trajectory entry (bridge `9eaf136`), with the frame specification
of Flint (bridge `9f868af`) and Turbo's four normalisations (bridge `e2e9700`). **Definitions, plus two
conditional theorems; nothing about ARP, RH, OB-6 or UB is proved.**

## The frame, as definitions over in-tree objects

* The kernel is the in-tree `GppKreinHPsi.Kpsi` (pole − prime + arch, with the triangle window). The odd-face
  kernel is `G(s,u) = ½[Kψ(s−u) − Kψ(s+u)]` (`oddKernel`). Because `Kψ` carries the triG window, the semilocal
  prime set `S_L = {n : log n ≤ 2 + L}` is *automatic* for `|s ± u| ≤ L`; nothing is truncated by hand.
* The modes are the in-tree sine atoms `GppOddFaceAtoms.phi ℓ j`; `ℓ = L/2` is **frame data**.
* `Mgram`, `uBorder`, `gBorder`: `M_jk = ∬ G φ_j φ_k`, `u_j = ∫₀^ℓ G(s, ℓ) φ_j(s) ds`, `g = G(ℓ, ℓ)`.
* `St = M − uuᵀ/g` (δ-elimination), and `Aeff = S_Z^eff = St_ZZ − St_ZY St_YY⁻¹ St_YZ`
  (Y-Schur complement), `Anorm = D^{-1/2} A D^{-1/2}`.
* The split is **frame data**: `FrameCut N K J` (X = 1..N, Y = N+1..N+K, Z = N+K+1..J). At `L = 0.5`:
  `ℓ = 1/4`, `frame05 = ⟨12, 60, 812⟩`, so `Z = 73..812`. **The general-`L` cutoff rule is NOT PINNED**
  (`T_*(L)` is Daniel's to ratify): `UB` therefore takes the rule as an argument.

**Numerical consistency check (not a certificate; `work/claude-code/frame/kernel_check.py` on the bridge).**
With the in-tree `Kpsi` evaluated in float64 at `ℓ = 1/4`: `g = 1.23787487e-4` against the filed Arb ball
`1.2378750e-4 ± 3e-12` (agreement `1.3e-11`, within the truncation of the arch integral), and
`u_1 = −3.44337863793e-5` against the filed `−3.443378638e-5` (agreement to the digits filed). The kernel-form
definitions here therefore reproduce Flint's `g` and `u_1`. **The `A_jj` of the 740 balls has *not* been
recomputed from these definitions** — that needs run 16's multi-precision pipeline.

## Conditional theorems at `L = 0.5` (named ball hypotheses, not proved)

* `uba_L05_of_balls`: if `aLo j ≤ Aeff (1/4) frame05 j j` for `j = 73..812` (Flint's lower endpoints, the
  ball hypothesis), then the (UB-A) clause holds with `c_A = 867483/500000` — from `WeilHAFiniteRange` (#610).
* `ubr_L05_of_balls`: if `|Anorm i j| ≤ s_ij/2³²` off the diagonal (Flint's entry balls), then every
  normalised off-diagonal row sum on `Z` is `≤ 3632727590/2³²` — from `WeilHRho.rowOk_all` (#610).

The hypotheses say that the *kernel-defined* `Aeff` lies in balls computed by run 16 in its *spectral*
presentation; that identification of presentations is **OPEN** (the kernel/spectral equality is a
paper-level CHECKED statement, and `St` is not the `linearZeta` Gram). No `sorry`, no axiom.
-/

open intervalIntegral Finset Matrix
open GppKreinHPsi GppOddFaceAtoms

noncomputable section

namespace GppOddFaceFrame

/-- The odd-face kernel `G(s,u) = ½[Kψ(s−u) − Kψ(s+u)]`. -/
def oddKernel (s u : ℝ) : ℝ := (Kpsi (s - u) - Kpsi (s + u)) / 2

/-- `M_jk = ∫₀^ℓ∫₀^ℓ G(s,u) φ_j(s) φ_k(u) du ds`. -/
def Mgram (ℓ : ℝ) (j k : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..ℓ, ∫ u in (0 : ℝ)..ℓ, oddKernel s u * phi ℓ j s * phi ℓ k u

/-- `u_j = B(φ_j, δ_ℓ) = ∫₀^ℓ G(s, ℓ) φ_j(s) ds`. -/
def uBorder (ℓ : ℝ) (j : ℕ) : ℝ := ∫ s in (0 : ℝ)..ℓ, oddKernel s ℓ * phi ℓ j s

/-- `g = B(δ_ℓ, δ_ℓ) = G(ℓ, ℓ)`. -/
def gBorder (ℓ : ℝ) : ℝ := oddKernel ℓ ℓ

/-- `St = M − uuᵀ/g`: the bordered Gram after δ-elimination. -/
def St (ℓ : ℝ) (j k : ℕ) : ℝ := Mgram ℓ j k - uBorder ℓ j * uBorder ℓ k / gBorder ℓ

/-- **Frame data**: the X/Y/Z split. `X = 1..N`, `Y = N+1..N+K`, `Z = N+K+1..J`. -/
structure FrameCut where
  N : ℕ
  K : ℕ
  J : ℕ

/-- The `Y × Y` block of `St`. -/
def stYY (ℓ : ℝ) (c : FrameCut) : Matrix (Fin c.K) (Fin c.K) ℝ :=
  Matrix.of fun a b => St ℓ (c.N + 1 + a) (c.N + 1 + b)

/-- The `Z` index set. -/
def Zset (c : FrameCut) : Finset ℕ := Finset.Icc (c.N + c.K + 1) c.J

/-- **`A = S_Z^eff = St_ZZ − St_ZY St_YY⁻¹ St_YZ`.** (`⁻¹` is Mathlib's matrix inverse: it is the
inverse exactly when `St_YY` is nonsingular, which the construction presupposes.) -/
def Aeff (ℓ : ℝ) (c : FrameCut) (j k : ℕ) : ℝ :=
  St ℓ j k - ∑ a : Fin c.K, ∑ b : Fin c.K,
    St ℓ j (c.N + 1 + a) * (stYY ℓ c)⁻¹ a b * St ℓ (c.N + 1 + b) k

/-- `Ã = D^{-1/2} A D^{-1/2}`. -/
def Anorm (ℓ : ℝ) (c : FrameCut) (j k : ℕ) : ℝ :=
  Aeff ℓ c j k / (Real.sqrt (Aeff ℓ c j j) * Real.sqrt (Aeff ℓ c k k))

/-- **(UB-A) at a frame**: `A_jj ≥ c_A · log ω_j / ω_j⁴`, `ω_j = jπ/ℓ`, on `Z`. -/
def UBAAt (ℓ : ℝ) (c : FrameCut) (cA : ℝ) : Prop :=
  ∀ j ∈ Zset c, cA * Real.log (om ℓ j) / (om ℓ j) ^ 4 ≤ Aeff ℓ c j j

/-- **(UB-R) at a frame**: every normalised off-diagonal row sum on `Z` is `≤ ρ`. -/
def UBRAt (ℓ : ℝ) (c : FrameCut) (ρ : ℝ) : Prop :=
  ∀ j ∈ Zset c, ∑ k ∈ (Zset c).erase j, |Anorm ℓ c j k| ≤ ρ

/-- **UB at a frame** (both clauses). -/
def UBAt (ℓ : ℝ) (c : FrameCut) (cA ρ : ℝ) : Prop := UBAAt ℓ c cA ∧ UBRAt ℓ c ρ

/-- **UB** (the open conjecture), for a *given* cutoff rule `L ↦ (N, K, J)` (the rule is NOT PINNED —
`T_*(L)` is to be ratified — so it is an argument): there are `c_A* > 0` and `ρ* < 1`, independent of `L`,
with `UBAt (L/2) (rule L) c_A* ρ*` for every width `L ≥ 1/2`. **OPEN.** -/
def UB (rule : ℝ → FrameCut) : Prop :=
  ∃ cA ρ : ℝ, 0 < cA ∧ ρ < 1 ∧ ∀ L : ℝ, 1 / 2 ≤ L → UBAt (L / 2) (rule L) cA ρ

/-- The `L = 0.5` frame: `ℓ = 1/4`, `X = 1..12`, `Y = 13..72`, `Z = 73..812`. -/
def frame05 : FrameCut := ⟨12, 60, 812⟩

theorem Zset_frame05 : Zset frame05 = Finset.Icc 73 812 := rfl

/-! ### Conditional bridges to the kernel-checked finite faces (#610) -/

theorem om_quarter (j : ℕ) : om (1 / 4) j = 4 * Real.pi * j := by
  unfold om; ring

/-- **(UB-A) at `L = 0.5`, from Flint's lower endpoints.** The hypothesis — that the kernel-defined `Aeff`
lies above the exported lower endpoints — is the ball hypothesis, **not** proved. -/
theorem uba_L05_of_balls
    (hball : ∀ j ∈ Zset frame05, (GppWeilHA.aLo j : ℝ) ≤ Aeff (1 / 4) frame05 j j) :
    UBAAt (1 / 4) frame05 (867483 / 500000) := by
  intro j hj
  rw [Zset_frame05, Finset.mem_Icc] at hj
  rw [om_quarter]
  have h := GppWeilHA.floor_of_lower_endpoint j hj.1 hj.2 _ (hball j (by
    rw [Zset_frame05, Finset.mem_Icc]; exact hj))
  have e : ((GppWeilHA.cA : ℚ) : ℝ) = 867483 / 500000 := by norm_num [GppWeilHA.cA]
  rwa [e] at h

/-- **(UB-R) at `L = 0.5`, from Flint's entry balls.** Given `|Ã_ij| ≤ s_ij / 2³²` for `i ≠ j` on `Z`
(the ball hypothesis, **not** proved), every normalised off-diagonal row sum is `≤ 3632727590/2³²`. -/
theorem ubr_L05_of_balls
    (hoff : ∀ i ∈ Zset frame05, ∀ j ∈ Zset frame05, i ≠ j →
      |Anorm (1 / 4) frame05 i j| ≤ (GppWeilHRho.sSym (i - 73) (j - 73) : ℝ) / 2 ^ 32) :
    UBRAt (1 / 4) frame05 ((GppWeilHRho.rowBound : ℝ) / 2 ^ 32) := by
  intro j hj
  have hj' := hj
  rw [Zset_frame05, Finset.mem_Icc] at hj'
  have hle : ∑ k ∈ (Zset frame05).erase j, |Anorm (1 / 4) frame05 j k| ≤
      ∑ k ∈ (Zset frame05).erase j, (GppWeilHRho.sSym (j - 73) (k - 73) : ℝ) / 2 ^ 32 :=
    Finset.sum_le_sum fun k hk =>
      hoff j hj k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk).symm
  refine hle.trans ?_
  rw [← Finset.sum_div]
  have hsum : ∑ k ∈ (Zset frame05).erase j, (GppWeilHRho.sSym (j - 73) (k - 73) : ℝ) =
      ∑ i ∈ Finset.range 740, (GppWeilHRho.sSym (j - 73) i : ℝ) := by
    have himg : (Zset frame05).erase j = ((Finset.range 740).erase (j - 73)).image (· + 73) := by
      ext k
      simp only [Finset.mem_erase, Zset_frame05, Finset.mem_Icc, Finset.mem_image,
        Finset.mem_range]
      constructor
      · rintro ⟨hne, h1, h2⟩
        exact ⟨k - 73, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        exact ⟨by omega, by omega, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_erase _ (by simp [GppWeilHRho.sSym_self])]
  rw [hsum]
  have hrow := GppWeilHRho.rowOk_all (j - 73) (by omega)
  have hrow' : (∑ i ∈ Finset.range 740, GppWeilHRho.sSym (j - 73) i) ≤ GppWeilHRho.rowBound := by
    omega
  have : (∑ i ∈ Finset.range 740, (GppWeilHRho.sSym (j - 73) i : ℝ)) ≤ (GppWeilHRho.rowBound : ℝ) := by
    exact_mod_cast hrow'
  exact div_le_div_of_nonneg_right this (by positivity)

end GppOddFaceFrame

#print axioms GppOddFaceFrame.uba_L05_of_balls
#print axioms GppOddFaceFrame.ubr_L05_of_balls
