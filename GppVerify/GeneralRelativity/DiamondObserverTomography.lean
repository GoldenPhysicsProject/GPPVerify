import Mathlib.Tactic

/-!
# Timelike observer tomography for a symmetric spacetime constraint tensor

For a symmetric rank-two tensor S_{μν} on a 3+1 Lorentzian tangent
space, the contraction S_{μν} u^μ u^ν is a quadratic polynomial in
the spatial components of a vector u=(1,v), where |v|<1 is timelike.

A finite set of ten timelike probe directions suffices to reconstruct
all ten independent components of S: the rest observer, the six axial
observers with v=±e_i/4, and three mixed observers with
v=(e_i+e_j)/4. Their spatial speeds are 0, 1/4 and 1/sqrt(8),
all strictly below light speed.

This is exact linear algebra, with no general relativity or QFT
assumption. When the *physical* family of small-diamond scalar
Hamiltonian constraints is available for all these observer frames,
the tensor residual at a point vanishes. It does not establish
independent modular/KMS response for every boosted observer; that
remains a physical hypothesis.
-/

namespace GppDiamondObserverTomography

/-- Quadratic contraction of a symmetric (0,2) tensor with the
unnormalized timelike vector (1,x,y,z).
a=S00, bi=S0i and cij=Sij, with cij symmetric. -/
noncomputable def contract
    (a bx by bz cxx cyy czz cxy cxz cyz x y z : ℝ) : ℝ :=
  a + 2*(bx*x + by*y + bz*z) +
    cxx*x^2 + cyy*y^2 + czz*z^2 +
    2*(cxy*x*y + cxz*x*z + cyz*y*z)

/-- All ten independent tensor entries are determined by ten
timelike contractions, each exactly zero. No need for all vectors. -/
theorem ten_timelike_contractions_force_zero
    (a bx by bz cxx cyy czz cxy cxz cyz : ℝ)
    (h0 : contract a bx by bz cxx cyy czz cxy cxz cyz 0 0 0 = 0)
    (hxp : contract a bx by bz cxx cyy czz cxy cxz cyz (1/4) 0 0 = 0)
    (hxm : contract a bx by bz cxx cyy czz cxy cxz cyz (-1/4) 0 0 = 0)
    (hyp : contract a bx by bz cxx cyy czz cxy cxz cyz 0 (1/4) 0 = 0)
    (hym : contract a bx by bz cxx cyy czz cxy cxz cyz 0 (-1/4) 0 = 0)
    (hzp : contract a bx by bz cxx cyy czz cxy cxz cyz 0 0 (1/4) = 0)
    (hzm : contract a bx by bz cxx cyy czz cxy cxz cyz 0 0 (-1/4) = 0)
    (hxy : contract a bx by bz cxx cyy czz cxy cxz cyz (1/4) (1/4) 0 = 0)
    (hxz : contract a bx by bz cxx cyy czz cxy cxz cyz (1/4) 0 (1/4) = 0)
    (hyz : contract a bx by bz cxx cyy czz cxy cxz cyz 0 (1/4) (1/4) = 0) :
    a = 0 ∧ bx = 0 ∧ by = 0 ∧ bz = 0 ∧
    cxx = 0 ∧ cyy = 0 ∧ czz = 0 ∧
    cxy = 0 ∧ cxz = 0 ∧ cyz = 0 := by
  unfold contract at *
  norm_num at h0 hxp hxm hyp hym hzp hzm hxy hxz hyz
  have ha : a = 0 := by linarith
  have hbx : bx = 0 := by linarith [hxp,hxm]
  have hby : by = 0 := by linarith [hyp,hym]
  have hbz : bz = 0 := by linarith [hzp,hzm]
  have hcxx : cxx = 0 := by linarith [hxp,hxm]
  have hcyy : cyy = 0 := by linarith [hyp,hym]
  have hczz : czz = 0 := by linarith [hzp,hzm]
  have hcxy : cxy = 0 := by linarith [hxy]
  have hcxz : cxz = 0 := by linarith [hxz]
  have hcyz : cyz = 0 := by linarith [hyz]
  exact ⟨ha,hbx,hby,hbz,hcxx,hcyy,hczz,hcxy,hcxz,hcyz⟩

/-- The three mixed probes are timelike since squared speed=1/8. -/
theorem mixed_probe_is_timelike : (1/4 : ℝ)^2 + (1/4)^2 < 1 := by
  norm_num

/-- The axial probes are timelike since squared speed=1/16. -/
theorem axial_probe_is_timelike : (1/4 : ℝ)^2 < 1 := by
  norm_num

end GppDiamondObserverTomography

#print axioms GppDiamondObserverTomography.ten_timelike_contractions_force_zero
#print axioms GppDiamondObserverTomography.mixed_probe_is_timelike
