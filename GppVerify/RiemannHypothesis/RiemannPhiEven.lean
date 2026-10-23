import GppVerify.RiemannHypothesis.RiemannPhi

/-!
# Riemann's Φ is even: `Φ = (f″ − f)/16` with `f` even by theta inversion

Source: Claude Code, `work/claude-code/2026-10-23_holographic_dictionary.md` §1, and the factor
convention in Astra, `work/2026-10-23_astra_phi_two_wave_interference.md` (GPP-bridge). Daniel
Toupin / Golden Physics Project, with AI assistance from Claude Code (and Astra for the
convention check).

Put `θ(x) = 1 + 2ψ(x)` and `f(u) = e^u θ(e^{4u})`.

* `f_even`: `f(−u) = f(u)`. This is the theta inversion `θ(x) = x^{−1/2}θ(1/x)` of
  `GppRiemannPhi.psi_functional_equation`.
* `hasDerivAt_f`, `hasDerivAt_f₁`: `f′ = f₁` and `f₁′ = f₂` with
  `f₁ = e^u(θ + 8xψ′)` and `f₂ = e^u(θ + 48xψ′ + 32x²ψ″)`, where `x = e^{4u}`.
* `phi_eq_f`: `Φ(u) = (f″(u) − f(u))/16`.
* `phi_even`: `Φ(−u) = Φ(u)`, because differentiation turns even into odd into even.

**Scope.** Positivity of `Φ`, its decay, and the cosine representation `Ξ(t) = 2∫Φ(u)cos(ut)du`
are not formalized. No claim about RH.
-/

open Real

namespace GppRiemannPhi

/-- `f(u) = e^u θ(e^{4u})` with `θ = 1 + 2ψ`. -/
noncomputable def f (u : ℝ) : ℝ := rexp u * (1 + 2 * psi (rexp (4 * u)))

/-- `f′`. -/
noncomputable def f₁ (u : ℝ) : ℝ :=
  rexp u * (1 + 2 * psi (rexp (4 * u)) + 8 * rexp (4 * u) * psi₁ (rexp (4 * u)))

/-- `f″`. -/
noncomputable def f₂ (u : ℝ) : ℝ :=
  rexp u * (1 + 2 * psi (rexp (4 * u)) + 48 * rexp (4 * u) * psi₁ (rexp (4 * u))
    + 32 * rexp (4 * u) ^ 2 * psi₂ (rexp (4 * u)))

/-- **`f` is even**, by theta inversion. -/
theorem f_even (u : ℝ) : f (-u) = f u := by
  have hx : 0 < rexp (4 * u) := Real.exp_pos _
  have hfe := psi_functional_equation hx
  have hinv : 1 / rexp (4 * u) = rexp (4 * -u) := by
    rw [one_div, ← Real.exp_neg]; ring_nf
  have hsq : rexp (4 * u) ^ (1 / 2 : ℝ) = rexp (2 * u) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hinv, hsq] at hfe
  have h2 : 1 + 2 * psi (rexp (4 * -u)) = rexp (2 * u) * (1 + 2 * psi (rexp (4 * u))) := by
    have hpos : 0 < rexp (2 * u) := Real.exp_pos _
    rw [hfe]; field_simp
  unfold f
  rw [h2, ← mul_assoc, ← Real.exp_add]
  ring_nf

lemma hasDerivAt_exp4 (u : ℝ) : HasDerivAt (fun u => rexp (4 * u)) (rexp (4 * u) * 4) u := by
  have := ((hasDerivAt_id u).const_mul 4).exp
  simpa using this

lemma hasDerivAt_comp {g g' : ℝ → ℝ} (hg : ∀ x, 0 < x → HasDerivAt g (g' x) x) (u : ℝ) :
    HasDerivAt (fun u => g (rexp (4 * u))) (g' (rexp (4 * u)) * (rexp (4 * u) * 4)) u :=
  (hg (rexp (4 * u)) (Real.exp_pos _)).comp (h := fun u => rexp (4 * u)) u (hasDerivAt_exp4 u)

theorem hasDerivAt_f (u : ℝ) : HasDerivAt f (f₁ u) u := by
  have hp := hasDerivAt_comp (fun x hx => hasDerivAt_psi hx) u
  have := (Real.hasDerivAt_exp u).mul ((hp.const_mul 2).const_add 1)
  refine this.congr_deriv ?_
  simp only [f₁]
  ring

theorem hasDerivAt_f₁ (u : ℝ) : HasDerivAt f₁ (f₂ u) u := by
  have hp := hasDerivAt_comp (fun x hx => hasDerivAt_psi hx) u
  have hp1 := hasDerivAt_comp (fun x hx => hasDerivAt_psi₁ hx) u
  have hx := hasDerivAt_exp4 u
  have inner := ((hp.const_mul 2).const_add 1).add ((hx.const_mul 8).mul hp1)
  have := (Real.hasDerivAt_exp u).mul inner
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  · simp only [f₂, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [f₁, Pi.add_apply, Pi.mul_apply]

/-- **`Φ = (f″ − f)/16`.** -/
theorem phi_eq_f (u : ℝ) : phi u = (f₂ u - f u) / 16 := by
  rw [phi_eq]
  unfold f₂ f
  ring

/-- The derivative of an even function is odd, and of an odd function is even. -/
lemma deriv_neg_of_comp {g g' : ℝ → ℝ} {s : ℝ} (hg : ∀ u, HasDerivAt g (g' u) u)
    (hsym : ∀ u, g (-u) = s * g u) (u : ℝ) : g' (-u) = -(s * g' u) := by
  have h1 : HasDerivAt (fun v => g (-v)) (g' (-u) * (-1)) u :=
    (hg (-u)).comp u (hasDerivAt_neg u)
  have h2 : HasDerivAt (fun v => g (-v)) (s * g' u) u := by
    have : (fun v => g (-v)) = fun v => s * g v := funext hsym
    rw [this]; exact (hg u).const_mul s
  have := h1.unique h2
  linarith

/-- **Riemann's Φ is even.** -/
theorem phi_even (u : ℝ) : phi (-u) = phi u := by
  have h1 : ∀ v, f₁ (-v) = -1 * f₁ v := fun v => by
    rw [deriv_neg_of_comp hasDerivAt_f (s := 1) (fun w => by rw [f_even, one_mul]) v]; ring
  have h2 : f₂ (-u) = f₂ u := by
    rw [deriv_neg_of_comp hasDerivAt_f₁ h1 u]; ring
  rw [phi_eq_f, phi_eq_f, h2, f_even]

end GppRiemannPhi
