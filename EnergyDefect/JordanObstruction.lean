/-
# N5 — the fixed-profile Jordan chain is obstructed (Theorem B skeleton)

In the Euler-dominated regime of an adiabatic collapse onto a steady Euler
profile `U₀`, the first-order corrector must solve `L₀ T₁ = −Λ U₀` with
`L₀ v = P[(U₀·∇)v + (v·∇)U₀]`.  Solvability forces the right-hand side to
pair to zero with every compactly supported element of the cokernel
`ker L₀*`.  Two independent real-analytic skeletons:

**(i) Range/cokernel obstruction.**  If `⟪L x, w⟫ = ⟪x, L† w⟫` for all `x`
(the weak formulation: `T₁ ∈ L²_loc`, `w ∈ C_c^∞` divergence-free), then
`L† w = 0` and `⟪y, w⟫ ≠ 0` imply `y ∉ range L`.  Stated first for an
arbitrary adjoint pair `(L, Ladj)` on a real inner product space (no
boundedness, no completeness — this is the form used for the unbounded
operator `L₀`), then for `ContinuousLinearMap.adjoint` on a Hilbert space.
No closed-range property of `L` is used, exactly as in the paper argument.

**(ii) The (C3) ODE consequence.**  For an axisymmetric profile in
Grad–Shafranov form `u = ∇ψ×∇φ + (F(ψ)/R) e_φ`, the third cokernel family
is `w = h(ψ) R e_φ` (kinematic: no steadiness used), and by coarea the
pairing `⟪Λ U₀, h(ψ) R e_φ⟫ = ∫ h(c) [½ F̃(c) T(c) + 3 F̃′(c) V(c)] dc`, with
`V(c)` the volume enclosed by the level torus `{ψ = c}`, `T(c) = V′(c)`,
and `F̃` the effective swirl (`research/paperA/checks/c3_pairing_check.py`,
coarea vs direct quadrature agree to `1.4·10⁻⁶`).  Vanishing for all `h`
gives the ODE `½ F̃ V′ + 3 F̃′ V = 0` on the level range, i.e.
`F̃ V^{1/6} = const`.  If `F̃ = 0` at the outer edge of the support (where
`V > 0`), then `F̃ ≡ 0`: **no swirling compactly supported axisymmetric
profile admits a first-order Jordan corrector.**  (With Jiu–Xin's vanishing
of swirl-free compactly supported axisymmetric steady Euler flows — a
literature input, not formalised — this is Theorem B.3.)

We formalise (ii) with `F V : ℝ → ℝ` differentiable at every point of
`[a, b]` (two-sided derivatives `F' V'` given as data), `V > 0` on `[a, b]`,
and the ODE as a hypothesis on `[a, b]`.

* `not_mem_range_of_adjoint_kernel_pairing` — abstract adjoint pair.
* `inner_eq_zero_of_mem_range_of_adjoint_kernel` — level-set corollary:
  `y = L x` forces `⟪y, w⟫ = 0` for every `w ∈ ker L†`.
* `ContinuousLinearMap.not_mem_range_of_adjoint_kernel_pairing` — Hilbert
  space version with `ContinuousLinearMap.adjoint`.
* `hasDerivAt_swirl_mul_rpow` — the derivative of `F · V^{1/6}` is
  `V^{−5/6} (F V′/6 + F′ V) = (V^{−5/6}/3)(½ F V′ + 3 F′ V)`.
* `swirl_const_of_C3` — `F · V^{1/6}` is constant on `[a, b]` under (C3).
* `swirl_zero_of_C3_boundary` — if moreover `F b = 0` then `F ≡ 0` on `[a, b]`.

Register entry N5 (`research/paperA/reports/G2_OBSTRUCTION.md` §3).
Route-specific: it removes a candidate that would have bypassed the wall
and produces no lower bound on transfer.
-/
import EnergyDefect.SuperDiffusiveAtom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

namespace EnergyDefect

open Set

section Cokernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cokernel obstruction, abstract adjoint pair.**  If `⟪L x, w⟫ = ⟪x, Ladj w⟫`
for all `x` (the weak formulation), `Ladj w = 0`, and `⟪y, w⟫ ≠ 0`, then `y`
is not of the form `L x`.  No boundedness or completeness is assumed. -/
theorem not_mem_range_of_adjoint_kernel_pairing {L Ladj : E → E} {w y : E}
    (hadj : ∀ x, inner ℝ (L x) w = inner ℝ x (Ladj w))
    (hw : Ladj w = 0) (hy : inner ℝ y w ≠ 0) :
    ¬ ∃ x, L x = y := by
  rintro ⟨x, rfl⟩
  apply hy
  rw [hadj x, hw, inner_zero_right]

/-- **Level-set corollary.**  If `y = L x` then `⟪y, w⟫ = 0` for every `w` in
the kernel of the adjoint: the right-hand side of a solvable corrector
equation is orthogonal to the whole cokernel.  Each compactly supported
`w ∈ ker L₀*` (families F1–F3 of the paper) yields one level-set condition
(C1)–(C3). -/
theorem inner_eq_zero_of_mem_range_of_adjoint_kernel {L Ladj : E → E} {w x : E}
    (hadj : ∀ x, inner ℝ (L x) w = inner ℝ x (Ladj w))
    (hw : Ladj w = 0) :
    inner ℝ (L x) w = 0 := by
  rw [hadj x, hw, inner_zero_right]

/-- **Cokernel obstruction, Hilbert space version.**  For a bounded operator
`L` on a real Hilbert space with `L† w = 0` and `⟪y, w⟫ ≠ 0`, `y ∉ range L`. -/
theorem ContinuousLinearMap.not_mem_range_of_adjoint_kernel_pairing [CompleteSpace E]
    (L : E →L[ℝ] E) {w y : E}
    (hw : ContinuousLinearMap.adjoint L w = 0) (hy : inner ℝ y w ≠ 0) :
    y ∉ LinearMap.range (L : E →ₗ[ℝ] E) := by
  intro hmem
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hmem
  exact EnergyDefect.not_mem_range_of_adjoint_kernel_pairing
    (L := L) (Ladj := ContinuousLinearMap.adjoint L)
    (fun x => (ContinuousLinearMap.adjoint_inner_right L x w).symm) hw hy ⟨x, rfl⟩

end Cokernel

section C3

/-- **Derivative of `F · V^{1/6}`.**  At a point where `V c > 0`,
`d/dc [F V^{1/6}] = V^{1/6 − 1} · (F′ V + F V′/6)`. -/
theorem hasDerivAt_swirl_mul_rpow {F V F' V' : ℝ → ℝ} {c : ℝ}
    (hF : HasDerivAt F (F' c) c) (hV : HasDerivAt V (V' c) c) (hVpos : 0 < V c) :
    HasDerivAt (fun c => F c * V c ^ (1 / 6 : ℝ))
      (V c ^ ((1 / 6 : ℝ) - 1) * (F' c * V c + F c * V' c / 6)) c := by
  have hpow : HasDerivAt (fun c => V c ^ (1 / 6 : ℝ))
      (V' c * (1 / 6 : ℝ) * V c ^ ((1 / 6 : ℝ) - 1)) c :=
    hV.rpow_const (Or.inl hVpos.ne')
  have h : HasDerivAt (fun c => F c * V c ^ (1 / 6 : ℝ))
      (F' c * V c ^ (1 / 6 : ℝ) + F c * (V' c * (1 / 6 : ℝ) * V c ^ ((1 / 6 : ℝ) - 1))) c :=
    hF.mul hpow
  have hVsub : V c ^ (1 / 6 : ℝ) = V c ^ ((1 / 6 : ℝ) - 1) * V c := by
    rw [Real.rpow_sub_one hVpos.ne', div_mul_cancel₀ _ hVpos.ne']
  convert h using 1
  rw [hVsub]; ring

/-- **(C3) forces `F · V^{1/6}` constant.**  If `F, V` are differentiable at
every point of `[a, b]`, `V > 0` there, and `½ F V′ + 3 F′ V = 0` on `[a, b]`,
then `F c · V c^{1/6} = F a · V a^{1/6}` for all `c ∈ [a, b]`. -/
theorem swirl_const_of_C3 {F V F' V' : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ c ∈ Icc a b, HasDerivAt F (F' c) c)
    (hV : ∀ c ∈ Icc a b, HasDerivAt V (V' c) c)
    (hVpos : ∀ c ∈ Icc a b, 0 < V c)
    (hODE : ∀ c ∈ Icc a b, (1 / 2) * F c * V' c + 3 * F' c * V c = 0) :
    ∀ c ∈ Icc a b, F c * V c ^ (1 / 6 : ℝ) = F a * V a ^ (1 / 6 : ℝ) := by
  have hderiv : ∀ c ∈ Icc a b, HasDerivAt (fun c => F c * V c ^ (1 / 6 : ℝ)) 0 c := by
    intro c hc
    have h := hasDerivAt_swirl_mul_rpow (hF c hc) (hV c hc) (hVpos c hc)
    have hz : V c ^ ((1 / 6 : ℝ) - 1) * (F' c * V c + F c * V' c / 6) = 0 := by
      have := hODE c hc
      have : F' c * V c + F c * V' c / 6 = 0 := by linarith
      rw [this, mul_zero]
    rwa [hz] at h
  apply constant_of_has_deriv_right_zero
  · intro c hc
    exact (hderiv c hc).continuousAt.continuousWithinAt
  · intro c hc
    exact (hderiv c (Ico_subset_Icc_self hc)).hasDerivWithinAt

/-- **(C3) with vanishing swirl at the support boundary forces `F ≡ 0`.**  If
in addition `F b = 0` (the effective swirl vanishes at the outer edge of a
compactly supported profile, where `V b > 0`), then `F c = 0` for every
`c ∈ [a, b]`: no swirling compactly supported axisymmetric profile admits a
first-order Jordan corrector. -/
theorem swirl_zero_of_C3_boundary {F V F' V' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ c ∈ Icc a b, HasDerivAt F (F' c) c)
    (hV : ∀ c ∈ Icc a b, HasDerivAt V (V' c) c)
    (hVpos : ∀ c ∈ Icc a b, 0 < V c)
    (hODE : ∀ c ∈ Icc a b, (1 / 2) * F c * V' c + 3 * F' c * V c = 0)
    (hFb : F b = 0) :
    ∀ c ∈ Icc a b, F c = 0 := by
  intro c hc
  have hconst := swirl_const_of_C3 hF hV hVpos hODE
  have hb : F b * V b ^ (1 / 6 : ℝ) = F a * V a ^ (1 / 6 : ℝ) :=
    hconst b ⟨hab, le_rfl⟩
  rw [hFb, zero_mul] at hb
  have hc' : F c * V c ^ (1 / 6 : ℝ) = 0 := by rw [hconst c hc, ← hb]
  have hVc : 0 < V c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (hVpos c hc) _
  rcases mul_eq_zero.mp hc' with h | h
  · exact h
  · exact absurd h hVc.ne'

end C3

end EnergyDefect
