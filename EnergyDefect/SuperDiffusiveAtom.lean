/-
# N4 — energy atoms are super-diffusive (Theorem A skeleton)

Let `u` be a Leray–Hopf solution on `𝕋³` (or `ℝ³`), smooth on `[0, T*)`,
whose endpoint energy measure `μ = lim_{t↑T*} |u(t)|² dx` has an atom of
mass `m₀ > 0` at `x₀`, and let `λ(t)` be its concentration scale
(`λ(t) = inf {r : ∫_{B_r(x₀)} |u(t)|² ≥ m₀/2}`).  Two PDE facts:

* **Poincaré on a ball of radius `∝ λ(t)` about the atom.**  With
  `R = λ (4E₀/m₀)^{1/3}`, Poincaré–Wirtinger on `B_R` and the mean-value
  bound give `‖∇u(t)‖² ≥ c / λ(t)²`, `c = c₀ m₀^{5/3} E₀^{−2/3}`.
* **Leray–Hopf energy inequality.**  `ν ∫_{t₀}^{T*} ‖∇u‖² dt ≤ E₀`; in
  particular the dissipation rate `D(t) = ‖∇u(t)‖²` is integrable up to `T*`.

Consequence: `∫^{T*} dt / λ(t)² ≤ E₀/(ν c) = C E₀^{5/3}/(ν m₀^{5/3})`, so the
concentration scale cannot stay below the diffusive scale
`λ(t)² ≤ K ν (T* − t)` on any terminal interval (the integral of
`1/(T* − t)` diverges).  In power laws `λ ∼ (T* − t)^α` this is `α < 1/2`.

We formalise the real-analytic skeleton with `lam : ℝ → ℝ` for `λ` and
`D : ℝ → ℝ` for `‖∇u(t)‖²`; the two PDE facts enter as explicit hypotheses
`hD` (the Poincaré lower bound) and `hint`/`hE` (finite dissipation and the
energy inequality).  Nothing is assumed globally.

* `integrableOn_inv_sq_of_poincare` — `1/λ²` is integrable up to `T*`
  (`0 ≤ 1/λ² ≤ D/c`).
* `superdiffusive_integral_bound` — `∫_{t₀}^{T*} dt/λ(t)² ≤ E₀/(ν c)`.
* `not_diffusive_on_terminal_interval` — no `K > 0` and `t₁ < T*` with
  `λ(t)² ≤ K ν (T* − t)` on `[t₁, T*)`: the bound would make `1/(T* − t)`
  integrable on `(t₁, T*)`, contradicting `intervalIntegrable_sub_inv_iff`.
  Only finite dissipation (`hint`) is used here, not the value `E₀/ν`.

The theorem is about one Leray–Hopf solution at fixed `ν`: it is not a
computable ceiling, involves no Galerkin uniformity, no forcing and no
family sliding.  Its hypothesis is the atom (via `hD`), not Proposition P.
Register entry N4 (`research/paperA/reports/G2_OBSTRUCTION.md` §2).
-/
import EnergyDefect.EnergyProfile
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace EnergyDefect

open MeasureTheory Set

/-- **Integrability of `1/λ²` up to `T*`.**  From `c/λ² ≤ D` on `[t₀, T*)`,
`c > 0`, and the integrability of the dissipation rate `D` on `(t₀, T*)`,
the function `1/λ²` is integrable on `(t₀, T*)`.  Measurability of `λ` is
needed for the Bochner integrability (it is automatic for the PDE
concentration scale, a lower semicontinuous function of `t`). -/
theorem integrableOn_inv_sq_of_poincare {t₀ Tstar c : ℝ} {lam D : ℝ → ℝ}
    (hc : 0 < c) (hmeas : Measurable lam)
    (hlam : ∀ t ∈ Ico t₀ Tstar, 0 < lam t)
    (hD : ∀ t ∈ Ico t₀ Tstar, c / (lam t) ^ 2 ≤ D t)
    (hint : IntegrableOn D (Ioo t₀ Tstar)) :
    IntegrableOn (fun t => 1 / (lam t) ^ 2) (Ioo t₀ Tstar) := by
  have hDc : IntegrableOn (fun t => D t / c) (Ioo t₀ Tstar) := hint.div_const c
  refine hDc.mono' ?_ ?_
  · exact (measurable_const.div (hmeas.pow_const 2)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Ico t₀ Tstar := Ioo_subset_Ico_self ht
    have hl : 0 < lam t := hlam t ht'
    have hsq : 0 < (lam t) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), le_div_iff₀ hc]
    have h := hD t ht'
    rw [div_eq_mul_one_div] at h
    linarith [mul_comm c (1 / (lam t) ^ 2)]

/-- **N4, integral form: `∫_{t₀}^{T*} dt/λ(t)² ≤ E₀/(ν c)`.**  The Poincaré
lower bound `c/λ² ≤ D` on `[t₀, T*)` and the energy inequality
`∫_{t₀}^{T*} D ≤ E₀/ν` (with `D` integrable) give the super-diffusive
integral bound; with `c = c₀ m₀^{5/3} E₀^{−2/3}` this is
`C E₀^{5/3}/(ν m₀^{5/3})`. -/
theorem superdiffusive_integral_bound {t₀ Tstar ν c E₀ : ℝ} {lam D : ℝ → ℝ}
    (hc : 0 < c) (hmeas : Measurable lam)
    (hlam : ∀ t ∈ Ico t₀ Tstar, 0 < lam t)
    (hD : ∀ t ∈ Ico t₀ Tstar, c / (lam t) ^ 2 ≤ D t)
    (hint : IntegrableOn D (Ioo t₀ Tstar))
    (hE : ∫ t in Ioo t₀ Tstar, D t ≤ E₀ / ν) :
    ∫ t in Ioo t₀ Tstar, 1 / (lam t) ^ 2 ≤ E₀ / (ν * c) := by
  have h1 : IntegrableOn (fun t => 1 / (lam t) ^ 2) (Ioo t₀ Tstar) :=
    integrableOn_inv_sq_of_poincare hc hmeas hlam hD hint
  have h2 : ∫ t in Ioo t₀ Tstar, 1 / (lam t) ^ 2 ≤ ∫ t in Ioo t₀ Tstar, D t / c := by
    apply setIntegral_mono_on h1 (hint.div_const c) measurableSet_Ioo
    intro t ht
    have ht' : t ∈ Ico t₀ Tstar := Ioo_subset_Ico_self ht
    rw [le_div_iff₀ hc]
    have h := hD t ht'
    rw [div_eq_mul_one_div] at h
    linarith [mul_comm c (1 / (lam t) ^ 2)]
  rw [integral_div] at h2
  calc ∫ t in Ioo t₀ Tstar, 1 / (lam t) ^ 2 ≤ (∫ t in Ioo t₀ Tstar, D t) / c := h2
    _ ≤ (E₀ / ν) / c := div_le_div_of_nonneg_right hE hc.le
    _ = E₀ / (ν * c) := div_div _ _ _

/-- **N4, terminal form: the concentration scale is not diffusive.**  Under
the Poincaré lower bound and finite dissipation up to `T*`, there is no
`t₁ ∈ [t₀, T*)` with `λ(t)² ≤ K ν (T* − t)` for all `t ∈ [t₁, T*)`: such a
bound gives `1/(Kν(T* − t)) ≤ 1/λ(t)² ≤ D(t)/c` on `(t₁, T*)`, so
`1/(T* − t)` would be integrable on `(t₁, T*)`, which it is not
(`intervalIntegrable_sub_inv_iff`).  In particular `λ(t)² > K ν (T* − t)`
for `t` arbitrarily close to `T*`, for every `K`; in the modulation ansatz
`b/ε → ∞` (Euler-dominated collapse), and the viscously selected law
`b = cε` carries no energy atom. -/
theorem not_diffusive_on_terminal_interval {t₀ Tstar ν c K : ℝ} {lam D : ℝ → ℝ}
    (hν : 0 < ν) (hc : 0 < c) (hK : 0 < K)
    (hlam : ∀ t ∈ Ico t₀ Tstar, 0 < lam t)
    (hD : ∀ t ∈ Ico t₀ Tstar, c / (lam t) ^ 2 ≤ D t)
    (hint : IntegrableOn D (Ioo t₀ Tstar)) :
    ¬ ∃ t₁ ∈ Ico t₀ Tstar, ∀ t ∈ Ico t₁ Tstar, (lam t) ^ 2 ≤ K * ν * (Tstar - t) := by
  rintro ⟨t₁, ⟨ht₀, ht₁⟩, hdiff⟩
  have hKν : 0 < K * ν := mul_pos hK hν
  have hsub : Ioo t₁ Tstar ⊆ Ioo t₀ Tstar := Ioo_subset_Ioo_left ht₀
  have hDc : IntegrableOn (fun t => D t / c) (Ioo t₁ Tstar) :=
    IntegrableOn.mono_set (hint.div_const c) hsub
  -- the diffusive bound makes `(Kν)⁻¹ (T* − t)⁻¹` integrable on `(t₁, T*)`
  have hg : IntegrableOn (fun t => (K * ν)⁻¹ * (Tstar - t)⁻¹) (Ioo t₁ Tstar) := by
    refine hDc.mono' ?_ ?_
    · exact (measurable_const.mul (measurable_const.sub measurable_id).inv).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Ico t₀ Tstar := ⟨ht₀.trans ht.1.le, ht.2⟩
      have hl : 0 < lam t := hlam t ht'
      have hsq : 0 < (lam t) ^ 2 := by positivity
      have hTt : 0 < Tstar - t := sub_pos.mpr ht.2
      have hb : (lam t) ^ 2 ≤ K * ν * (Tstar - t) := hdiff t ⟨ht.1.le, ht.2⟩
      have hpos : 0 < (K * ν)⁻¹ * (Tstar - t)⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hpos.le, ← mul_inv]
      -- `1/(Kν(T* − t)) ≤ 1/λ² ≤ D/c`
      have h1 : (K * ν * (Tstar - t))⁻¹ ≤ ((lam t) ^ 2)⁻¹ := inv_anti₀ hsq hb
      have h2 : ((lam t) ^ 2)⁻¹ ≤ D t / c := by
        rw [le_div_iff₀ hc]
        have h := hD t ht'
        rw [div_eq_mul_inv] at h
        linarith [mul_comm c ((lam t) ^ 2)⁻¹]
      exact h1.trans h2
  -- hence `(t − T*)⁻¹` is integrable on `(t₁, T*)`
  have hg' : IntegrableOn (fun t => (t - Tstar)⁻¹) (Ioo t₁ Tstar) := by
    refine IntegrableOn.congr_fun (hg.const_mul (-(K * ν))) ?_ measurableSet_Ioo
    intro t _
    have hKν' : K * ν ≠ 0 := hKν.ne'
    simp only
    rw [← mul_assoc, neg_mul, mul_inv_cancel₀ hKν', ← neg_sub Tstar t, inv_neg]
    ring
  have hii : IntervalIntegrable (fun x => (x - Tstar)⁻¹) volume t₁ Tstar := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht₁.le]
    exact hg'
  rw [intervalIntegrable_sub_inv_iff] at hii
  rcases hii with h | h
  · exact ht₁.ne h
  · exact h right_mem_uIcc

end EnergyDefect
