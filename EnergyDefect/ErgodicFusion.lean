/-
# The fused statement: extremal measures, band-flux positivity, and exit

Fusion of the three pieces identified on the spectral-topology thread —
`quasiperiodic_floor` (compact phase space, horizon-free),
`extremal_measure_exists` (well-posed entropy principle), and the
averaged Onsager chain (`averaged_supercritical_exit`) — into a single
statement.  Two theorems:

* `ensemble_supercritical_exit` — **fully proven, no ergodic input**: an
  invariant/extremal measure `μ` whose band fluxes are uniformly positive
  in the mean (`∫Π_j dμ ≥ B > 0` for all `j`), with the trilinear band
  bound and the energy bound `μ`-a.e., charges **no `H^{s}` bound for any
  `s ≥ 1/2`**: the weighted sums `Σ_j 2^{2sj}∫a_j²dμ` exceed every
  threshold.  The ensemble of states seen by such a measure is
  supercritically rough.  Combined with `extremal_measure_exists`
  (existence of extremal `μ` over any closed constraint set on a compact
  state space), the entropy-principle route is now a complete conditional
  chain whose ONLY remaining content is the measure-theoretic positivity
  `∫Π_j dμ ≥ B` uniformly in `j`.
* `birkhoff_transfer` — the trajectory version, with the ergodic input
  isolated as a single `Tendsto` hypothesis (exactly what the pointwise
  ergodic theorem supplies for ergodic `μ` and a.e. data; not yet in
  Mathlib — recorded as the upstream target): if the running time-averages
  of the trajectory flux converge to a limit `≥ B`, then for every
  `ε > 0` the integrated floors `∫₀^T Π_j ≥ (B−ε)T` hold for all large
  `T` — the hypothesis format of `averaged_supercritical_exit`.
-/
import EnergyDefect.GenusThreshold
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace EnergyDefect

open Real Finset MeasureTheory Filter

/-- **Ensemble supercritical exit (proven; the fused statement).**
Let `μ` be a probability measure on a state space `X` (e.g. an invariant
or extremal measure on the compact transient set), `a j : X → ℝ` the band
amplitudes and `Pi j : X → ℝ` the band fluxes.  If `μ`-a.e. the trilinear
bound `Pi j ≤ c₀·2^j·(a j)³` and the energy bound `0 ≤ a j ≤ M` hold, the
relevant functions are integrable, and the fluxes are uniformly positive
in the mean — `B ≤ ∫ Pi j dμ` for all `j` — then for every `s ≥ 1/2` and
every threshold `M'` finitely many bands make the ensemble-weighted sum
exceed `M'`:  the measure charges no `H^{s}`-bounded set. -/
theorem ensemble_supercritical_exit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {a Pi : ℕ → X → ℝ} {B c₀ M s : ℝ}
    (hc₀ : 0 < c₀) (hM : 0 < M) (hB : 0 < B) (hs : (1:ℝ)/2 ≤ s)
    (haM : ∀ j, ∀ᵐ x ∂μ, 0 ≤ a j x ∧ a j x ≤ M)
    (htri : ∀ j, ∀ᵐ x ∂μ, Pi j x ≤ c₀ * 2 ^ j * a j x ^ 3)
    (hint_a2 : ∀ j, Integrable (fun x => a j x ^ 2) μ)
    (hint_Pi : ∀ j, Integrable (Pi j) μ)
    (hfloor : ∀ j, B ≤ ∫ x, Pi j x ∂μ)
    (M' : ℝ) :
    ∃ J : ℕ, M' ≤ ∑ j ∈ range J, ((2:ℝ) ^ j) ^ (2*s) * ∫ x, a j x ^ 2 ∂μ := by
  set β : ℝ := B / (c₀ * M) with hβ
  have hβpos : 0 < β := by positivity
  have hterm : ∀ j, β ≤ ((2:ℝ) ^ j) ^ (2*s) * ∫ x, a j x ^ 2 ∂μ := by
    intro j
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h2j1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    -- a.e. domination Pi ≤ (c₀ 2^j M) a², then integrate
    have hdom : ∀ᵐ x ∂μ, Pi j x ≤ (c₀ * 2 ^ j * M) * a j x ^ 2 := by
      filter_upwards [haM j, htri j] with x hx htx
      obtain ⟨h0, hMx⟩ := hx
      calc Pi j x ≤ c₀ * 2 ^ j * a j x ^ 3 := htx
        _ = (c₀ * 2 ^ j) * (a j x * a j x ^ 2) := by ring
        _ ≤ (c₀ * 2 ^ j) * (M * a j x ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hMx (by positivity)
        _ = (c₀ * 2 ^ j * M) * a j x ^ 2 := by ring
    have h1 : (∫ x, Pi j x ∂μ) ≤ ∫ x, (c₀ * 2 ^ j * M) * a j x ^ 2 ∂μ :=
      integral_mono_ae (hint_Pi j) ((hint_a2 j).const_mul _) hdom
    rw [integral_const_mul] at h1
    have hA : β / 2 ^ j ≤ ∫ x, a j x ^ 2 ∂μ := by
      rw [hβ, div_div]
      rw [div_le_iff₀ (by positivity)]
      calc B ≤ ∫ x, Pi j x ∂μ := hfloor j
        _ ≤ (c₀ * 2 ^ j * M) * ∫ x, a j x ^ 2 ∂μ := h1
        _ = (∫ x, a j x ^ 2 ∂μ) * (c₀ * M * 2 ^ j) := by ring
    have hw2 : (2:ℝ) ^ j ≤ ((2:ℝ) ^ j) ^ (2*s) := by
      have h := Real.rpow_le_rpow_of_exponent_le h2j1
        (by linarith : (1:ℝ) ≤ 2*s)
      simpa using h
    have hint_nn : 0 ≤ ∫ x, a j x ^ 2 ∂μ :=
      le_trans (by positivity : (0:ℝ) ≤ β / 2 ^ j) hA
    calc β = 2 ^ j * (β / 2 ^ j) := by field_simp
      _ ≤ 2 ^ j * ∫ x, a j x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hA h2j.le
      _ ≤ ((2:ℝ) ^ j) ^ (2*s) * ∫ x, a j x ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_right hw2 hint_nn
  obtain ⟨J, hJ⟩ := exists_nat_ge (M' / β)
  refine ⟨J, ?_⟩
  have h1 : (J : ℝ) * β ≤ ∑ j ∈ range J,
      ((2:ℝ) ^ j) ^ (2*s) * ∫ x, a j x ^ 2 ∂μ := by
    calc (J : ℝ) * β = ∑ _j ∈ range J, β := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j
  have h2 : M' ≤ (J : ℝ) * β := by
    rw [div_le_iff₀ hβpos] at hJ
    linarith
  linarith

/-- **Birkhoff transfer (proven conditional on the ergodic limit).**  If
the running time-averages of the trajectory flux converge to a limit
`I ≥ B` (the conclusion the pointwise ergodic theorem supplies, for
ergodic `μ` and a.e. initial state, with `I = ∫ Pi dμ`), then for every
`ε ∈ (0, B)` the integrated floors of the averaged Onsager chain hold for
all sufficiently large horizons: `(B − ε)·T ≤ ∫₀^T Π`. -/
theorem birkhoff_transfer {F : ℝ → ℝ} {B I ε : ℝ}
    (hlim : Tendsto (fun T => (∫ t in (0:ℝ)..T, F t) / T) atTop (nhds I))
    (hIB : B ≤ I) (hε : 0 < ε) :
    ∀ᶠ T in atTop, (B - ε) * T ≤ ∫ t in (0:ℝ)..T, F t := by
  have h1 : ∀ᶠ T in atTop, B - ε < (∫ t in (0:ℝ)..T, F t) / T :=
    hlim.eventually_const_lt (by linarith)
  filter_upwards [h1, eventually_gt_atTop (0:ℝ)] with T hT hT0
  calc (B - ε) * T ≤ (∫ t in (0:ℝ)..T, F t) / T * T :=
        mul_le_mul_of_nonneg_right hT.le hT0.le
    _ = ∫ t in (0:ℝ)..T, F t := by field_simp

end EnergyDefect
