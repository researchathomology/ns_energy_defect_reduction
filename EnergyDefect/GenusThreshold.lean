/-
# Analytic continuation of the spectral-topology thread

Three theorems upgrading the correspondence ideas (genus resonances,
N-torus/attractor floors) into machinery consumable by the verified
engine:

* `genus_threshold_ends_epoch` — **the topological threshold theorem**:
  if the reconnection staircase of a genus-`g` structure sustains the
  flux floor for duration `g·τ` (one reconnection step per unit of genus,
  lifetime `τ` each — the Liu–Ricca staircase), and `g` exceeds the
  explicit threshold `g* = ((C/B)^{1/q} − w₀)/τ`, then the epoch of
  regularity ends *before the staircase is exhausted*.  Blowup becomes a
  genus-counting condition.
* `averaged_amplitude_floor` — the time-averaged trilinear step: an
  averaged flux floor pushes through `Π_j ≤ c₀2^j a_j³` and the energy
  bound `a_j ≤ M` to an averaged amplitude floor
  `∫ a_j² ≥ B(w−w₀)/(c₀2^jM)`.
* `averaged_supercritical_exit` — hence every `H^s`, `s ≥ 1/2`,
  square-sum diverges **in time average** (`L²_t H^s` exit).  This is
  R5's "weaker usable variant (b)", previously claimed, now proven — the
  form matched to invariant measures: `∫Π_j dμ > 0` for a measure on a
  compact transient set (cf. `quasiperiodic_floor`,
  `extremal_measure_exists`) gives exactly such averaged floors along
  generic trajectories.  Note the honest exponent: pointwise floors give
  the Onsager exponent 1/3; averaged floors (with the energy crutch
  `a ≤ M`) give 1/2 — the critical space, still a loss-of-regularity
  statement.
-/
import EnergyDefect.HardyRoute
import EnergyDefect.OnsagerRoute

namespace EnergyDefect

open Real Finset MeasureTheory intervalIntegral

/-- **The topological threshold theorem.**  Suppose the flux floor `B` is
sustained while the reconnection staircase lasts — on
`[w₀, min e (w₀ + g·τ))`, `g` = genus, `τ` = per-step lifetime — together
with the polynomial ceiling.  If the genus exceeds the explicit threshold,
`max w₀ ((C/B)^{1/q}) < w₀ + g·τ`, then the epoch of regularity ends
before the staircase is exhausted: `e ≤ max w₀ ((C/B)^{1/q})`. -/
theorem genus_threshold_ends_epoch {nut : ℝ → ℝ} {B C q w₀ τ e : ℝ} {g : ℕ}
    (hB : 0 < B) (hq : 0 < q) (hw₀ : 0 ≤ w₀)
    (hg : max w₀ ((C / B) ^ q⁻¹) < w₀ + g * τ)
    (hfloor : ∀ t ∈ Set.Ico w₀ (min e (w₀ + g * τ)), B ≤ nut t)
    (hceil : ∀ t ∈ Set.Ico w₀ (min e (w₀ + g * τ)), nut t ≤ C * t ^ (-q)) :
    e ≤ max w₀ ((C / B) ^ q⁻¹) := by
  have h1 : min e (w₀ + g * τ) ≤ max w₀ ((C / B) ^ q⁻¹) :=
    epoch_le_of_shifted_floor_polynomial_ceiling hB hq hw₀ hfloor hceil
  rcases min_cases e (w₀ + g * τ) with ⟨hmin, _⟩ | ⟨hmin, hle⟩
  · rwa [hmin] at h1
  · rw [hmin] at h1
    linarith

/-- **Time-averaged trilinear step.**  If the time-integrated flux carries
the floor `B(w−w₀)`, the trilinear band bound `Π ≤ c₀2^j a³` holds, and
the amplitude obeys the energy bound `0 ≤ a ≤ M`, then the integrated
square amplitude is floored:
`∫ a² ≥ B(w−w₀)/(c₀2^jM)`. -/
theorem averaged_amplitude_floor {Pi a : ℝ → ℝ} {B c₀ M w₀ w : ℝ} {j : ℕ}
    (hc₀ : 0 < c₀) (hM : 0 < M) (hI : w₀ ≤ w)
    (haM : ∀ t ∈ Set.Icc w₀ w, 0 ≤ a t ∧ a t ≤ M)
    (htri : ∀ t ∈ Set.Icc w₀ w, Pi t ≤ c₀ * 2 ^ j * a t ^ 3)
    (hint_a2 : IntervalIntegrable (fun t => a t ^ 2) volume w₀ w)
    (hint_Pi : IntervalIntegrable Pi volume w₀ w)
    (hfloor : B * (w - w₀) ≤ ∫ t in w₀..w, Pi t) :
    B * (w - w₀) / (c₀ * 2 ^ j * M) ≤ ∫ t in w₀..w, a t ^ 2 := by
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have hmono : ∀ t ∈ Set.Icc w₀ w, Pi t ≤ (c₀ * 2 ^ j * M) * a t ^ 2 := by
    intro t ht
    obtain ⟨ha0, haMt⟩ := haM t ht
    calc Pi t ≤ c₀ * 2 ^ j * a t ^ 3 := htri t ht
      _ = (c₀ * 2 ^ j) * (a t * a t ^ 2) := by ring
      _ ≤ (c₀ * 2 ^ j) * (M * a t ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right haMt (by positivity)
      _ = (c₀ * 2 ^ j * M) * a t ^ 2 := by ring
  have h1 : (∫ t in w₀..w, Pi t)
      ≤ ∫ t in w₀..w, (c₀ * 2 ^ j * M) * a t ^ 2 := by
    apply integral_mono_on hI hint_Pi (hint_a2.const_mul _) hmono
  rw [intervalIntegral.integral_const_mul] at h1
  rw [div_le_iff₀ (by positivity)]
  calc B * (w - w₀) ≤ (c₀ * 2 ^ j * M) * ∫ t in w₀..w, a t ^ 2 :=
        hfloor.trans h1
    _ = (∫ t in w₀..w, a t ^ 2) * (c₀ * 2 ^ j * M) := by ring

/-- **Time-averaged supercritical exit (R5 variant (b), proven).**  Under
uniform *integrated* flux floors at every band and the energy bound, every
weighted square sum with exponent `s ≥ 1/2` exceeds any threshold in time
average: the solution admits no `L²_t H^s` bound, `s > 1/2`, on the
window.  This is the invariant-measure/ergodic form of the R5 chain
(averaged floors are what `∫Π_j dμ > 0` on a compact transient set
delivers along trajectories). -/
theorem averaged_supercritical_exit {a : ℕ → ℝ → ℝ} {Pi : ℕ → ℝ → ℝ}
    {B c₀ M w₀ w s : ℝ}
    (hc₀ : 0 < c₀) (hM : 0 < M) (hI : w₀ < w) (hB : 0 < B)
    (hs : (1:ℝ)/2 ≤ s)
    (haM : ∀ j, ∀ t ∈ Set.Icc w₀ w, 0 ≤ a j t ∧ a j t ≤ M)
    (htri : ∀ j, ∀ t ∈ Set.Icc w₀ w, Pi j t ≤ c₀ * 2 ^ j * a j t ^ 3)
    (hint_a2 : ∀ j, IntervalIntegrable (fun t => a j t ^ 2) volume w₀ w)
    (hint_Pi : ∀ j, IntervalIntegrable (Pi j) volume w₀ w)
    (hfloor : ∀ j, B * (w - w₀) ≤ ∫ t in w₀..w, Pi j t)
    (M' : ℝ) :
    ∃ J : ℕ, M' ≤ ∑ j ∈ range J,
      ((2:ℝ) ^ j) ^ (2*s) * ∫ t in w₀..w, a j t ^ 2 := by
  set β : ℝ := B * (w - w₀) / (c₀ * M) with hβ
  have hβpos : 0 < β := by
    have : 0 < w - w₀ := by linarith
    positivity
  have hterm : ∀ j, β ≤ ((2:ℝ) ^ j) ^ (2*s) * ∫ t in w₀..w, a j t ^ 2 := by
    intro j
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h2j1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hA := averaged_amplitude_floor hc₀ hM hI.le (haM j) (htri j)
      (hint_a2 j) (hint_Pi j) (hfloor j)
    -- ∫a² ≥ B(w−w₀)/(c₀2^jM) = β/2^j
    have hA' : β / 2 ^ j ≤ ∫ t in w₀..w, a j t ^ 2 := by
      have heq : B * (w - w₀) / (c₀ * 2 ^ j * M) = β / 2 ^ j := by
        rw [hβ]
        field_simp
      linarith [heq ▸ hA]
    -- weight: (2^j)^{2s} ≥ 2^j for s ≥ 1/2
    have hw2 : (2:ℝ) ^ j ≤ ((2:ℝ) ^ j) ^ (2*s) := by
      have h := Real.rpow_le_rpow_of_exponent_le h2j1
        (by linarith : (1:ℝ) ≤ 2*s)
      simpa using h
    have hint_nn : 0 ≤ ∫ t in w₀..w, a j t ^ 2 :=
      le_trans (by positivity : (0:ℝ) ≤ β / 2 ^ j) hA'
    calc β = 2 ^ j * (β / 2 ^ j) := by field_simp
      _ ≤ 2 ^ j * ∫ t in w₀..w, a j t ^ 2 :=
          mul_le_mul_of_nonneg_left hA' h2j.le
      _ ≤ ((2:ℝ) ^ j) ^ (2*s) * ∫ t in w₀..w, a j t ^ 2 :=
          mul_le_mul_of_nonneg_right hw2 hint_nn
  obtain ⟨J, hJ⟩ := exists_nat_ge (M' / β)
  refine ⟨J, ?_⟩
  have h1 : (J : ℝ) * β ≤ ∑ j ∈ range J,
      ((2:ℝ) ^ j) ^ (2*s) * ∫ t in w₀..w, a j t ^ 2 := by
    calc (J : ℝ) * β = ∑ _j ∈ range J, β := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j
  have h2 : M' ≤ (J : ℝ) * β := by
    rw [div_le_iff₀ hβpos] at hJ
    linarith
  linarith

/-- **Sufficient genus always exists (Archimedes).**  For any engine
constants `C, B, q` and any positive per-step lifetime `τ`, there is a
genus `g` exceeding the threshold: `max w₀ ((C/B)^{1/q}) < w₀ + g·τ`.
The abstract example-side of the threshold theorem is thus never the
obstruction — what must be verified for a concrete knotted datum is only
the *hypothesis pair* (floor sustained during the staircase, per-step
lifetime `τ` bounded below).  The experiment `knot_ladder.py` measures
exactly these two quantities. -/
theorem genus_threshold_attainable {C B q w₀ τ : ℝ} (hτ : 0 < τ) :
    ∃ g : ℕ, max w₀ ((C / B) ^ q⁻¹) < w₀ + g * τ := by
  obtain ⟨g, hg⟩ := exists_nat_gt ((max w₀ ((C / B) ^ q⁻¹) - w₀) / τ)
  refine ⟨g, ?_⟩
  have h1 : (max w₀ ((C / B) ^ q⁻¹) - w₀) / τ * τ < g * τ :=
    mul_lt_mul_of_pos_right hg hτ
  have h2 : (max w₀ ((C / B) ^ q⁻¹) - w₀) / τ * τ
      = max w₀ ((C / B) ^ q⁻¹) - w₀ := by field_simp
  linarith [h2 ▸ h1]

end EnergyDefect
