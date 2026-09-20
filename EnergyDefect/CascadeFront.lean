/-
# The cascade-front lemma (route R5: existence of a common window)

A structural gap in the R5 statement, closed here: for C^∞ data the band
fluxes vanish rapidly in `j` at `t = 0`, so uniform floors `B ≤ Π_j`
*cannot hold at time zero* — they must develop dynamically, band `j`
acquiring its floor only after the cascade front arrives at scale `j`, at
some time `t_j`.  A common window for **all** bands then exists iff the
arrival times are uniformly bounded.

The classical accelerating-cascade mechanism supplies exactly this: in
Kolmogorov scaling the eddy-turnover time at band `j` scales like
`2^{-2j/3}`, so the arrival delays are geometrically summable and the
front reaches all scales by a finite time `t∞ ≤ t₀ + D/(1-r)`.

Proven here:

* `front_arrival_bounded` — geometrically summable delays give uniformly
  bounded arrival times: `t_j ≤ t₀ + D/(1-r)`.
* `common_window_of_front` — consequently, if band `j` carries its floor
  from `t_j` onward (up to the window end `w`), then **all** bands carry
  the floor on the common window `[t₀ + D/(1-r), w]` — the hypothesis
  format of `uniform_band_floor_defeats_bound` and the Onsager chain.

Empirical counterpart: `research/experiments/dyadic/front_times.py`
measures the arrival times and their geometric-delay structure.
-/
import EnergyDefect.Interface

namespace EnergyDefect

open Finset

/-- **Front-arrival bound (proven).**  If the band arrival times satisfy
geometrically summable delays `t (j+1) − t j ≤ D·r^j` with `0 ≤ r < 1`,
then all arrival times are uniformly bounded:
`t j ≤ t 0 + D/(1-r)`. -/
theorem front_arrival_bounded {t : ℕ → ℝ} {D r : ℝ}
    (hD : 0 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdelay : ∀ j, t (j+1) - t j ≤ D * r ^ j) (j : ℕ) :
    t j ≤ t 0 + D / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  induction j with
  | zero => simp; positivity
  | succ n ih =>
    -- telescope: t (n+1) ≤ t 0 + D * Σ_{i<n+1} r^i ≤ t 0 + D/(1-r)
    have htel : ∀ m : ℕ, t m ≤ t 0 + D * ∑ i ∈ range m, r ^ i := by
      intro m
      induction m with
      | zero => simp
      | succ k ihk =>
        have := hdelay k
        have hsum : ∑ i ∈ range (k+1), r ^ i
            = (∑ i ∈ range k, r ^ i) + r ^ k := Finset.sum_range_succ _ _
        rw [hsum]
        linarith
    have hgeo : ∑ i ∈ range (n+1), r ^ i ≤ 1 / (1 - r) := by
      rw [geom_sum_eq (by linarith : r ≠ 1) (n+1)]
      have hpow : 0 ≤ r ^ (n+1) := pow_nonneg hr0 _
      have heq : (r ^ (n+1) - 1) / (r - 1) = (1 - r ^ (n+1)) / (1 - r) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [heq, div_le_div_iff_of_pos_right h1r]
      linarith
    calc t (n+1) ≤ t 0 + D * ∑ i ∈ range (n+1), r ^ i := htel (n+1)
      _ ≤ t 0 + D * (1 / (1 - r)) := by
          have := mul_le_mul_of_nonneg_left hgeo hD
          linarith
      _ = t 0 + D / (1 - r) := by ring

/-- **Common window from the accelerating cascade (proven).**  If band `j`
carries the floor `B ≤ Π_j(s)` for all `s ∈ [t_j, w]`, and the arrival
delays are geometrically summable, then *all* bands carry the floor on the
common window `[t₀ + D/(1-r), w]` — exactly the uniform-floor hypothesis
of the machine-checked Onsager chain (`uniform_band_floor_defeats_bound`,
`onsager_amplitude_floor`, …). -/
theorem common_window_of_front {t : ℕ → ℝ} {Pi : ℕ → ℝ → ℝ} {B D r w : ℝ}
    (hD : 0 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdelay : ∀ j, t (j+1) - t j ≤ D * r ^ j)
    (hfloor : ∀ j, ∀ s, t j ≤ s → s ≤ w → B ≤ Pi j s) :
    ∀ j, ∀ s, t 0 + D / (1 - r) ≤ s → s ≤ w → B ≤ Pi j s := by
  intro j s hs hw
  exact hfloor j s ((front_arrival_bounded hD hr0 hr1 hdelay j).trans hs) hw

end EnergyDefect
