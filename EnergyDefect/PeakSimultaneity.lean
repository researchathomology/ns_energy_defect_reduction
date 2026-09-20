/-
# Peak simultaneity: what the certified margin measures, and the tail tower

The 2026-09 campaign's certified margin uses the theorem-capped per-shell
ceiling `C_j = sup_t Π_j(t) t^q`.  Write `p_j(t) := Π_j(t) t^q / C_j ∈ [0,1]`
for the *normalized weighted profile*.  On a point window `w` the joint
margin is `min_j p_j(w)`; every optimum in the campaign record is a point
window, so `m*_sup = max_t min_j p_j(t)` — the margin measures whether the
weighted fluxes of all shells attain their suprema **at the same time**.
Mined from the archived runs (`campaign/peak_structure.py`,
`campaign/logs/peak_structure.txt`): the deep shells peak within 0.1–0.8
time units of each other, the shallow shells `K = 2, 4` peak 1–2.5 units
earlier; the "uniform 0.06 per octave" cost that produced the
never-crosses verdict was entirely the early peaks of `K = 2, 4`.

This file records the elementary theorems behind the corrected reading:

* `tail_band_count`, `tail_supercritical_sums_unbounded` — **the Onsager
  chain never needed the low shells**: floors on `j ≥ J₀` alone force the
  `H^s` sums (`s ≥ 1/3`) over `[J₀, J)` above any bound, with `J − J₀`
  explicit.  Gap 2's quantifier may be read "for all `j ≥ j₀`", and the
  certified tower may be anchored at any shell.
* `certified_profile_le_one` — the normalized profile is `≤ 1`: the
  certified margin is a *necessary-condition* diagnostic (saturation, not
  violation, is its ceiling).
* `lag_model_margin_bound`, `lag_model_cost_bound` — the pure-lag model
  (`p_j(t) = p(t − τ_j)`, common `L`-Lipschitz shape peaking at `0`): at the
  midpoint of the peak times every shell is within `L·spread/2` of its
  peak, so the joint margin is `≥ 1 − L·spread/2` and the tower cost is
  `≤ L·spread/2` — the cost is the *spread of peak times*, not the number
  of shells.
* `lag_model_crossing_iff_simultaneous` — under a strictly peaked shape
  the certified margin reaches `1` iff all peak times coincide: the
  certified crossing is exactly peak simultaneity.
* `tail_spread_of_geometric_lags`, `tail_margin_of_geometric_lags` —
  geometrically summable peak lags (the accelerating cascade,
  `front_arrival_bounded`) give tail spread `≤ D r^{J₀}/(1−r)`, hence a
  tail-anchored margin `≥ 1 − L D r^{J₀}/(2(1−r)) → 1` as `J₀ → ∞`: in the
  lag model, the cost-decay branch of Gap 2′ is the front-acceleration
  hypothesis for *peak* times.

Epistemic status: every theorem here is elementary real arithmetic about
the diagnostic; none is a statement about Navier–Stokes.  The model
hypotheses (common shape, Lipschitz constant, geometric lags) are
measured, not proven — see the session log.
-/
import EnergyDefect.ValidatedProof
import EnergyDefect.CascadeFront

namespace EnergyDefect

open Real Finset

/-- **Tail band count.**  Floors on the shells `J₀ ≤ j < J` alone, with the
trilinear bound, push the weighted square sum over those shells above `M`
as soon as `J − J₀ ≥ M/b₀`, `b₀ = ((B/c)^{1/3})²`.  The low shells
`j < J₀` are not used. -/
theorem tail_band_count {a Pi : ℕ → ℝ} {B c s M : ℝ} {J₀ J : ℕ}
    (hB : 0 < B) (hc : 0 < c) (hs : (1:ℝ)/3 ≤ s) (hJ₀ : J₀ ≤ J)
    (ha : ∀ j, J₀ ≤ j → j < J → 0 ≤ a j)
    (hfloor : ∀ j, J₀ ≤ j → j < J → B ≤ Pi j)
    (htri : ∀ j, J₀ ≤ j → j < J → Pi j ≤ c * 2 ^ j * a j ^ 3)
    (hJ : M / ((B / c) ^ ((1:ℝ)/3)) ^ 2 ≤ (J : ℝ) - J₀) :
    M ≤ ∑ j ∈ Ico J₀ J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
  set b₀ : ℝ := ((B / c) ^ ((1:ℝ)/3)) ^ 2 with hb₀
  have hb₀pos : 0 < b₀ := by positivity
  have hterm : ∀ j, J₀ ≤ j → j < J → b₀ ≤ ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    intro j hj₀ hj
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h2j1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hA := amplitude_floor_single j hB hc (ha j hj₀ hj) (hfloor j hj₀ hj)
      (htri j hj₀ hj)
    have hA0 : (0:ℝ) ≤ (B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3) := by
      positivity
    have hsq : ((B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3)) ^ 2 ≤ a j ^ 2 :=
      pow_le_pow_left₀ hA0 hA 2
    have hexp : ((2:ℝ) ^ j) ^ (2*s) * (((2:ℝ) ^ j) ^ (-(1:ℝ)/3)) ^ 2
        = ((2:ℝ) ^ j) ^ (2*s - 2/3) := by
      rw [← Real.rpow_natCast (((2:ℝ) ^ j) ^ (-(1:ℝ)/3)) 2,
        ← Real.rpow_mul h2j.le, ← Real.rpow_add h2j]
      congr 1
      push_cast
      ring
    have hone : (1:ℝ) ≤ ((2:ℝ) ^ j) ^ (2*s - 2/3) := by
      have h := Real.rpow_le_rpow_of_exponent_le h2j1
        (by linarith : (0:ℝ) ≤ 2*s - 2/3)
      simpa using h
    calc b₀ = 1 * b₀ := (one_mul _).symm
      _ ≤ ((2:ℝ) ^ j) ^ (2*s - 2/3) * b₀ :=
          mul_le_mul_of_nonneg_right hone hb₀pos.le
      _ = ((2:ℝ) ^ j) ^ (2*s) *
          (((B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3)) ^ 2) := by
          rw [mul_pow, ← hexp, hb₀]; ring
      _ ≤ ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  have hcard : ((Ico J₀ J).card : ℝ) = (J : ℝ) - J₀ := by
    rw [Nat.card_Ico, Nat.cast_sub hJ₀]
  have h1 : ((J : ℝ) - J₀) * b₀ ≤ ∑ j ∈ Ico J₀ J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    calc ((J : ℝ) - J₀) * b₀ = ∑ _j ∈ Ico J₀ J, b₀ := by
          rw [sum_const, nsmul_eq_mul, hcard]
      _ ≤ _ := Finset.sum_le_sum fun j hj => by
          obtain ⟨hj₀, hjJ⟩ := Finset.mem_Ico.mp hj
          exact hterm j hj₀ hjJ
  have h2 : M ≤ ((J : ℝ) - J₀) * b₀ := by
    rw [div_le_iff₀ hb₀pos] at hJ
    linarith
  linarith

/-- **Tail floors suffice (the Onsager chain from any shell on).**  Uniform
flux floors on all shells `j ≥ J₀` — no hypothesis on `j < J₀` — force
every `H^s` weighted sum (`s ≥ 1/3`) over `[J₀, J)` above any threshold
for some finite `J`.  Gap 2's "for all `j`" may be read "for all
`j ≥ j₀`", and a certified tower may be anchored at any shell. -/
theorem tail_supercritical_sums_unbounded {a Pi : ℕ → ℝ} {B c s : ℝ}
    {J₀ : ℕ} (hB : 0 < B) (hc : 0 < c) (hs : (1:ℝ)/3 ≤ s)
    (ha : ∀ j, J₀ ≤ j → 0 ≤ a j) (hfloor : ∀ j, J₀ ≤ j → B ≤ Pi j)
    (htri : ∀ j, J₀ ≤ j → Pi j ≤ c * 2 ^ j * a j ^ 3) (M : ℝ) :
    ∃ J : ℕ, M ≤ ∑ j ∈ Ico J₀ J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (M / ((B / c) ^ ((1:ℝ)/3)) ^ 2)
  refine ⟨J₀ + n, tail_band_count hB hc hs (Nat.le_add_right _ _)
    (fun j hj _ => ha j hj) (fun j hj _ => hfloor j hj)
    (fun j hj _ => htri j hj) ?_⟩
  push_cast
  linarith

/-- **The certified profile never exceeds one.**  With the theorem-capped
ceiling `C ≥ sup_t Π(t) t^q`, the normalized weighted profile is `≤ 1`:
the certified margin can saturate, never violate.  It is a
necessary-condition diagnostic for the R5 configuration. -/
theorem certified_profile_le_one {Pi C : ℝ} (hC : 0 < C) (hsup : Pi ≤ C) :
    Pi / C ≤ 1 := by
  rw [div_le_one hC]
  exact hsup

/-- **Lag model, margin bound.**  If every shell's normalized profile is a
time shift `p(t − τ_i)` of a common shape `p` with `p 0 = 1` and Lipschitz
constant `L`, and all peak times lie in `[lo, hi]`, then at the midpoint
`(lo + hi)/2` every shell is within `L·(hi − lo)/2` of its peak.  The
joint margin is thus at least `1 − L·spread/2`: it depends on the spread
of the peak times, not on the number of shells. -/
theorem lag_model_margin_bound {ι : Type*} {p : ℝ → ℝ} {L : ℝ}
    (hpeak : p 0 = 1) (hlip : ∀ x y, |p x - p y| ≤ L * |x - y|)
    {τ : ι → ℝ} {lo hi : ℝ} (hτ : ∀ i, lo ≤ τ i ∧ τ i ≤ hi) (i : ι) :
    1 - L * ((hi - lo) / 2) ≤ p ((lo + hi) / 2 - τ i) := by
  obtain ⟨h1, h2⟩ := hτ i
  have hd : |(lo + hi) / 2 - τ i - 0| ≤ (hi - lo) / 2 := by
    rw [sub_zero, abs_le]
    constructor <;> linarith
  have hL : 0 ≤ L := by
    have := hlip 1 0
    have h01 : (0:ℝ) ≤ |p 1 - p 0| := abs_nonneg _
    simp at this
    linarith
  have := hlip ((lo + hi) / 2 - τ i) 0
  rw [hpeak] at this
  have hbound : |p ((lo + hi) / 2 - τ i) - 1| ≤ L * ((hi - lo) / 2) :=
    this.trans (mul_le_mul_of_nonneg_left hd hL)
  have := (abs_le.mp hbound).1
  linarith

/-- **Lag model, cost bound.**  Any certified subset margin is `≤ 1`
(`certified_profile_le_one`); with the tower margin `≥ 1 − L·spread/2`
the tower cost `S − M` is at most `L·spread/2`.  Feeds
`bounded_cost_crossing` with `C = L·spread/2`. -/
theorem lag_model_cost_bound {S M L spread : ℝ} (hS : S ≤ 1)
    (hM : 1 - L * (spread / 2) ≤ M) :
    S - M ≤ L * (spread / 2) := by linarith

/-- **Certified crossing ⟺ simultaneous peaks.**  If the common shape is
strictly peaked (`p x < 1` for `x ≠ 0`, `p 0 = 1`), then at time `t` every
shell sits at its ceiling iff every peak time equals `t`.  The certified
margin reaches `1` exactly when all weighted fluxes peak together. -/
theorem lag_model_crossing_iff_simultaneous {ι : Type*} {p : ℝ → ℝ}
    (hpeak : p 0 = 1) (hstrict : ∀ x, x ≠ 0 → p x < 1)
    {τ : ι → ℝ} (t : ℝ) :
    (∀ i, 1 ≤ p (t - τ i)) ↔ ∀ i, τ i = t := by
  constructor
  · intro h i
    by_contra hne
    have hx : t - τ i ≠ 0 := fun h0 => hne (by linarith)
    exact absurd (h i) (not_le.mpr (hstrict _ hx))
  · intro h i
    rw [h i, sub_self, hpeak]

/-- **Tail spread under geometric lags.**  If consecutive peak lags are
nonneg and geometrically summable, `0 ≤ τ (j+1) − τ j ≤ D r^j`, then for
all `j ≥ J₀` the peak time lies in `[τ J₀, τ J₀ + D r^{J₀}/(1 − r)]`:
the tail spread from shell `J₀` on is `≤ D r^{J₀}/(1−r)`. -/
theorem tail_spread_of_geometric_lags {τ : ℕ → ℝ} {D r : ℝ}
    (hD : 0 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmono : ∀ j, τ j ≤ τ (j+1))
    (hdelay : ∀ j, τ (j+1) - τ j ≤ D * r ^ j) (J₀ : ℕ) :
    ∀ j, J₀ ≤ j → τ J₀ ≤ τ j ∧ τ j ≤ τ J₀ + D * r ^ J₀ / (1 - r) := by
  intro j hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  refine ⟨?_, ?_⟩
  · -- monotonicity along the tail
    have hm : Monotone τ := monotone_nat_of_le_succ hmono
    exact hm (Nat.le_add_right _ _)
  · -- shift the sequence and apply the front-arrival bound
    have hshift := front_arrival_bounded (t := fun k => τ (J₀ + k))
      (D := D * r ^ J₀) (r := r) (by positivity) hr0 hr1
      (fun k => by
        have := hdelay (J₀ + k)
        calc τ (J₀ + (k + 1)) - τ (J₀ + k) = τ (J₀ + k + 1) - τ (J₀ + k) := by
              rw [Nat.add_assoc]
          _ ≤ D * r ^ (J₀ + k) := this
          _ = D * r ^ J₀ * r ^ k := by rw [pow_add]; ring) k
    simpa using hshift

/-- **Tail margin under geometric lags (lag model).**  Combining the two:
with a common `L`-Lipschitz shape and geometrically summable peak lags,
there is a time at which every shell `j ≥ J₀` is within
`L·D r^{J₀}/(2(1−r))` of its ceiling.  As `J₀ → ∞` the tail-anchored
certified margin tends to `1`: in the lag model, the cost-decay branch
of Gap 2′ is the front-acceleration hypothesis for peak times. -/
theorem tail_margin_of_geometric_lags {p : ℝ → ℝ} {L : ℝ}
    (hpeak : p 0 = 1) (hlip : ∀ x y, |p x - p y| ≤ L * |x - y|)
    {τ : ℕ → ℝ} {D r : ℝ}
    (hD : 0 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmono : ∀ j, τ j ≤ τ (j+1))
    (hdelay : ∀ j, τ (j+1) - τ j ≤ D * r ^ j) (J₀ : ℕ) :
    ∃ t : ℝ, ∀ j, J₀ ≤ j →
      1 - L * (D * r ^ J₀ / (1 - r) / 2) ≤ p (t - τ j) := by
  refine ⟨(τ J₀ + (τ J₀ + D * r ^ J₀ / (1 - r))) / 2, fun j hj => ?_⟩
  have hτ := tail_spread_of_geometric_lags hD hr0 hr1 hmono hdelay J₀
  have := lag_model_margin_bound (ι := {j : ℕ // J₀ ≤ j}) hpeak hlip
    (τ := fun i => τ i.1) (lo := τ J₀) (hi := τ J₀ + D * r ^ J₀ / (1 - r))
    (fun i => hτ i.1 i.2) ⟨j, hj⟩
  have heq : (τ J₀ + D * r ^ J₀ / (1 - r) - τ J₀) / 2
      = D * r ^ J₀ / (1 - r) / 2 := by ring
  simpa [heq] using this

end EnergyDefect
