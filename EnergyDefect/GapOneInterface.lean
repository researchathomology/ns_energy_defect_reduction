/-
# Gap 1 interface: the ceiling constant, and what a computed witness can beat

Gap 1 of `nsmill_nonsmooth.tex` asks for the analytic ceiling
`ν_t(t) ≤ C·t^{−q}` on the epoch, with `C` from data.  The transfer from
strip-boundary `L^p` control to the pointwise ceiling is proven
(`ceiling_from_strip_Lp`).  This file supplies

* `StripCeilingData` — the **scaffolded interface**: the record of inputs
  Gap 1 must produce (circle measures inside the analyticity domain, the
  analytic extension on the circles, mean-value bound, boundary `L^p`
  profile `C·t^{−q}`).  Filling a term of this structure for Navier–Stokes
  *is* Gap 1; no proof is offered here.  `StripCeilingData.ceiling`
  discharges the ceiling hypothesis (iii) of `validated_epoch_ends_inside`.
* `radius_floor_of_enstrophy_bound` — the Foias–Temam-type radius scaling
  as an interface lemma: a radius bound `r(t) ≥ c ν³/Z(t)²` (hypothesis;
  the PDE input) and an enstrophy bound on the window give a uniform
  strip width.  Records that the analyticity radius is enstrophy-controlled.
* `ceiling_dominates_weighted_sup` — any valid pointwise ceiling
  constant dominates the weighted supremum `Π(t) t^q` on the window: the
  campaign's certified `C_sup` is a lower bound for every admissible `C`
  (the certified margin bounds the true margin from above).
* `galerkin_uniform_ceiling_unwitnessable` — **the obstruction.**  If the
  ceiling `C·t^{−q}` also holds for the *computed* trajectory `ν̃_t` on the
  window where its floors are verified, then the margin check
  `max w₀ ((C/(B−ε))^{1/q}) < w` of the CAP master theorem is false: the
  hypotheses of `validated_epoch_ends_inside` are jointly unsatisfiable.
  Every ceiling proven by energy methods that commute with the Galerkin
  projection (energy budget, `L^{4/3}` bounds of the Leray–Hopf class,
  Foias–Temam Gevrey radius and norms, the Jensen transfer) holds for the
  Galerkin trajectory with the same constants — so no such ceiling can be
  witnessed by a Galerkin computation.
* `witness_requires_truncation_violation` — the contrapositive as a
  positive statement: if the CAP hypotheses do hold, the computed
  trajectory violates the ceiling somewhere on the window.  The witness
  condition is *exactly* a ceiling violation by the truncated flow.

Epistemic status: theorems are elementary real arithmetic (Lean-verified).
The classification of which ceilings are Galerkin-uniform is a paper
argument (`research/routes/GAP1_CONSTANT.md`), labelled there.
-/
import EnergyDefect.JensenCeiling

namespace EnergyDefect

open Real MeasureTheory

/-- **The Gap 1 interface.**  Everything the strip/Jensen ceiling needs for
a functional `nut` on the window `[w₀, w)`: at each `t`, a probability
measure `μ t` (uniform measure on a circle of radius `r(t)` inside the
time-analyticity domain), the analytic extension `F t` on that circle,
the mean-value bound, integrability, and the boundary `L^p` profile
`C·t^{−q}`.  Producing a term of this type for Navier–Stokes with `C`
controlled by the data norms is Gap 1. -/
structure StripCeilingData {α : Type*} [MeasurableSpace α]
    (nut : ℝ → ℝ) (w₀ w : ℝ) where
  C : ℝ
  q : ℝ
  p : ℝ
  μ : ℝ → Measure α
  F : ℝ → α → ℝ
  hp : 1 ≤ p
  hC : 0 ≤ C
  hprob : ∀ t ∈ Set.Ico w₀ w, IsProbabilityMeasure (μ t)
  hpos : ∀ t ∈ Set.Ico w₀ w, 0 < t
  hmv : ∀ t ∈ Set.Ico w₀ w, |nut t| ≤ ⨍ x, |F t x| ∂(μ t)
  hint1 : ∀ t ∈ Set.Ico w₀ w, Integrable (fun x => |F t x|) (μ t)
  hintp : ∀ t ∈ Set.Ico w₀ w, Integrable (fun x => |F t x| ^ p) (μ t)
  hbd : ∀ t ∈ Set.Ico w₀ w,
    (∫ x, |F t x| ^ p ∂(μ t)) ≤ (C * t ^ (-q)) ^ p

/-- A `StripCeilingData` term discharges the ceiling hypothesis of the CAP
master theorem (via the proven Jensen transfer). -/
theorem StripCeilingData.ceiling {α : Type*} [MeasurableSpace α]
    {nut : ℝ → ℝ} {w₀ w : ℝ} (d : StripCeilingData (α := α) nut w₀ w) :
    ∀ t ∈ Set.Ico w₀ w, nut t ≤ d.C * t ^ (-d.q) :=
  ceiling_from_strip_Lp d.hp d.hC d.hprob d.hpos d.hmv d.hint1 d.hintp d.hbd

/-- **Radius from an enstrophy bound (interface lemma).**  If the
time-analyticity radius obeys the Foias–Temam-type scaling
`r(t) ≥ c ν³ / Z(t)²` (hypothesis: the PDE input, with `Z` the enstrophy)
and `0 < Z(t) ≤ Zmax` on the window, then `r(t) ≥ c ν³ / Zmax²` there.
The strip width is controlled by the enstrophy on the window — the
quantity whose a priori control is the regularity problem itself. -/
theorem radius_floor_of_enstrophy_bound {r Z : ℝ → ℝ} {c ν Zmax w₀ w : ℝ}
    (hc : 0 ≤ c) (hν : 0 ≤ ν)
    (hFT : ∀ t ∈ Set.Ico w₀ w, c * ν ^ 3 / Z t ^ 2 ≤ r t)
    (hZ : ∀ t ∈ Set.Ico w₀ w, 0 < Z t ∧ Z t ≤ Zmax) :
    ∀ t ∈ Set.Ico w₀ w, c * ν ^ 3 / Zmax ^ 2 ≤ r t := by
  intro t ht
  obtain ⟨hZ0, hZm⟩ := hZ t ht
  have hZmax : 0 < Zmax := lt_of_lt_of_le hZ0 hZm
  have hsq : Z t ^ 2 ≤ Zmax ^ 2 := pow_le_pow_left₀ hZ0.le hZm 2
  calc c * ν ^ 3 / Zmax ^ 2 ≤ c * ν ^ 3 / Z t ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ ≤ r t := hFT t ht

/-- **Any admissible ceiling constant dominates the weighted supremum.**
If `nut t ≤ C·t^{−q}` on the window, then `nut t · t^q ≤ C` there: the
campaign's certified constant `C_sup = sup_t Π t^q` is a lower bound for
every valid ceiling constant, and the certified margin bounds the true
margin from above. -/
theorem ceiling_dominates_weighted_sup {nut : ℝ → ℝ} {C q w₀ w : ℝ}
    (hpos : ∀ t ∈ Set.Ico w₀ w, 0 < t)
    (hceil : ∀ t ∈ Set.Ico w₀ w, nut t ≤ C * t ^ (-q)) :
    ∀ t ∈ Set.Ico w₀ w, nut t * t ^ q ≤ C := by
  intro t ht
  have ht0 := hpos t ht
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht0 q
  have h := hceil t ht
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv, le_div_iff₀ htq] at h
  exact h

/-- **Galerkin-uniform ceilings are unwitnessable.**  Let the computed
trajectory `nutN` carry the verified floors `B ≤ nutN` on the nonempty
window `[w₀, w)` and *also* obey the ceiling `nutN ≤ C·t^{−q}` there
(as it does whenever the ceiling theorem applies to the truncated system
with the same constant).  Then for any enclosure `0 ≤ ε < B` the margin
check of the CAP master theorem fails:
`¬ (max w₀ ((C/(B−ε))^{1/q}) < w)`.  The hypotheses of
`validated_epoch_ends_inside` cannot be met by such a computation. -/
theorem galerkin_uniform_ceiling_unwitnessable {nutN : ℝ → ℝ}
    {B C q w₀ w ε : ℝ}
    (hq : 0 < q) (hw₀ : 0 ≤ w₀) (hε : 0 ≤ ε) (hεB : ε < B)
    (hfloorN : ∀ t ∈ Set.Ico w₀ w, B ≤ nutN t)
    (hceilN : ∀ t ∈ Set.Ico w₀ w, nutN t ≤ C * t ^ (-q)) :
    ¬ (max w₀ ((C / (B - ε)) ^ q⁻¹) < w) := by
  intro hwin
  set M := max w₀ ((C / (B - ε)) ^ q⁻¹) with hM
  have hM0 : w₀ ≤ M := le_max_left _ _
  have hMc : (C / (B - ε)) ^ q⁻¹ ≤ M := le_max_right _ _
  set t := (M + w) / 2 with ht
  have htw : t < w := by simp only [ht]; linarith
  have hMt : M < t := by simp only [ht]; linarith
  have htw₀ : w₀ ≤ t := le_trans hM0 hMt.le
  have ht0 : 0 < t := lt_of_le_of_lt (hw₀.trans hM0) hMt
  have hmem : t ∈ Set.Ico w₀ w := ⟨htw₀, htw⟩
  have hB : 0 < B := lt_of_le_of_lt hε hεB
  have hBε : 0 < B - ε := by linarith
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht0 q
  -- floor ∧ ceiling at t:  B·t^q ≤ C
  have h1 : B ≤ C * t ^ (-q) := (hfloorN t hmem).trans (hceilN t hmem)
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv, le_div_iff₀ htq] at h1
  -- hence C > 0 and C/(B−ε) ≥ 0
  have hC : 0 < C := lt_of_lt_of_le (by positivity) h1
  have hratio : 0 ≤ C / (B - ε) := by positivity
  -- from (C/(B−ε))^{1/q} < t:  C/(B−ε) < t^q
  have h2 : C / (B - ε) < t ^ q := by
    have hlt : (C / (B - ε)) ^ q⁻¹ < t := lt_of_le_of_lt hMc hMt
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hratio _) hlt hq
    rwa [← Real.rpow_mul hratio, inv_mul_cancel₀ hq.ne', Real.rpow_one] at this
  -- (B−ε)·t^q > C ≥ B·t^q  ⇒  ε·t^q < 0, contradiction
  have h3 : C < (B - ε) * t ^ q := by
    rw [div_lt_iff₀ hBε] at h2; linarith
  have h4 : ε * t ^ q < 0 := by nlinarith
  have h5 : 0 ≤ ε * t ^ q := by positivity
  linarith

/-- **A witness is a ceiling violation by the truncated flow.**  If the
finitely-checkable hypotheses of the CAP master theorem hold for the
computed trajectory (floors on the window and the margin check), then the
computed trajectory exceeds the ceiling `C·t^{−q}` somewhere on the
window.  The Gap 1 constant a computation can witness must therefore be
one the *truncated* dynamics does not obey — ceilings inherited by every
Galerkin truncation (energy-method ceilings) are excluded. -/
theorem witness_requires_truncation_violation {nutN : ℝ → ℝ}
    {B C q w₀ w ε : ℝ}
    (hq : 0 < q) (hw₀ : 0 ≤ w₀) (hε : 0 ≤ ε) (hεB : ε < B)
    (hfloorN : ∀ t ∈ Set.Ico w₀ w, B ≤ nutN t)
    (hwin : max w₀ ((C / (B - ε)) ^ q⁻¹) < w) :
    ∃ t ∈ Set.Ico w₀ w, C * t ^ (-q) < nutN t := by
  by_contra hcon
  push Not at hcon
  exact galerkin_uniform_ceiling_unwitnessable hq hw₀ hε hεB hfloorN
    (fun t ht => hcon t ht) hwin

end EnergyDefect
