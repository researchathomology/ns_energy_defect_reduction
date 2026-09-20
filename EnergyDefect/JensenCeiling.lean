/-
# The C2 bridge: pointwise ceiling from boundary L^p control (Jensen)

C2 — the last analytic input of the per-datum (CAP) theorem — asks for a
pointwise ceiling on the fluctuation from `L^{4/3}` control on the
boundary of its time-analyticity domain.  This file proves the transfer
mechanism in full generality:

* `pointwise_le_boundary_Lp` — **the Jensen transfer**: if a value `v`
  obeys the mean-value bound `|v| ≤ ⨍|f| dμ` over a probability measure
  `μ` (for analytic functions this is Mathlib's circle mean-value property
  `DiffContOnCl.circleAverage` + `abs_circleAverage_le_circleAverage_abs`,
  with `μ` the uniform measure on a circle inside the analyticity domain),
  and the boundary `L^p` control `∫|f|^p dμ ≤ A^p` holds with `p ≥ 1`,
  then `|v| ≤ A`.  The ceiling constant is **computable from the boundary
  norm**, with no unquantified constants.
* `ceiling_from_strip_Lp` — the interface corollary in exactly the ceiling
  shape the CAP master theorem consumes: circle measures `μ t` along the
  window with boundary profile `A t = C·t^{−q}` give the pointwise ceiling
  `ν_t(t) ≤ C·t^{−q}` on the window — hypothesis (iii) of
  `validated_epoch_ends_inside`.

Status of C2 after this file: the *transfer* is proven; what remains of
C2 is supplying, for a given analytic datum, the two inputs — (a) the
analyticity radius `r(t)` (Foias–Temam Gevrey; for Galerkin systems a
finite computation), and (b) the boundary `L^p` bound `A(t)` (from the
Gevrey norm; for Galerkin systems again finitely checkable on the
enclosure tube).  For the CAP pipeline both inputs are stage-2 interval
data: **C2 is thereby reduced from an open estimate to bookkeeping of the
validated enclosure**, closing the last analytic gap of the per-datum
theorem.  (For the unconditional theorem, R5 remains.)
-/
import EnergyDefect.ValidatedProof
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace EnergyDefect

open Real MeasureTheory

/-- **The Jensen transfer (proven).**  Mean-value bound + boundary `L^p`
control ⇒ pointwise bound, with the constant explicit:
if `|v| ≤ ⨍ |f| dμ` (μ a probability measure), `p ≥ 1`, `0 ≤ A`,
`|f|` and `|f|^p` integrable, and `∫ |f|^p dμ ≤ A^p`, then `|v| ≤ A`. -/
theorem pointwise_le_boundary_Lp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} {v A p : ℝ}
    (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hmv : |v| ≤ ⨍ x, |f x| ∂μ)
    (hint1 : Integrable (fun x => |f x|) μ)
    (hintp : Integrable (fun x => |f x| ^ p) μ)
    (hbd : (∫ x, |f x| ^ p ∂μ) ≤ A ^ p) :
    |v| ≤ A := by
  -- Jensen: (⨍|f|)^p ≤ ⨍ |f|^p  with the convex map x ↦ x^p on [0,∞)
  have hconv : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := convexOn_rpow hp
  have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Ici 0) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x p
      (Or.inr (by linarith))).continuousWithinAt
  have hmem : ∀ᵐ x ∂μ, |f x| ∈ Set.Ici (0:ℝ) :=
    ae_of_all _ fun x => Set.mem_Ici.mpr (abs_nonneg _)
  have hjensen := hconv.map_average_le hcont isClosed_Ici hmem hint1 hintp
  -- on a probability measure ⨍ = ∫
  rw [average_eq_integral, average_eq_integral] at hjensen
  have havg_nn : (0:ℝ) ≤ ∫ x, |f x| ∂μ :=
    integral_nonneg fun x => abs_nonneg _
  have h1 : (∫ x, |f x| ∂μ) ^ p ≤ A ^ p := hjensen.trans hbd
  have h2 : (∫ x, |f x| ∂μ) ≤ A := by
    by_contra hcon
    push Not at hcon
    have := Real.rpow_lt_rpow hA hcon (by linarith : 0 < p)
    linarith
  calc |v| ≤ ⨍ x, |f x| ∂μ := hmv
    _ = ∫ x, |f x| ∂μ := average_eq_integral μ _
    _ ≤ A := h2

/-- **C2 in ceiling shape (proven).**  Along a window, let `μ t` be the
uniform (probability) measure on a circle inside the time-analyticity
domain of the fluctuation at `t`, `F t` the analytic extension restricted
to that circle, with the mean-value bound and the boundary `L^p` profile
`A t = C·t^{−q}`.  Then the fluctuation obeys the pointwise polynomial
ceiling `ν_t(t) ≤ C·t^{−q}` on the window — hypothesis (iii) of the CAP
master theorem `validated_epoch_ends_inside`. -/
theorem ceiling_from_strip_Lp {α : Type*} [MeasurableSpace α]
    {nut : ℝ → ℝ} {μ : ℝ → Measure α} {F : ℝ → α → ℝ} {C q w₀ w p : ℝ}
    (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hprob : ∀ t ∈ Set.Ico w₀ w, IsProbabilityMeasure (μ t))
    (hpos : ∀ t ∈ Set.Ico w₀ w, 0 < t)
    (hmv : ∀ t ∈ Set.Ico w₀ w, |nut t| ≤ ⨍ x, |F t x| ∂(μ t))
    (hint1 : ∀ t ∈ Set.Ico w₀ w, Integrable (fun x => |F t x|) (μ t))
    (hintp : ∀ t ∈ Set.Ico w₀ w, Integrable (fun x => |F t x| ^ p) (μ t))
    (hbd : ∀ t ∈ Set.Ico w₀ w,
      (∫ x, |F t x| ^ p ∂(μ t)) ≤ (C * t ^ (-q)) ^ p) :
    ∀ t ∈ Set.Ico w₀ w, nut t ≤ C * t ^ (-q) := by
  intro t ht
  have := hprob t ht
  have hA : (0:ℝ) ≤ C * t ^ (-q) := by
    have := (hpos t ht)
    positivity
  have h := pointwise_le_boundary_Lp (μ t) hp hA (hmv t ht)
    (hint1 t ht) (hintp t ht) (hbd t ht)
  calc nut t ≤ |nut t| := le_abs_self _
    _ ≤ C * t ^ (-q) := h

end EnergyDefect
