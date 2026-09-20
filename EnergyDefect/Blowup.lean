/-
# The blowup mechanism (Fig. 1, eq. `eq:compare`, Theorem `sec:blowup`.1)

Formalization of the quantitative engine of the blowup proof of
"Non-Smooth Solutions of the Navier-Stokes Equation and their Means"
(Glimm–Petrillo, `nsmill.tex`).

The paper's "three contradictory facts" (Sec. 1.4) are:

* **F1** the solution energy decays at the *slow* exact viscous rate
  `O(e^{-νt/2})` (Lemma/Theorem `sec:ent`.1; see `EnergyDecay.lean`);
* **F2** the turbulent fluctuation `ν_t` decays at the *fast* rate
  `O(e^{-3t/4})` (Theorem `sec:ent`.1(b)) — an unproven step of the paper
  (blueprint gap G/F2), taken here as the hypothesis `hfast`;
* **F3** for entropy-production-maximizing solutions, `ν_t` remains *above*
  the viscous decay curve of the solution (Theorem `sec:ent`.1(c)) — resting
  on the entropy principle, taken here as the hypothesis `hfloor`.

We prove that F2 and F3 are jointly satisfiable only up to the explicit
crossing time `T* = log(A/B)/(3/4 - ν/2)` (for `0 < ν < 3/2`), so the epoch
of regularity is finite — the skeleton of Theorem `sec:blowup`.1 ("This time
is `T* < ∞`. `T*` is the time of blowup") and the precise form of the
paper's claim that eq. `eq:compare` "is logically contradictory for large T".

We also prove the ODE form of the argument used in earlier versions of the
paper: a quantity decreasing at a rate bounded away from `0` crosses any
floor in finite time (`finite_time_floor_crossing`).

Blueprint nodes: CORE [F], with F2, F3 as hypotheses.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace EnergyDefect

open Real

/-- The crossing time `T*` of Fig. 1: the time at which the fast-decaying
fluctuation bound `A e^{-at}` crosses the slow-decaying viscous floor
`B e^{-bt}`. -/
noncomputable def crossingTime (A B a b : ℝ) : ℝ :=
  Real.log (A / B) / (a - b)

/-- A slow-decaying exponential can stay below a fast-decaying exponential
only up to the crossing time: if `B e^{-bt} ≤ A e^{-at}` with `b < a`
and `A, B > 0`, then `t ≤ T*`. -/
theorem le_crossingTime {A B a b t : ℝ} (hA : 0 < A) (hB : 0 < B) (hab : b < a)
    (h : B * exp (-(b * t)) ≤ A * exp (-(a * t))) :
    t ≤ crossingTime A B a b := by
  have hgap : 0 < a - b := sub_pos.2 hab
  have h1 : B * exp ((a - b) * t) ≤ A := by
    have h2 := mul_le_mul_of_nonneg_right h (exp_pos (a * t)).le
    calc B * exp ((a - b) * t)
        = B * exp (-(b * t)) * exp (a * t) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ A * exp (-(a * t)) * exp (a * t) := h2
      _ = A := by rw [mul_assoc, ← Real.exp_add]; simp
  have h3 : exp ((a - b) * t) ≤ A / B := (le_div_iff₀' hB).2 h1
  have h4 : (a - b) * t ≤ Real.log (A / B) :=
    (Real.le_log_iff_exp_le (div_pos hA hB)).2 h3
  have h5 : t * (a - b) ≤ Real.log (A / B) := by rw [mul_comm]; exact h4
  exact (le_div_iff₀ hgap).2 h5

/-- **Eq. `eq:compare` is "logically contradictory for large T"**: strictly
beyond the crossing time, the fast-decaying bound is *strictly below* the
slow-decaying floor. -/
theorem fast_lt_slow_beyond_crossing {A B a b t : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hab : b < a)
    (ht : crossingTime A B a b < t) :
    A * exp (-(a * t)) < B * exp (-(b * t)) := by
  by_contra hcon
  push Not at hcon
  exact absurd (le_crossingTime hA hB hab hcon) (not_le.2 ht)

/-- **Skeleton of Theorem `sec:blowup`.1.** Let `ν_t` be the turbulent
fluctuation of a weak solution on its epoch of regularity `S`, satisfying

* (F3, `hfloor`) `ν_t` dominates the viscous decay floor `B e^{-(ν/2)t}`, and
* (F2, `hfast`) `ν_t` is bounded by the fast fluctuation decay `A e^{-(3/4)t}`,

with `0 < ν < 3/2`.  Then every time in `S` is at most the crossing time
`T* = log(A/B)/(3/4 - ν/2)`: the epoch of regularity is finite. -/
theorem epoch_of_regularity_bounded {S : Set ℝ} {nut : ℝ → ℝ} {A B ν : ℝ}
    (hA : 0 < A) (hB : 0 < B) (_hν : 0 < ν) (hν' : ν < 3 / 2)
    (hfloor : ∀ t ∈ S, B * exp (-(ν / 2 * t)) ≤ nut t)
    (hfast : ∀ t ∈ S, nut t ≤ A * exp (-(3 / 4 * t))) :
    ∀ t ∈ S, t ≤ crossingTime A B (3 / 4) (ν / 2) := by
  intro t ht
  exact le_crossingTime hA hB (by linarith) ((hfloor t ht).trans (hfast t ht))

/-- The epoch of regularity is bounded above (finiteness of `T*`). -/
theorem epoch_bddAbove {S : Set ℝ} {nut : ℝ → ℝ} {A B ν : ℝ}
    (hA : 0 < A) (hB : 0 < B) (_hν : 0 < ν) (hν' : ν < 3 / 2)
    (hfloor : ∀ t ∈ S, B * exp (-(ν / 2 * t)) ≤ nut t)
    (hfast : ∀ t ∈ S, nut t ≤ A * exp (-(3 / 4 * t))) :
    BddAbove S :=
  ⟨crossingTime A B (3 / 4) (ν / 2),
    fun _ ht => epoch_of_regularity_bounded hA hB _hν hν' hfloor hfast _ ht⟩

/-- **No global regularity**: facts F2 and F3 cannot hold on all of `[0, ∞)`.
This is the contradiction that forces the end of the epoch of regularity. -/
theorem not_globally_regular {nut : ℝ → ℝ} {A B ν : ℝ}
    (hA : 0 < A) (hB : 0 < B) (_hν : 0 < ν) (hν' : ν < 3 / 2)
    (hfloor : ∀ t : ℝ, 0 ≤ t → B * exp (-(ν / 2 * t)) ≤ nut t)
    (hfast : ∀ t : ℝ, 0 ≤ t → nut t ≤ A * exp (-(3 / 4 * t))) :
    False := by
  set T := max 0 (crossingTime A B (3 / 4) (ν / 2)) + 1 with hT
  have hmax0 := le_max_left 0 (crossingTime A B (3 / 4) (ν / 2))
  have hmaxc := le_max_right 0 (crossingTime A B (3 / 4) (ν / 2))
  have hT0 : 0 ≤ T := by simp only [hT]; linarith
  have h1 : T ≤ crossingTime A B (3 / 4) (ν / 2) :=
    le_crossingTime hA hB (by linarith) ((hfloor T hT0).trans (hfast T hT0))
  simp only [hT] at h1
  linarith

/-- **Existence of a finite blowup time** (Theorem `sec:blowup`.1): if the
epoch of regularity is an interval `[0, e)` on which F2 and F3 hold, then its
endpoint satisfies `e ≤ max 0 T*`; in particular the epoch is finite and ends
at some `T* < ∞`, the time of blowup. -/
theorem blowup_time_le {nut : ℝ → ℝ} {A B ν e : ℝ}
    (hA : 0 < A) (hB : 0 < B) (_hν : 0 < ν) (hν' : ν < 3 / 2)
    (hfloor : ∀ t ∈ Set.Ico (0 : ℝ) e, B * exp (-(ν / 2 * t)) ≤ nut t)
    (hfast : ∀ t ∈ Set.Ico (0 : ℝ) e, nut t ≤ A * exp (-(3 / 4 * t))) :
    e ≤ max 0 (crossingTime A B (3 / 4) (ν / 2)) := by
  by_contra hcon
  push Not at hcon
  set M := max 0 (crossingTime A B (3 / 4) (ν / 2)) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMc : crossingTime A B (3 / 4) (ν / 2) ≤ M := le_max_right _ _
  set t := (M + e) / 2 with htdef
  have ht0 : 0 ≤ t := by simp only [htdef]; linarith
  have hte : t < e := by simp only [htdef]; linarith
  have htM : M < t := by simp only [htdef]; linarith
  have h1 := epoch_of_regularity_bounded hA hB _hν hν' hfloor hfast t ⟨ht0, hte⟩
  linarith

/-- The paper's rate hypothesis: for `0 < ν < 1/4` (eq. `eq:compare`), the
viscous rate `ν/2` is strictly slower than the fluctuation rate `3/4`. -/
theorem paper_rate_gap {ν : ℝ} (h0 : 0 < ν) (h : ν < 1 / 4) : ν / 2 < 3 / 4 := by
  linarith

/-- **ODE form of the blowup argument** (used in earlier revisions of the
paper): a differentiable quantity whose decrease rate is bounded below by
`D_min > 0` falls below any floor `m ≤ f 0` by the finite time
`(f 0 - m)/D_min`.  "While non-zero, `ν_t(s)` … decreases at the
`s`-independent rate `D_min > 0`; for a finite value of `s` it is smaller
than its allowed strictly positive minimum." -/
theorem finite_time_floor_crossing {f : ℝ → ℝ} {D : ℝ} (hD : 0 < D)
    (hf : Differentiable ℝ f) (hf' : ∀ t, deriv f t ≤ -D)
    {m : ℝ} (hm : m ≤ f 0) :
    f ((f 0 - m) / D) ≤ m := by
  have key : ∀ t, 0 ≤ t → f t ≤ f 0 - D * t := by
    intro t ht
    have hg : ∀ s, HasDerivAt (fun r => f r + D * r) (deriv f s + D) s := by
      intro s
      have h1 : HasDerivAt (fun r : ℝ => D * r) D s := by
        simpa using (hasDerivAt_id s).const_mul D
      exact ((hf s).hasDerivAt).add h1
    have hanti : Antitone fun r => f r + D * r := by
      refine antitone_of_deriv_nonpos (fun s => (hg s).differentiableAt) fun s => ?_
      rw [(hg s).deriv]
      linarith [hf' s]
    have h := hanti ht
    simp only [mul_zero, add_zero] at h
    linarith
  have hT : 0 ≤ (f 0 - m) / D := div_nonneg (by linarith) hD.le
  have h := key _ hT
  have hcancel : D * ((f 0 - m) / D) = f 0 - m := by field_simp
  linarith [hcancel ▸ h]

end EnergyDefect
