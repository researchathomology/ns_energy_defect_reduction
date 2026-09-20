/-
# Research interface: from decay bounds to blowup

Proven glue between the research targets F2′/F3′ (see
`research/F2/TARGET.md`, `research/F3/TARGET.md`) and the verified blowup
engine of `EnergyDefect.Blowup`.

The point of this file: the search for F2′/F3′ is *rate-flexible*.  Any
future proof producing a floor `B e^{-bt} ≤ ν_t` and a ceiling
`ν_t ≤ A e^{-at}` with `0 < A`, `0 < B`, `b < a` — packaged as a
`DecayBounds` — immediately forces the epoch of regularity to end by
`max 0 T*` with `T* = log(A/B)/(a-b)` (`epoch_le_of_decayBounds`), and
rules out global regularity (`no_global_decayBounds`).  In particular the
paper's ν-uniform ceiling rate `3/4` is unnecessary: per-viscosity rates
such as floor `ν` vs. ceiling `2ν` suffice (`spectral_rate_gap`).
-/
import EnergyDefect.Blowup

namespace EnergyDefect

open EnergyDefect Real

/-- What a successful joint proof of the research targets F3′ (floor) and
F2′ (ceiling) must deliver for the fluctuation `nut` on an epoch of
regularity `[0, e)`.  The rates `a, b` and prefactors `A, B` may depend on
the viscosity in any way; only `b < a` is required. -/
structure DecayBounds (nut : ℝ → ℝ) (e : ℝ) where
  /-- Ceiling prefactor. -/
  A : ℝ
  /-- Floor prefactor. -/
  B : ℝ
  /-- Ceiling rate. -/
  a : ℝ
  /-- Floor rate. -/
  b : ℝ
  hA : 0 < A
  hB : 0 < B
  /-- The only rate condition needed: the ceiling decays strictly faster. -/
  hab : b < a
  /-- F3′: the floor, on the epoch. -/
  floor : ∀ t ∈ Set.Ico (0 : ℝ) e, B * Real.exp (-(b * t)) ≤ nut t
  /-- F2′: the ceiling, on the epoch. -/
  ceiling : ∀ t ∈ Set.Ico (0 : ℝ) e, nut t ≤ A * Real.exp (-(a * t))

/-- **Glue theorem (proven).**  Any `DecayBounds` package forces the epoch of
regularity to end by `max 0 T*`, `T* = log(A/B)/(a-b)`.  Rate-agnostic:
this is the entire remaining content of the paper's Part IV once F2′ and
F3′ are supplied. -/
theorem epoch_le_of_decayBounds {nut : ℝ → ℝ} {e : ℝ} (d : DecayBounds nut e) :
    e ≤ max 0 (crossingTime d.A d.B d.a d.b) := by
  by_contra hcon
  push Not at hcon
  set M := max 0 (crossingTime d.A d.B d.a d.b) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMc : crossingTime d.A d.B d.a d.b ≤ M := le_max_right _ _
  set t := (M + e) / 2 with ht
  have ht0 : 0 ≤ t := by simp only [ht]; linarith
  have hte : t < e := by simp only [ht]; linarith
  have htM : M < t := by simp only [ht]; linarith
  have h1 := le_crossingTime d.hA d.hB d.hab
    ((d.floor t ⟨ht0, hte⟩).trans (d.ceiling t ⟨ht0, hte⟩))
  linarith

/-- Global form of the targets: a floor/ceiling pair with **fixed** constants
holding for all `t ≥ 0`. -/
structure GlobalDecayBounds (nut : ℝ → ℝ) where
  /-- Ceiling prefactor. -/
  A : ℝ
  /-- Floor prefactor. -/
  B : ℝ
  /-- Ceiling rate. -/
  a : ℝ
  /-- Floor rate. -/
  b : ℝ
  hA : 0 < A
  hB : 0 < B
  /-- The only rate condition needed: the ceiling decays strictly faster. -/
  hab : b < a
  /-- F3′ on `[0, ∞)`. -/
  floor : ∀ t, 0 ≤ t → B * Real.exp (-(b * t)) ≤ nut t
  /-- F2′ on `[0, ∞)`. -/
  ceiling : ∀ t, 0 ≤ t → nut t ≤ A * Real.exp (-(a * t))

/-- **No global regularity from decay bounds (proven).**  A `GlobalDecayBounds`
package is contradictory: F2′ + F3′ with fixed constants and any rates
`b < a` cannot hold on all of `[0, ∞)`.  (Note the constants must be fixed:
if the prefactors were allowed to grow with the time horizon, the pair of
bounds would be satisfiable globally — a further reason the research
targets must produce horizon-independent constants.) -/
theorem no_global_decayBounds {nut : ℝ → ℝ} (d : GlobalDecayBounds nut) :
    False := by
  set T := max 0 (crossingTime d.A d.B d.a d.b) + 1 with hT
  have hmax0 := le_max_left 0 (crossingTime d.A d.B d.a d.b)
  have hmaxc := le_max_right 0 (crossingTime d.A d.B d.a d.b)
  have hT0 : 0 ≤ T := by simp only [hT]; linarith
  have h1 := le_crossingTime d.hA d.hB d.hab
    ((d.floor T hT0).trans (d.ceiling T hT0))
  simp only [hT] at h1
  linarith

/-- **Rate flexibility (proven).**  Per-viscosity rates suffice for the
engine: e.g. a floor at rate `ν` and a ceiling at rate `2ν` satisfy the
required gap for every `ν > 0`.  The paper's ν-uniform ceiling rate `3/4`
(which is unattainable for solutions obeying Foias–Saut `O(ν)` asymptotics)
is not needed. -/
theorem spectral_rate_gap {ν : ℝ} (hν : 0 < ν) : ν < 2 * ν := by linarith

end EnergyDefect
