/-
# The energy profile along good times: right-limit envelope and defect jumps

For a Leray–Hopf solution the profile `Φ(t) = E(t) + ν∫₀ᵗ‖∇u‖²` is
nonincreasing along the set `G` of *good times* (times from which the
strong energy inequality holds); `G` has full measure, hence is dense from
the right, and `Φ` is right-lower-semicontinuous along `G` (weak `L²`
continuity of `u`).  The energy defect of a window is `𝒜(w₀,w) = Φ(w₀) − Φ(w)`.

We formalise the real-analytic skeleton with `f : ℝ → ℝ` for `Φ` and
`G : Set ℝ` for the good times.  All PDE inputs (good times of full
measure, weak `L²` continuity, energy equality on regular intervals, the
CKN slice covering) enter as explicit hypotheses; nothing is assumed
globally.

* `rightProfile f G t = sSup (f '' {s ∈ G | t < s})` is the right-limit
  envelope `Ψ` of `Φ` along good times.
* `le_rightProfile` — `Φ ≤ Ψ` everywhere: weak lower semicontinuity.
* `rightProfile_antitone` — `Ψ` is antitone: the monotone regularisation.
* `rightProfile_eq_of_mem` — `Ψ = Φ` on `G`.
* `apply_le_rightProfile_of_lt` — `Φ(t') ≤ Ψ(t)` for `t < t'`.
* `antitone_iff_eq_rightProfile` — full monotonicity of `Φ` is equivalent
  to `Φ = Ψ` (i.e. every time behaves as a good time — open for LH
  solutions).  Hence the defect over a window with good endpoints is the
  drop of `Ψ`.
* `defect_eq_jump_single_singular_time` — with a single singular time
  `tstar` separating two plateaus `L` (left) and `R` (right) and the LH
  ordering `f tstar ≤ R ≤ L`, the defect over any window straddling `tstar`
  is the jump `L − R ≥ 0`, and the defect over a window ending at `tstar`
  is at least the jump (the excess is the "dip" at a bad singular time).
* `no_jump_of_small_covers` — the real-analytic skeleton of "a
  Morrey-type local energy bound on the `ℋ¹`-null singular slice excludes
  an energy jump" (Leslie–Shvydkoy 2018 mechanism): if for every `ε` the
  quantity `m` splits below `Tstar` as `A + B` with `A ≤ Cε` eventually and
  `B → mstar`, then `m ≤ mstar + ε'` eventually for every `ε' > 0`.

Every statement here is also true for Galerkin flows (singular set
`Σ = ∅`, all times good); the file is a skeleton for the bookkeeping of
`𝒜`, not an input to Proposition P.
-/
import EnergyDefect.Sharpening
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic

namespace EnergyDefect

open Filter Topology

/-- The right-limit envelope of `f` along `G` at `t`: the supremum of `f`
over good times strictly to the right of `t`. -/
noncomputable def rightProfile (f : ℝ → ℝ) (G : Set ℝ) (t : ℝ) : ℝ :=
  sSup (f '' {s | s ∈ G ∧ t < s})

/-- The image set defining `rightProfile` is nonempty when `G` is dense
from the right. -/
theorem rightProfile_nonempty {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ) (t : ℝ) :
    (f '' {s | s ∈ G ∧ t < s}).Nonempty := by
  obtain ⟨s, hsG, hts, -⟩ := hG t 1 one_pos
  exact ⟨f s, s, ⟨hsG, hts⟩, rfl⟩

/-- The image set defining `rightProfile` is bounded above when `f '' G` is. -/
theorem rightProfile_bddAbove {f : ℝ → ℝ} {G : Set ℝ}
    (hbdd : BddAbove (f '' G)) (t : ℝ) :
    BddAbove (f '' {s | s ∈ G ∧ t < s}) :=
  hbdd.mono (Set.image_mono fun _ hs => hs.1)

/-- **Monotone regularisation.**  If `G` is dense from the right and `f` is
antitone on `G` with `f '' G` bounded above, then `rightProfile f G` is
antitone.  (The antitonicity of `f` on `G` is not even needed: the sets
shrink as `t` grows.) -/
theorem rightProfile_antitone {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hbdd : BddAbove (f '' G)) :
    Antitone (rightProfile f G) := by
  intro t t' htt'
  apply csSup_le_csSup (rightProfile_bddAbove hbdd t) (rightProfile_nonempty hG t')
  rintro _ ⟨s, ⟨hsG, hs⟩, rfl⟩
  exact ⟨s, ⟨hsG, lt_of_le_of_lt htt' hs⟩, rfl⟩

/-- **On good times `Ψ ≤ Φ`.**  From the strong energy inequality at a good
time `t`, every later value is `≤ f t`, hence so is the supremum. -/
theorem rightProfile_le_of_mem {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hsei : ∀ s ∈ G, ∀ t', s ≤ t' → f t' ≤ f s) :
    ∀ t ∈ G, rightProfile f G t ≤ f t := by
  intro t htG
  apply csSup_le (rightProfile_nonempty hG t)
  rintro _ ⟨s, ⟨-, hts⟩, rfl⟩
  exact hsei t htG s hts.le

/-- **Weak lower semicontinuity: `Φ ≤ Ψ` everywhere.**  Right-lsc of `f`
along `G` gives `f t ≤ f s + ε` for good `s` slightly to the right of `t`;
`f s ≤ Ψ t` by definition. -/
theorem le_rightProfile {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hlsc : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ G, t < s → s < t + δ → f t ≤ f s + ε)
    (hbdd : BddAbove (f '' G)) :
    ∀ t, f t ≤ rightProfile f G t := by
  intro t
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hlsc t ε hε
  obtain ⟨s, hsG, hts, hsδ⟩ := hG t δ hδ
  have h1 : f t ≤ f s + ε := hδε s hsG hts hsδ
  have h2 : f s ≤ rightProfile f G t :=
    le_csSup (rightProfile_bddAbove hbdd t) ⟨s, ⟨hsG, hts⟩, rfl⟩
  linarith

/-- **`Ψ = Φ` on good times.** -/
theorem rightProfile_eq_of_mem {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hsei : ∀ s ∈ G, ∀ t', s ≤ t' → f t' ≤ f s)
    (hlsc : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ G, t < s → s < t + δ → f t ≤ f s + ε)
    (hbdd : BddAbove (f '' G)) :
    ∀ t ∈ G, rightProfile f G t = f t :=
  fun t htG => le_antisymm (rightProfile_le_of_mem hG hsei t htG)
    (le_rightProfile hG hlsc hbdd t)

/-- **Later values lie below the envelope.**  For `t < t'` pick a good
`s ∈ (t, t')`; then `f t' ≤ f s ≤ Ψ t`. -/
theorem apply_le_rightProfile_of_lt {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hsei : ∀ s ∈ G, ∀ t', s ≤ t' → f t' ≤ f s)
    (hbdd : BddAbove (f '' G)) :
    ∀ t t', t < t' → f t' ≤ rightProfile f G t := by
  intro t t' htt'
  obtain ⟨s, hsG, hts, hst'⟩ := hG t (t' - t) (by linarith)
  have h1 : f t' ≤ f s := hsei s hsG t' (by linarith)
  have h2 : f s ≤ rightProfile f G t :=
    le_csSup (rightProfile_bddAbove hbdd t) ⟨s, ⟨hsG, hts⟩, rfl⟩
  exact h1.trans h2

/-- **Antitone profiles coincide with their envelope.** -/
theorem eq_rightProfile_of_antitone {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hlsc : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ G, t < s → s < t + δ → f t ≤ f s + ε)
    (hbdd : BddAbove (f '' G)) (hf : Antitone f) :
    ∀ t, f t = rightProfile f G t := by
  intro t
  refine le_antisymm (le_rightProfile hG hlsc hbdd t) ?_
  apply csSup_le (rightProfile_nonempty hG t)
  rintro _ ⟨s, ⟨-, hts⟩, rfl⟩
  exact hf hts.le

/-- **A profile equal to its envelope is antitone.** -/
theorem antitone_of_eq_rightProfile {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hbdd : BddAbove (f '' G)) (hf : ∀ t, f t = rightProfile f G t) :
    Antitone f := by
  have : f = rightProfile f G := funext hf
  rw [this]
  exact rightProfile_antitone hG hbdd

/-- **Full monotonicity of `Φ` ⟺ `Φ = Ψ`.**  Under right-density of `G`,
right-lsc along `G` and boundedness (the strong energy inequality is not
needed for this equivalence), `f` is antitone on all of `ℝ` iff it coincides with its
right-limit envelope along `G` — i.e. iff every time behaves as a good
time.  For Leray–Hopf solutions this is open; for Galerkin flows it holds
trivially. -/
theorem antitone_iff_eq_rightProfile {f : ℝ → ℝ} {G : Set ℝ}
    (hG : ∀ t δ : ℝ, 0 < δ → ∃ s ∈ G, t < s ∧ s < t + δ)
    (hlsc : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ G, t < s → s < t + δ → f t ≤ f s + ε)
    (hbdd : BddAbove (f '' G)) :
    Antitone f ↔ ∀ t, f t = rightProfile f G t := by
  exact ⟨eq_rightProfile_of_antitone hG hlsc hbdd,
    antitone_of_eq_rightProfile hG hbdd⟩

/-- **One singular time: the defect is the jump between plateaus.**  If
`f a = L` (left plateau value; the plateau `f = L` on `(a, tstar)` itself is
not needed), `f = R` on `(tstar, b]`, and the Leray–Hopf ordering
`f tstar ≤ R ≤ L` holds (`E(T*) ≤ E⁺(T*) ≤ E⁻(T*)`: weak lower
semicontinuity puts the value *at* the singular time below the right
plateau, `Ψ(T*) = R`; a strict inequality `f tstar < R` is the "dip" of a
bad singular time), then the defect over `[a, b]` is `L − R ≥ 0`, and the
defect over `[a, tstar]` is `L − f tstar ≥ L − R`: the window ending at
the singular time sees the whole jump and possibly more (the dip), the
window straddling it sees exactly the jump.  Pure algebra. -/
theorem defect_eq_jump_single_singular_time (f : ℝ → ℝ) (a tstar b L R : ℝ)
    (htb : tstar < b) (hR : ∀ s, tstar < s → s ≤ b → f s = R) (haL : f a = L)
    (hdip : f tstar ≤ R) (hRL : R ≤ L) :
    f a - f b = L - R ∧ 0 ≤ L - R ∧
      f a - f b = (f a - f tstar) + (f tstar - f b) ∧
      L - R ≤ f a - f tstar ∧ f tstar - f b ≤ 0 := by
  have hb : f b = R := hR b htb le_rfl
  rw [haL, hb]
  refine ⟨rfl, by linarith, by ring, by linarith, by linarith⟩

/-- **Small covers exclude a jump (Leslie–Shvydkoy skeleton).**  Suppose
that for every `ε > 0` the quantity `m` decomposes below `Tstar` as
`m = A + B`, where `A ≤ Cε` eventually as `t ↑ Tstar` (the contribution of an
`ε`-cover of the singular slice, controlled by a Morrey-type bound) and
`B → mstar` (the regular remainder).  Then `m t ≤ mstar + ε'` eventually as
`t ↑ Tstar` for every `ε' > 0`: no positive jump above `mstar` survives. -/
theorem no_jump_of_small_covers (m : ℝ → ℝ) (mstar Tstar C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ A B : ℝ → ℝ, (∀ t, t < Tstar → m t = A t + B t) ∧
      (∀ᶠ t in 𝓝[<] Tstar, A t ≤ C * ε) ∧ Tendsto B (𝓝[<] Tstar) (𝓝 mstar)) :
    ∀ ε' > 0, ∀ᶠ t in 𝓝[<] Tstar, m t ≤ mstar + ε' := by
  intro ε' hε'
  have hC1 : 0 < C + 1 := by linarith
  set ε : ℝ := ε' / (2 * (C + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hCε : C * ε ≤ ε' / 2 := by
    rw [hε_def, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨A, B, hid, hA, hB⟩ := h ε hε
  have hBev : ∀ᶠ t in 𝓝[<] Tstar, B t < mstar + ε' / 2 :=
    hB.eventually_lt_const (by linarith)
  have hlt : ∀ᶠ t in 𝓝[<] Tstar, t < Tstar := self_mem_nhdsWithin
  filter_upwards [hA, hBev, hlt] with t hAt hBt htT
  rw [hid t htT]
  linarith

end EnergyDefect
