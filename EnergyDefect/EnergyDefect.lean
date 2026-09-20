/-
# The energy-defect form of Gap 2: averaged tail floors ⟺ dissipation anomaly

Target (i) of the 2026-09-02 handoff: the one open input of
`ensemble_supercritical_exit` is uniform mean positivity of the band
fluxes.  Asking what the *averaged* flux equals for a Leray–Hopf solution
gives an exact identity that recasts the whole averaged form of Gap 2.

**The identity (PDE input, hypothesis here).**  With
`Π_j := ⟨P_{≤j}u, P(u·∇u)⟩` (energy leaving the shells `≤ j`; this is the
solver's convention and the sign forced by the balance law
`d/dt E_{≤j} = −Π_j − ν‖∇P_{≤j}u‖²`), for every Leray–Hopf weak solution
and every window `[w₀, w]`:

    ∫_{w₀}^{w} Π_j dt = E_{≤j}(w₀) − E_{≤j}(w) − ν∫_{w₀}^{w} ‖∇P_{≤j}u‖² dt .

(Finite-dimensional projection of the weak formulation; `P_{≤j}u` is
smooth in time.)  Letting `j → ∞` — Parseval for the shell energies,
monotone convergence for the shell dissipation, both proven below in
abstract form — gives

    lim_{j→∞} ∫_{w₀}^{w} Π_j dt = E(w₀) − E(w) − ν∫_{w₀}^{w}‖∇u‖² dt =: 𝒜(w₀,w),

the **energy defect** of the window.  Strong solutions have `𝒜 = 0`
(energy equality).

**Consequences (proven here, abstract).**
* `averaged_tail_floor_le_defect` — uniform averaged floors on the tail
  force `𝒜 ≥ B·ℓ > 0`: the averaged form of Gap 2 implies a strict energy
  inequality on the window, hence the solution is not strong there.  No
  paraproduct bound, no ceiling.
* `energy_equality_no_averaged_tail_floor` — contrapositive: energy
  equality on the window excludes every uniform averaged tail floor.
* `defect_gives_averaged_tail_floor` — conversely a positive defect yields
  averaged floors `≥ B·ℓ` for every `B < 𝒜/ℓ` on some tail `j ≥ j₀`.
  **The averaged form of Gap 2 is equivalent to a positive energy defect
  on some window.**
* `pointwise_floor_implies_averaged` — the pointwise Gap 2 implies the
  averaged one, hence the defect: pointwise floors on `j ≥ j₀` already
  break energy equality.
* `shell_partial_sums_tendsto` — Parseval along any monotone exhausting
  shell filtration (the `E_{≤j}(t) → E(t)` step).
* `shell_dissipation_tendsto` — monotone convergence for the shell
  dissipation integrals (the `ν∫‖∇P_{≤j}u‖² → ν∫‖∇u‖²` step).
* `extremal_defect_exists` — the entropy principle in its well-posed
  defect form: an upper semicontinuous defect functional attains its
  maximum on a compact set of solutions; the paper's "entropy production
  maximizing solution" is a *defect maximizer*.

Epistemic status: theorems are elementary (Lean-verified).  The identity
and the semicontinuity of the defect are PDE inputs recorded as
hypotheses; see `research/routes/ENERGY_DEFECT.md`.
-/
import EnergyDefect.ErgodicFusion
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.Filter.AtTopBot.Finset

namespace EnergyDefect

open Filter Topology MeasureTheory intervalIntegral

/-- **Parseval along a shell filtration.**  If the modal energies `e k`
sum (unconditionally) to `E`, and `S j` is a monotone exhausting sequence
of finite shell sets, then the shell partial sums `Σ_{k ∈ S j} e k` tend
to `E`.  This is `E_{≤j}(t) → E(t)`. -/
theorem shell_partial_sums_tendsto {ι : Type*} {e : ι → ℝ} {E : ℝ}
    (he : HasSum e E) {S : ℕ → Finset ι} (hmono : Monotone S)
    (hexh : ∀ k, ∃ j, k ∈ S j) :
    Tendsto (fun j => ∑ k ∈ S j, e k) atTop (𝓝 E) :=
  he.comp (tendsto_atTop_finset_of_monotone hmono hexh)

/-- **Monotone convergence for the shell dissipation.**  If the shell
dissipation densities `d j t` increase in `j` to `D t` a.e. on the window,
with `D` integrable, then `∫ d j → ∫ D`.  This is
`ν∫‖∇P_{≤j}u‖² dt → ν∫‖∇u‖² dt`. -/
theorem shell_dissipation_tendsto {d : ℕ → ℝ → ℝ} {D : ℝ → ℝ} {w₀ w : ℝ}
    (hint : ∀ j, IntegrableOn (d j) (Set.Ioc w₀ w))
    (hD : IntegrableOn D (Set.Ioc w₀ w))
    (hmono : ∀ᵐ t ∂(volume.restrict (Set.Ioc w₀ w)), Monotone fun j => d j t)
    (hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioc w₀ w)),
      Tendsto (fun j => d j t) atTop (𝓝 (D t))) :
    Tendsto (fun j => ∫ t in Set.Ioc w₀ w, d j t) atTop
      (𝓝 (∫ t in Set.Ioc w₀ w, D t)) :=
  integral_tendsto_of_tendsto_of_monotone hint hD hmono hlim

/-- **The flux limit is the energy defect.**  Given the shell identity
`F j = Elo j − Ehi j − Dsh j` (integrated flux = low-mode energy drop
minus low-mode dissipation) and the three convergences, the averaged
fluxes converge to `𝒜 = E₀ − E₁ − D`. -/
theorem flux_tendsto_defect {F Elo Ehi Dsh : ℕ → ℝ} {E₀ E₁ D : ℝ}
    (hid : ∀ j, F j = Elo j - Ehi j - Dsh j)
    (h₀ : Tendsto Elo atTop (𝓝 E₀)) (h₁ : Tendsto Ehi atTop (𝓝 E₁))
    (hD : Tendsto Dsh atTop (𝓝 D)) :
    Tendsto F atTop (𝓝 (E₀ - E₁ - D)) := by
  have : F = fun j => Elo j - Ehi j - Dsh j := funext hid
  rw [this]
  exact (h₀.sub h₁).sub hD

/-- **Averaged tail floors force a positive defect.**  If the averaged
fluxes converge to the defect `𝒜` and satisfy `F j ≥ β` for all `j ≥ j₀`,
then `𝒜 ≥ β`.  With `β = B·ℓ > 0`: the averaged Gap 2 implies a strict
energy inequality on the window — the solution is not strong there. -/
theorem averaged_tail_floor_le_defect {F : ℕ → ℝ} {𝒜 β : ℝ} {j₀ : ℕ}
    (hlim : Tendsto F atTop (𝓝 𝒜))
    (hfloor : ∀ j, j₀ ≤ j → β ≤ F j) : β ≤ 𝒜 :=
  ge_of_tendsto hlim (eventually_atTop.mpr ⟨j₀, hfloor⟩)

/-- **Energy equality excludes averaged tail floors.**  If the defect
vanishes (`𝒜 = 0`, energy equality on the window), no positive uniform
averaged floor holds on any tail. -/
theorem energy_equality_no_averaged_tail_floor {F : ℕ → ℝ}
    (hlim : Tendsto F atTop (𝓝 0)) :
    ¬ ∃ β > 0, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → β ≤ F j := by
  rintro ⟨β, hβ, j₀, hfloor⟩
  have := averaged_tail_floor_le_defect hlim hfloor
  linarith

/-- **A positive defect gives averaged tail floors.**  If `𝒜 > 0` then for
every `β < 𝒜` there is `j₀` with `F j ≥ β` for all `j ≥ j₀`: the averaged
form of Gap 2 holds on the tail with any floor below `𝒜/ℓ`. -/
theorem defect_gives_averaged_tail_floor {F : ℕ → ℝ} {𝒜 β : ℝ}
    (hlim : Tendsto F atTop (𝓝 𝒜)) (hβ : β < 𝒜) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → β ≤ F j := by
  have h := hlim.eventually_const_lt hβ
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp h
  exact ⟨j₀, fun j hj => (hj₀ j hj).le⟩

/-- **Pointwise floors imply averaged floors.**  A pointwise floor
`B ≤ Π_j(t)` on `[w₀, w]` integrates to `B·(w − w₀) ≤ ∫ Π_j`. -/
theorem pointwise_floor_implies_averaged {Pi : ℝ → ℝ} {B w₀ w : ℝ}
    (hI : w₀ ≤ w) (hint : IntervalIntegrable Pi volume w₀ w)
    (hfloor : ∀ t ∈ Set.Icc w₀ w, B ≤ Pi t) :
    B * (w - w₀) ≤ ∫ t in w₀..w, Pi t := by
  have h := integral_mono_on hI intervalIntegrable_const hint hfloor
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h
  exact h

/-- **Pointwise Gap 2 forces a positive defect (composition).**  Pointwise
floors `B ≤ Π_j(t)` on the window for all `j ≥ j₀`, the shell identity,
and the three convergences give `B·(w − w₀) ≤ 𝒜`: the pointwise Gap 2
breaks energy equality with no paraproduct bound and no ceiling. -/
theorem pointwise_tail_floor_le_defect {Pi : ℕ → ℝ → ℝ}
    {Elo Ehi Dsh : ℕ → ℝ} {E₀ E₁ D B w₀ w : ℝ} {j₀ : ℕ}
    (hI : w₀ ≤ w)
    (hint : ∀ j, IntervalIntegrable (Pi j) volume w₀ w)
    (hfloor : ∀ j, j₀ ≤ j → ∀ t ∈ Set.Icc w₀ w, B ≤ Pi j t)
    (hid : ∀ j, (∫ t in w₀..w, Pi j t) = Elo j - Ehi j - Dsh j)
    (h₀ : Tendsto Elo atTop (𝓝 E₀)) (h₁ : Tendsto Ehi atTop (𝓝 E₁))
    (hD : Tendsto Dsh atTop (𝓝 D)) :
    B * (w - w₀) ≤ E₀ - E₁ - D := by
  have hlim : Tendsto (fun j => ∫ t in w₀..w, Pi j t) atTop
      (𝓝 (E₀ - E₁ - D)) := flux_tendsto_defect hid h₀ h₁ hD
  refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨j₀, fun j hj => ?_⟩)
  exact pointwise_floor_implies_averaged hI (hint j) (hfloor j hj)

/-- **The entropy principle as defect maximization (well-posed).**  On a
nonempty compact set `S` of solutions (e.g. the Leray–Hopf solutions with
prescribed data, weakly compact), an upper semicontinuous defect
functional `𝒜` attains its maximum: there is a *defect-maximizing*
solution.  (`𝒜 = E(w₀) − E(w) − ν∫‖∇u‖²` is upper semicontinuous under
weak convergence: `E(w)` and the dissipation are weakly lower
semicontinuous — PDE input, hypothesis here.)  Either the maximum is `0`
— every solution with this data satisfies energy equality on the window,
and no averaged Gap 2 holds for any of them — or it is positive, and the
maximizer realizes the averaged Gap 2. -/
theorem extremal_defect_exists {X : Type*} [TopologicalSpace X]
    {S : Set X} (hne : S.Nonempty) (hS : IsCompact S)
    {𝒜 : X → ℝ} (husc : UpperSemicontinuousOn 𝒜 S) :
    ∃ u ∈ S, ∀ v ∈ S, 𝒜 v ≤ 𝒜 u := by
  obtain ⟨u, hu, hmax⟩ := husc.exists_isMaxOn hne hS
  exact ⟨u, hu, fun v hv => hmax hv⟩

/-- **The defect dichotomy.**  For a defect maximizer `u*` over `S`: either
`𝒜 u* ≤ 0` and then every solution in `S` has nonpositive defect (energy
equality for all, given the energy inequality `𝒜 ≥ 0`), or `𝒜 u* > 0` and
the maximizer carries averaged tail floors at every level `β < 𝒜 u*`. -/
theorem defect_dichotomy {X : Type*} {S : Set X} {𝒜 : X → ℝ} {u : X}
    (hmax : ∀ v ∈ S, 𝒜 v ≤ 𝒜 u) {F : X → ℕ → ℝ}
    (hlim : ∀ v, Tendsto (F v) atTop (𝓝 (𝒜 v))) :
    (∀ v ∈ S, 𝒜 v ≤ 0) ∨
    (0 < 𝒜 u ∧ ∀ β < 𝒜 u, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → β ≤ F u j) := by
  by_cases h : 𝒜 u ≤ 0
  · exact Or.inl fun v hv => (hmax v hv).trans h
  · push Not at h
    exact Or.inr ⟨h, fun β hβ => defect_gives_averaged_tail_floor (hlim u) hβ⟩

end EnergyDefect
