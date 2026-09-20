/-
# Sharpening the reduced hypothesis (research/sharpening, Track A)

Open 1 of the reduction paper: a Leray–Hopf solution from `C^∞` data with
energy defect `𝒜(w₀,w) > 0` on a finite window.  Three necessary /
structural consequences, abstract and Lean-verified; PDE inputs are
hypotheses.  Notation: `F j = ∫_{w₀}^{w} Π_j dt` (window-integrated flux
through shell `j`), `Dhi j = ν∫‖∇P_{>j}u‖²` (dissipation above `j`),
`𝒜` the defect.

* `defect_le_limsup_cubic` (A2) — if the integrated flux is bounded by a
  cubic Onsager quantity, `F j ≤ C · G j` (CCFS-type flux estimate with
  `G j ~ ∫ 2^j a_j³`, constant from the literature), and `F j → 𝒜 > 0`,
  then `G j ≥ (𝒜 − ε)/C` for all large `j`: **the Onsager-critical cubic
  sum does not vanish along the tail.**  A checkable necessary condition.
* `deep_flux_exceeds_dissipation` (A3) — `F j − Dhi j → 𝒜`, so for a
  defective solution `F j ≥ Dhi j + 𝒜/2` for all large `j`: **at deep
  shells the cascade current exceeds the viscous dissipation above them by
  a fixed amount** — viscosity does not absorb the deep flux.
* `family_defect_of_uniform_inertial_floors` (A5) — the bridge from the
  ν → 0 family statement to a defect: if for each `ν` the floors hold on
  `j ≤ J ν` with `J ν → ∞`, and `F ν j → F₀ j` as `ν → 0` for each `j`,
  then `F₀ j ≥ B` for every `j`, hence the limit's defect `𝒜₀ = lim_j F₀ j`
  is `≥ B`.  **The family statement yields anomalous dissipation of the
  limit, not a fixed-ν defect.**  Separation of Open 1 from Open 3.
-/
import EnergyDefect.StationaryFlux

namespace EnergyDefect

open Filter Topology

/-- **A2: the Onsager cubic sum is bounded below by the defect.**  With
`F j ≤ C · G j` (`C > 0`) and `F j → 𝒜`, for every `ε > 0` eventually
`(𝒜 − ε)/C ≤ G j`. -/
theorem defect_le_limsup_cubic {F G : ℕ → ℝ} {C 𝒜 : ℝ} (hC : 0 < C)
    (hbound : ∀ j, F j ≤ C * G j) (hlim : Tendsto F atTop (𝓝 𝒜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → (𝒜 - ε) / C ≤ G j := by
  have h := hlim.eventually_const_lt (by linarith : 𝒜 - ε < 𝒜)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp h
  refine ⟨j₀, fun j hj => ?_⟩
  have h1 : 𝒜 - ε < C * G j := lt_of_lt_of_le (hj₀ j hj) (hbound j)
  rw [div_le_iff₀ hC]
  linarith

/-- **A3: the deep flux exceeds the deep dissipation by the defect.**  If
`F j − Dhi j → 𝒜 > 0`, then eventually `Dhi j + 𝒜/2 ≤ F j`. -/
theorem deep_flux_exceeds_dissipation {F Dhi : ℕ → ℝ} {𝒜 : ℝ} (h𝒜 : 0 < 𝒜)
    (hlim : Tendsto (fun j => F j - Dhi j) atTop (𝓝 𝒜)) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → Dhi j + 𝒜 / 2 ≤ F j := by
  have h := hlim.eventually_const_lt (by linarith : 𝒜 / 2 < 𝒜)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp h
  exact ⟨j₀, fun j hj => by linarith [hj₀ j hj]⟩

/-- **A5: uniform inertial floors along the family give a defect of the
limit.**  Let `F ν j` be the integrated flux at viscosity `ν` (indexed by
`n : ℕ` along a sequence `ν_n → 0`), with floors `B ≤ F n j` for all
`j ≤ J n`, `J n → ∞`, and `F n j → F₀ j` as `n → ∞` for each `j`.  Then
`B ≤ F₀ j` for every `j`; if moreover `F₀ j → 𝒜₀` then `B ≤ 𝒜₀`: the
limit has energy defect at least `B`. -/
theorem family_defect_of_uniform_inertial_floors {F : ℕ → ℕ → ℝ}
    {F₀ : ℕ → ℝ} {J : ℕ → ℕ} {B 𝒜₀ : ℝ}
    (hJ : Tendsto J atTop atTop)
    (hfloor : ∀ n j, j ≤ J n → B ≤ F n j)
    (hconv : ∀ j, Tendsto (fun n => F n j) atTop (𝓝 (F₀ j)))
    (hlim : Tendsto F₀ atTop (𝓝 𝒜₀)) :
    (∀ j, B ≤ F₀ j) ∧ B ≤ 𝒜₀ := by
  have hj : ∀ j, B ≤ F₀ j := by
    intro j
    have hev : ∀ᶠ n in atTop, B ≤ F n j := by
      have := hJ.eventually_ge_atTop j
      filter_upwards [this] with n hn
      exact hfloor n j hn
    exact ge_of_tendsto (hconv j) hev
  exact ⟨hj, ge_of_tendsto hlim (Eventually.of_forall hj)⟩

end EnergyDefect
