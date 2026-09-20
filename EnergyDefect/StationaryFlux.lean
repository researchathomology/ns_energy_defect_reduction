/-
# The forced / stationary setting: mean flux = input − low-mode dissipation

Execution of the "move to the setting where statistical objects exist"
step.  On unforced `𝕋³` the only invariant measure is `δ₀`; with a force
`f` supported in the shells `≤ j_f` (deterministic, or white in time with
covariance `Q` — then the mean energy input is the Itô constant
`I = ½ tr Q`, an identity, not an estimate), a stationary statistical
solution `μ` obeys, for every `j ≥ j_f`, the exact mean shell balance

    ∫ Π_j dμ  =  I − ν ∫ ‖∇P_{≤j}u‖² dμ  =  D_{>j} + 𝒜_μ ,

where `D_{≤j} := ν∫‖∇P_{≤j}u‖² dμ ↑ D_tot := ν∫‖∇u‖² dμ ≤ I`, the mean
defect is `𝒜_μ := I − D_tot ≥ 0`, and `D_{>j} := D_tot − D_{≤j} ↓ 0`
(PDE input, hypotheses here).  Consequences, proven abstractly:

* `stationary_mean_flux_ge_defect`, `stationary_mean_flux_tendsto_defect`
  — every mean flux sits above the defect and converges to it: at fixed
  `ν`, **uniform-in-`j` mean floors ⟺ `𝒜_μ > 0`** (the same identification
  as in the unforced window form, `EnergyDefect.lean`).
* `stationary_mean_flux_positive` — for each fixed `j` the mean flux is
  positive as soon as some dissipation occurs above shell `j`: mean
  positivity for *finitely many* shells is free in the forced stationary
  setting.  The content of Gap 2 is the uniformity, exactly as before.
* `floors_force_dissipation_above` — for a zero-defect flow, a floor `B`
  on the shells `j₀ ≤ j ≤ J` forces `D_{>J} ≥ B`: **flux floors on a tower
  require dissipation of at least `B` above the tower.**  This is the
  quantitative statement behind the campaign's `ρ = 3/4` and behind what
  separates the dyadic model (dissipation concentrated at the top shell)
  from Navier–Stokes (dissipation spread over the range around `k_η`).
* `inertial_floors_of_uniform_energy_bound`,
  `inertial_range_deepens` — the `ν`-family form (R5 variant (c)): if the
  low-mode mean dissipation obeys the Bernstein bound
  `D_{≤j}(ν) ≤ ν 4^{j+1} M` with `M` a `ν`-uniform bound on the mean
  energy, then `∫Π_j dμ_ν ≥ I/2` for all `j ≤ J(ν)` with `J(ν) → ∞`.
  **In the white-noise-forced setting, mean flux floors on an inertial
  range of unbounded depth follow from a `ν`-uniform mean-energy bound**
  — the standing open estimate of the stochastic 3D theory — but only as
  `ν → 0`, never as an infinite tower at fixed `ν`.

Epistemic status: elementary arithmetic (Lean-verified) on top of the
stationary shell balance (PDE input, standard; recorded as hypothesis).
Analysis and literature labels: `research/routes/FORCED_STATIONARY.md`.
-/
import EnergyDefect.EnergyDefect

namespace EnergyDefect

open Filter Topology

/-- **Mean flux dominates the defect.**  With `F j = I − Dlo j` and
`Dlo j ≤ Dtot`, every mean shell flux is at least the mean defect
`𝒜 = I − Dtot`. -/
theorem stationary_mean_flux_ge_defect {F Dlo : ℕ → ℝ} {I Dtot : ℝ}
    (hid : ∀ j, F j = I - Dlo j) (hle : ∀ j, Dlo j ≤ Dtot) (j : ℕ) :
    I - Dtot ≤ F j := by
  rw [hid j]; linarith [hle j]

/-- **Mean flux converges to the defect.**  If the low-mode dissipation
`Dlo j → Dtot`, then `F j = I − Dlo j → I − Dtot = 𝒜`.  Hence
uniform-in-`j` mean floors at fixed `ν` are equivalent to `𝒜 > 0`
(`averaged_tail_floor_le_defect`, `defect_gives_averaged_tail_floor`). -/
theorem stationary_mean_flux_tendsto_defect {F Dlo : ℕ → ℝ} {I Dtot : ℝ}
    (hid : ∀ j, F j = I - Dlo j) (hD : Tendsto Dlo atTop (𝓝 Dtot)) :
    Tendsto F atTop (𝓝 (I - Dtot)) := by
  have : F = fun j => I - Dlo j := funext hid
  rw [this]
  exact tendsto_const_nhds.sub hD

/-- **Per-shell mean positivity is free.**  With nonnegative defect and
some dissipation above shell `j` (`Dlo j < Dtot`), the mean flux through
shell `j` is strictly positive.  Finitely many mean floors cost nothing
in the forced stationary setting; the uniformity is the content. -/
theorem stationary_mean_flux_positive {F Dlo : ℕ → ℝ} {I Dtot : ℝ}
    (hid : ∀ j, F j = I - Dlo j) (hA : 0 ≤ I - Dtot) {j : ℕ}
    (hj : Dlo j < Dtot) : 0 < F j := by
  rw [hid j]; linarith

/-- **Floors force dissipation above the tower.**  For a zero-defect flow
(`I = Dtot`), a floor `B ≤ F j` on the shells `j₀ ≤ j ≤ J` forces the dissipation above shell `J` to be
at least `B`:
`B ≤ Dtot − Dlo J`.  Uniform floors on a tower need the dissipation to
sit above the tower — a delta at the top shell realizes them uniformly
(dyadic model), a dissipation range spread over octaves does not. -/
theorem floors_force_dissipation_above {F Dlo : ℕ → ℝ} {I Dtot B : ℝ}
    {j₀ J : ℕ}
    (hid : ∀ j, F j = I - Dlo j) (hzero : I = Dtot) (hj₀J : j₀ ≤ J)
    (hfloor : ∀ j, j₀ ≤ j → j ≤ J → B ≤ F j) :
    B ≤ Dtot - Dlo J := by
  have h := hfloor J hj₀J le_rfl
  rw [hid J, hzero] at h
  exact h

/-- **Inertial-range mean floors from a `ν`-uniform energy bound (R5
variant (c), stochastic form).**  If the low-mode mean dissipation obeys
`Dlo ν j ≤ ν · 4^(j+1) · M` (Bernstein on the shells `≤ j`, `M` a bound on
the mean energy uniform in `ν`), then on every shell with
`ν · 4^(j+1) · M ≤ I/2` the mean flux is at least `I/2`. -/
theorem inertial_floors_of_uniform_energy_bound {F Dlo : ℝ → ℕ → ℝ}
    {I M : ℝ}
    (hid : ∀ ν j, F ν j = I - Dlo ν j)
    (hbern : ∀ ν j, Dlo ν j ≤ ν * 4 ^ (j + 1) * M)
    {ν : ℝ} {j : ℕ} (hj : ν * 4 ^ (j + 1) * M ≤ I / 2) :
    I / 2 ≤ F ν j := by
  rw [hid ν j]
  linarith [hbern ν j]

/-- **The inertial range deepens without bound as `ν → 0`.**  For every
depth `J` there is `ν₀ > 0` such that for all `0 < ν ≤ ν₀` every shell
`j ≤ J` satisfies the floor condition `ν · 4^(j+1) · M ≤ I/2`.  Together
with the previous theorem: mean floors `≥ I/2` hold on `j ≤ J` for all
sufficiently small `ν` — a statement about the family `ν → 0`, not about
an infinite tower at fixed `ν`. -/
theorem inertial_range_deepens {I M : ℝ} (hI : 0 < I) (hM : 0 < M) (J : ℕ) :
    ∃ ν₀ > 0, ∀ ν, 0 < ν → ν ≤ ν₀ → ∀ j ≤ J,
      ν * 4 ^ (j + 1) * M ≤ I / 2 := by
  refine ⟨I / 2 / (4 ^ (J + 1) * M), by positivity, fun ν hν hν₀ j hj => ?_⟩
  have h4 : (4:ℝ) ^ (j + 1) ≤ 4 ^ (J + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpos : (0:ℝ) < 4 ^ (J + 1) * M := by positivity
  have h1 : ν * (4 ^ (J + 1) * M) ≤ I / 2 := by
    rwa [le_div_iff₀ hpos] at hν₀
  calc ν * 4 ^ (j + 1) * M = ν * (4 ^ (j + 1) * M) := by ring
    _ ≤ ν * (4 ^ (J + 1) * M) := by
        apply mul_le_mul_of_nonneg_left _ hν.le
        exact mul_le_mul_of_nonneg_right h4 hM.le
    _ ≤ I / 2 := h1

end EnergyDefect
