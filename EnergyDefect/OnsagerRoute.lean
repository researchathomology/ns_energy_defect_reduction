/-
# Route R5: shell-uniform flux persistence — the Onsager-side core

Rigorous abstract half of route R5 (see `research/F3/TARGET.md` R5 and
`research/experiments/dyadic/front_probe.py` for the empirical basis).

Setting: dyadic frequency bands `j = 0, 1, 2, …` with amplitudes
`a j ≥ 0` (Littlewood–Paley piece norms `‖Δ_j u‖`), band energy fluxes
`Π j`, and the single-shell flux bound `Π j ≤ c · 2^j · (a j)³`.
**Status of that bound (corrected 2026-09-04):** with `a j` the `L²` norm
of the shell it is *not* a theorem of the Navier–Stokes equation; it is the
Kolmogorov-phenomenological locality assumption (flux through a shell
controlled by that shell alone). The rigorous Cheskidov–Constantin–
Friedlander–Shvydkoy bound controls `Π j` by a weighted sum of `L³` norms
of the *neighbouring* shells. The bound is therefore a modelling
hypothesis of the theorems below, kept explicit, never asserted.

Proven here:

* `onsager_amplitude_floor` — a uniform flux floor `B ≤ Π j` forces the
  amplitudes to sit **above the Onsager-critical profile**:
  `a j ≥ (B/c)^{1/3} · 2^{-j/3}`.
* `supercritical_sums_unbounded_of_flux_floor` — consequently every
  super-critical weighted square sum `Σ_j (2^j)^{2s} (a j)²` with
  `s ≥ 1/3` exceeds any bound as more bands are included: the solution
  has no `H^{s}` (s > 1/3) bound on the window where the floors hold.
  Combined with the windowed engine, the epoch of regularity ends inside
  the window.

Together with `uniform_band_floor_defeats_bound` (HardyRoute.lean) this
completes the machine-checked chain of R5:

  uniform band-flux floors on a window
    ⇒ amplitudes ≥ Onsager profile           (here)
    ⇒ all H^{s>1/3} partial sums diverge      (here)
    ⇒ no regular solution carries the floors  (engine)
-/
import EnergyDefect.Interface
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EnergyDefect

open Real Finset

/-- **Onsager amplitude floor (proven).**  If the band flux obeys the
trilinear estimate `Π j ≤ c·2^j·(a j)³` and the uniform floor `B ≤ Π j`,
then the band amplitude sits above the Onsager-critical profile:
`(B/c)^{1/3} · (2^j)^{-1/3} ≤ a j`. -/
theorem onsager_amplitude_floor {a Pi : ℕ → ℝ} {B c : ℝ}
    (hB : 0 < B) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (hfloor : ∀ j, B ≤ Pi j)
    (htri : ∀ j, Pi j ≤ c * 2 ^ j * a j ^ 3) (j : ℕ) :
    (B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3) ≤ a j := by
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have hcube : B / (c * 2 ^ j) ≤ a j ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    calc B ≤ Pi j := hfloor j
      _ ≤ c * 2 ^ j * a j ^ 3 := htri j
      _ = a j ^ 3 * (c * 2 ^ j) := by ring
  have hr : (0:ℝ) < B / (c * 2 ^ j) := by positivity
  have h1 : (B / (c * 2 ^ j)) ^ ((1:ℝ)/3) ≤ (a j ^ 3 : ℝ) ^ ((1:ℝ)/3) :=
    Real.rpow_le_rpow hr.le hcube (by norm_num)
  have h2 : (a j ^ 3 : ℝ) ^ ((1:ℝ)/3) = a j := by
    rw [← Real.rpow_natCast (a j) 3, ← Real.rpow_mul (ha j)]
    norm_num
  have h3 : (B / (c * 2 ^ j)) ^ ((1:ℝ)/3)
      = (B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3) := by
    rw [neg_div, Real.rpow_neg h2j.le, ← div_eq_mul_inv,
      ← Real.div_rpow (by positivity) h2j.le, div_div]
  rw [← h2, ← h3]
  exact h1

/-- **Super-critical norms diverge under uniform flux floors (proven).**
Under the hypotheses of `onsager_amplitude_floor`, for every regularity
exponent `s ≥ 1/3` and every threshold `M` there are finitely many bands
whose weighted square sum `Σ_{j<J} (2^j)^{2s} (a j)²` already exceeds `M`:
no `H^{s}`-type bound survives on the window carrying the floors. -/
theorem supercritical_sums_unbounded_of_flux_floor {a Pi : ℕ → ℝ}
    {B c s : ℝ} (hB : 0 < B) (hc : 0 < c) (hs : (1:ℝ)/3 ≤ s)
    (ha : ∀ j, 0 ≤ a j) (hfloor : ∀ j, B ≤ Pi j)
    (htri : ∀ j, Pi j ≤ c * 2 ^ j * a j ^ 3) (M : ℝ) :
    ∃ J : ℕ, M ≤ ∑ j ∈ range J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
  set b₀ : ℝ := ((B / c) ^ ((1:ℝ)/3)) ^ 2 with hb₀
  have hb₀pos : 0 < b₀ := by positivity
  have hterm : ∀ j, b₀ ≤ ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    intro j
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h2j1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hA := onsager_amplitude_floor hB hc ha hfloor htri j
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
  obtain ⟨J, hJ⟩ := exists_nat_ge (M / b₀)
  refine ⟨J, ?_⟩
  have h1 : (J : ℝ) * b₀ ≤ ∑ j ∈ range J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    calc (J : ℝ) * b₀ = ∑ _j ∈ range J, b₀ := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j
  have h2 : M ≤ (J : ℝ) * b₀ := by
    rw [div_le_iff₀ hb₀pos] at hJ
    linarith
  linarith

end EnergyDefect
