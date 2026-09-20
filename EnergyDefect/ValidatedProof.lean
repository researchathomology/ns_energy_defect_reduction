/-
# The computation-to-analysis bridge (validated / computer-assisted proofs)

The program's standing requirement: **numerics locate the example; the
proof must be analytic.**  This file supplies the bridge — the theorems
that convert a *finite, rigorously enclosed* computation into the
hypotheses of the verified blowup chain, in the tradition of validated
computer-assisted proofs (Tucker's Lorenz attractor; Arioli–Koch;
Gómez-Serrano's survey; the Chen–Hou blowup verification).

The pipeline (`research/routes/VALIDATED_PROOF.md`):

  (1) analytic initial datum (closed-form trigonometric polynomial — the
      knot/link family already constructed);
  (2) interval-validated integration of the Galerkin system + a-posteriori
      defect control ⇒ an enclosure `|ν_t − ν̃_t| ≤ ε` of the true
      fluctuation around the computed one (`aposteriori_gronwall` gives
      the growth law of the enclosure);
  (3) finite verification: floors `B ≤ ν̃_t` checked on the window by
      interval arithmetic — finitely many conditions;
  (4) ONE remaining theory estimate: the ceiling constant `C`
      (Hardy/Gevrey, from the data norms — open item C2);
  (5) the master theorem below turns (2)+(3)+(4) into the analytic
      conclusion: the epoch of regularity ends inside the window.

Proven here:

* `amplitude_floor_single` — single-band Onsager floor (hypotheses at one
  `j` only: the finitely-verifiable form).
* `effective_band_count` — **effective finite-band sufficiency**: to push
  the `H^s` sum above a given bound `M`, floors on the *explicitly many*
  bands `J ≥ M/b₀`, `b₀ = ((B/c)^{1/3})²`, suffice — a finite computation
  defeats any *given* regularity bound.
* `validated_epoch_ends_inside` — **the CAP master theorem**: enclosure +
  finite floor verification with margin + theory ceiling + a finite
  margin check imply the epoch ends inside the window.  Every hypothesis
  except the ceiling constant is checkable by finite interval arithmetic.
* `aposteriori_gronwall` — the enclosure growth law: defect `δ` and
  one-sided Lipschitz bound `K` give `‖u−ũ‖ ≤ gronwallBound 0 K δ (t−a)`
  (wrapping Mathlib's Grönwall; equals `(δ/K)(e^{K(t−a)}−1)`).
-/
import EnergyDefect.HardyRoute
import EnergyDefect.OnsagerRoute
import Mathlib.Analysis.ODE.Gronwall

namespace EnergyDefect

open Real Finset

/-- **Single-band amplitude floor** — the finitely-verifiable form of
`onsager_amplitude_floor`: hypotheses at one band only. -/
theorem amplitude_floor_single {B c a Pi : ℝ} (j : ℕ)
    (hB : 0 < B) (hc : 0 < c) (ha : 0 ≤ a)
    (hfloor : B ≤ Pi) (htri : Pi ≤ c * 2 ^ j * a ^ 3) :
    (B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3) ≤ a := by
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have hcube : B / (c * 2 ^ j) ≤ a ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    calc B ≤ Pi := hfloor
      _ ≤ c * 2 ^ j * a ^ 3 := htri
      _ = a ^ 3 * (c * 2 ^ j) := by ring
  have hr : (0:ℝ) < B / (c * 2 ^ j) := by positivity
  have h1 : (B / (c * 2 ^ j)) ^ ((1:ℝ)/3) ≤ (a ^ 3 : ℝ) ^ ((1:ℝ)/3) :=
    Real.rpow_le_rpow hr.le hcube (by norm_num)
  have h2 : (a ^ 3 : ℝ) ^ ((1:ℝ)/3) = a := by
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha]
    norm_num
  have h3 : (B / (c * 2 ^ j)) ^ ((1:ℝ)/3)
      = (B / c) ^ ((1:ℝ)/3) * ((2:ℝ) ^ j) ^ (-(1:ℝ)/3) := by
    rw [neg_div, Real.rpow_neg h2j.le, ← div_eq_mul_inv,
      ← Real.div_rpow (by positivity) h2j.le, div_div]
  rw [← h2, ← h3]
  exact h1

/-- **Effective finite-band sufficiency.**  Floors verified on the
explicitly many bands `j < J`, `J ≥ M/b₀` with
`b₀ = ((B/c)^{1/3})²`, already push the `H^s` weighted sum (`s ≥ 1/3`)
above the given bound `M`: a finite computation defeats any *given*
regularity bound.  (Hypotheses quantified over `j < J` only.) -/
theorem effective_band_count {a Pi : ℕ → ℝ} {B c s M : ℝ} {J : ℕ}
    (hB : 0 < B) (hc : 0 < c) (hs : (1:ℝ)/3 ≤ s)
    (ha : ∀ j < J, 0 ≤ a j) (hfloor : ∀ j < J, B ≤ Pi j)
    (htri : ∀ j < J, Pi j ≤ c * 2 ^ j * a j ^ 3)
    (hJ : M / ((B / c) ^ ((1:ℝ)/3)) ^ 2 ≤ (J : ℝ)) :
    M ≤ ∑ j ∈ range J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
  set b₀ : ℝ := ((B / c) ^ ((1:ℝ)/3)) ^ 2 with hb₀
  have hb₀pos : 0 < b₀ := by positivity
  have hterm : ∀ j < J, b₀ ≤ ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    intro j hj
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have h2j1 : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hA := amplitude_floor_single j hB hc (ha j hj) (hfloor j hj) (htri j hj)
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
  have h1 : (J : ℝ) * b₀ ≤ ∑ j ∈ range J, ((2:ℝ) ^ j) ^ (2*s) * a j ^ 2 := by
    calc (J : ℝ) * b₀ = ∑ _j ∈ range J, b₀ := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
          hterm j (Finset.mem_range.mp hj)
  have h2 : M ≤ (J : ℝ) * b₀ := by
    rw [div_le_iff₀ hb₀pos] at hJ
    linarith
  linarith

/-- **The CAP master theorem.**  Suppose on the window `[w₀, min e w)`:
(i) the enclosure `|ν_t − ν̃_t| ≤ ε` around the validated numerical
trajectory (a-posteriori bound, `aposteriori_gronwall`); (ii) the floors
`B ≤ ν̃_t` verified by finite interval arithmetic; (iii) the theory-side
ceiling `ν_t ≤ C·t^{-q}` (the one analytic input, item C2); and (iv) the
finite margin check `max w₀ ((C/(B−ε))^{1/q}) < w`.  Then the epoch of
regularity ends inside the window:
`e ≤ max w₀ ((C/(B−ε))^{1/q}) < w`.  Every hypothesis except (iii) is
finitely checkable; the conclusion is analytic. -/
theorem validated_epoch_ends_inside {nut nutN : ℝ → ℝ}
    {B C q w₀ w ε e : ℝ}
    (hq : 0 < q) (hw₀ : 0 ≤ w₀) (hε : 0 ≤ ε) (hεB : ε < B)
    (henc : ∀ t ∈ Set.Ico w₀ (min e w), |nut t - nutN t| ≤ ε)
    (hfloorN : ∀ t ∈ Set.Ico w₀ (min e w), B ≤ nutN t)
    (hceil : ∀ t ∈ Set.Ico w₀ (min e w), nut t ≤ C * t ^ (-q))
    (hwin : max w₀ ((C / (B - ε)) ^ q⁻¹) < w) :
    e ≤ max w₀ ((C / (B - ε)) ^ q⁻¹) := by
  have hfloor : ∀ t ∈ Set.Ico w₀ (min e w), B - ε ≤ nut t := by
    intro t ht
    have h1 := abs_le.1 (henc t ht)
    have h2 := hfloorN t ht
    linarith [h1.1]
  have h1 := epoch_le_of_shifted_floor_polynomial_ceiling
    (by linarith : 0 < B - ε) hq hw₀ hfloor hceil
  rcases min_cases e w with ⟨hmin, _⟩ | ⟨hmin, hle⟩
  · rwa [hmin] at h1
  · rw [hmin] at h1
    linarith

/-- **A-posteriori enclosure growth (Grönwall wrapper).**  If the
difference `d` between the true and the validated numerical trajectory
starts at `0`, and its right derivative obeys the defect/Lipschitz bound
`‖d'‖ ≤ K‖d‖ + δ` on the window (defect `δ` from interval-validated
integration; `K` a Lipschitz constant of the vector field on the
enclosure tube), then `‖d(x)‖ ≤ gronwallBound 0 K δ (x − w₀)`
(`= (δ/K)(e^{K(x−w₀)} − 1)` for `K ≠ 0`): the enclosure `ε` of the master
theorem, with its explicit growth law. -/
theorem aposteriori_gronwall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d d' : ℝ → E} {δ K w₀ w : ℝ}
    (hd : ContinuousOn d (Set.Icc w₀ w))
    (hd' : ∀ x ∈ Set.Ico w₀ w, HasDerivWithinAt d (d' x) (Set.Ici x) x)
    (h0 : ‖d w₀‖ ≤ 0)
    (hdefect : ∀ x ∈ Set.Ico w₀ w, ‖d' x‖ ≤ K * ‖d x‖ + δ) :
    ∀ x ∈ Set.Icc w₀ w, ‖d x‖ ≤ gronwallBound 0 K δ (x - w₀) :=
  norm_le_gronwallBound_of_norm_deriv_right_le hd hd' h0 hdefect

end EnergyDefect
