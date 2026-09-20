/-
# The Hardy/analyticity route for F2 (proposed workaround, formal dissection)

Formalization of the proposed F2 workaround (drop "Montel"; use only
analyticity of the scalar function `t ↦ ν_t(t)`; differentiate the running
`L^{4/3}(0, ε)` norm in `ε`; obtain the rate from Hardy-space boundary
value theory).  See `research/routes/HARDY_ANALYTICITY.md` for the full
assessment.

Proven here:

* `hasDerivAt_running_rpow_integral` — the differentiation step is **valid
  and exact**: for continuous `ν_t`,
  `d/dε ∫₀^ε |ν_t|^p = |ν_t(ε)|^p`.  (It transfers no decay by itself:
  `EnergyDefect.no_decay_from_memLp`.)
* `no_persistent_floor_of_integrable` — the **integrability form of the
  blowup engine**: a uniform bound on the running `L^p` norm is
  incompatible with a persistent constant floor.  No rates, no exponentials
  — `L^{4/3}`-type control alone refutes an eternal floor, concentrating
  the entire difficulty of the program in F3-persistence.
* `crossing_of_constant_floor_polynomial_ceiling` — the **corrected
  crossing lemma** for the rates the Hardy step actually yields: a constant
  floor `B` against the polynomial ceiling `C·t^{-q}` (Hardy: `q = 3/4`
  for `p = 4/3`) forces `t ≤ (C/B)^{1/q}`.  Together with the windowed
  floor (`constant_floor_of_pos_on_compact`) this is a complete alternative
  blowup skeleton needing no exponential F2 at all.
-/
import EnergyDefect.Interface
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EnergyDefect

open Real MeasureTheory intervalIntegral

/-- **The differentiation-in-ε step (valid, exact).**  For continuous
(a fortiori analytic) `ν_t` and `p ≥ 0`, the running `L^p`-norm functional
`F(ε) = ∫₀^ε |ν_t|^p` is differentiable with `F'(ε) = |ν_t(ε)|^p` exactly.
Pointwise evaluation of the fluctuation is recovered from the family of
norms — but note this transfers no decay by itself
(`EnergyDefect.no_decay_from_memLp`). -/
theorem hasDerivAt_running_rpow_integral {f : ℝ → ℝ} {p : ℝ}
    (hf : Continuous f) (hp : 0 ≤ p) (ε : ℝ) :
    HasDerivAt (fun s => ∫ t in (0:ℝ)..s, |f t| ^ p) (|f ε| ^ p) ε := by
  have hcont : Continuous fun t => |f t| ^ p :=
    hf.abs.rpow_const fun x => Or.inr hp
  exact integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- **The integrability form of the blowup engine.**  If the running
`L^p` norm of the fluctuation is uniformly bounded (which is all that
`ν_t ∈ L^{4/3}` gives — no rate needed), then `ν_t` cannot sit above a
positive constant floor forever: the two hypotheses are contradictory.
No exponential rates are involved; the entire difficulty of the program is
thereby concentrated in the *persistence* of the floor (F3). -/
theorem no_persistent_floor_of_integrable {nut : ℝ → ℝ} {p B M : ℝ}
    (hp : 0 < p) (hB : 0 < B)
    (hint : ∀ T, 0 < T → IntervalIntegrable (fun t => |nut t| ^ p) volume 0 T)
    (hbound : ∀ T, 0 < T → (∫ t in (0:ℝ)..T, |nut t| ^ p) ≤ M)
    (hfloor : ∀ t, 0 ≤ t → B ≤ nut t) : False := by
  have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hB p
  set T := (M + 1) / B ^ p with hT
  have hM0 : 0 ≤ M :=
    le_trans (intervalIntegral.integral_nonneg zero_le_one
      fun x _ => Real.rpow_nonneg (abs_nonneg _) p) (hbound 1 one_pos)
  have hT0 : 0 < T := by positivity
  have h1 : (∫ _ in (0:ℝ)..T, B ^ p) ≤ ∫ t in (0:ℝ)..T, |nut t| ^ p := by
    apply integral_mono_on hT0.le (intervalIntegrable_const) (hint T hT0)
    intro t ht
    have hBn : B ≤ |nut t| := (hfloor t ht.1).trans (le_abs_self _)
    exact Real.rpow_le_rpow hB.le hBn hp.le
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  have h2 := hbound T hT0
  have h3 : T * B ^ p = M + 1 := by rw [hT]; field_simp
  linarith

/-- **The corrected crossing lemma for the Hardy route.**  The rates that
Hardy-space boundary theory actually yields for `p = 4/3` are polynomial
(`C·t^{-3/4}`, the exponent lands in the *power*, not in an exponential).
Against an exponential floor such a ceiling produces no contradiction
(`EnergyDefect.no_contradiction_from_polynomial_decay`) — but against a
**constant** floor (the windowed F3‴ form,
`constant_floor_of_pos_on_compact`) it forces the explicit crossing
`t ≤ (C/B)^{1/q}`: a complete alternative blowup skeleton with no
exponential F2 needed. -/
theorem crossing_of_constant_floor_polynomial_ceiling {nut : ℝ → ℝ}
    {B C q t : ℝ} (hB : 0 < B) (hq : 0 < q) (ht : 0 < t)
    (hfloor : B ≤ nut t) (hceil : nut t ≤ C * t ^ (-q)) :
    t ≤ (C / B) ^ q⁻¹ := by
  have htq : (0:ℝ) < t ^ q := Real.rpow_pos_of_pos ht q
  have h1 : B ≤ C * t ^ (-q) := hfloor.trans hceil
  rw [Real.rpow_neg ht.le, ← div_eq_mul_inv, le_div_iff₀ htq] at h1
  have h3 : t ^ q ≤ C / B := (le_div_iff₀ hB).2 (by linarith)
  calc t = (t ^ q) ^ q⁻¹ := by
        rw [← Real.rpow_mul ht.le, mul_inv_cancel₀ hq.ne', Real.rpow_one]
    _ ≤ (C / B) ^ q⁻¹ := Real.rpow_le_rpow htq.le h3 (by positivity)

/-- **The windowed blowup skeleton, composed.**  If on an epoch `[0, e)` the
fluctuation sits above a constant floor `B > 0` (the F3‴ output of
`constant_floor_of_pos_on_compact`) and below the polynomial ceiling
`C·t^{-q}` (the Hardy-route output, `q = 3/4` for `p = 4/3`), then
`e ≤ max 0 ((C/B)^{1/q})`: the epoch of regularity ends by an explicit
time.  This is the polynomial-ceiling counterpart of
`epoch_le_of_decayBounds` — the complete alternative engine requiring no
exponential F2. -/
theorem epoch_le_of_constant_floor_polynomial_ceiling {nut : ℝ → ℝ}
    {B C q e : ℝ} (hB : 0 < B) (hq : 0 < q)
    (hfloor : ∀ t ∈ Set.Ico (0:ℝ) e, B ≤ nut t)
    (hceil : ∀ t ∈ Set.Ico (0:ℝ) e, nut t ≤ C * t ^ (-q)) :
    e ≤ max 0 ((C / B) ^ q⁻¹) := by
  by_contra hcon
  push Not at hcon
  set M := max 0 ((C / B) ^ q⁻¹) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMc : (C / B) ^ q⁻¹ ≤ M := le_max_right _ _
  set t := (M + e) / 2 with ht
  have hte : t < e := by simp only [ht]; linarith
  have htM : M < t := by simp only [ht]; linarith
  have ht0 : 0 < t := lt_of_le_of_lt hM0 htM
  have h1 := crossing_of_constant_floor_polynomial_ceiling hB hq ht0
    (hfloor t ⟨ht0.le, hte⟩) (hceil t ⟨ht0.le, hte⟩)
  linarith

/-- **Shifted-window engine (proven).**  Completes the zero-gap repair at
the interface level: a constant floor on a *shifted* zero-free window
`[w₀, e)` (whose existence is guaranteed by
`analytic_pos_zeros_finite_on_compact`) together with the polynomial
ceiling on the epoch forces `e ≤ max w₀ ((C/B)^{1/q})`.  Windows need not
be anchored at `0`. -/
theorem epoch_le_of_shifted_floor_polynomial_ceiling {nut : ℝ → ℝ}
    {B C q w₀ e : ℝ} (hB : 0 < B) (hq : 0 < q) (hw₀ : 0 ≤ w₀)
    (hfloor : ∀ t ∈ Set.Ico w₀ e, B ≤ nut t)
    (hceil : ∀ t ∈ Set.Ico w₀ e, nut t ≤ C * t ^ (-q)) :
    e ≤ max w₀ ((C / B) ^ q⁻¹) := by
  by_contra hcon
  push Not at hcon
  set M := max w₀ ((C / B) ^ q⁻¹) with hM
  have hM0 : w₀ ≤ M := le_max_left _ _
  have hMc : (C / B) ^ q⁻¹ ≤ M := le_max_right _ _
  set t := (M + e) / 2 with ht
  have hte : t < e := by simp only [ht]; linarith
  have htM : M < t := by simp only [ht]; linarith
  have htw : w₀ ≤ t := le_trans hM0 htM.le
  have ht0 : 0 < t := lt_of_le_of_lt (hw₀.trans hM0) htM
  have h1 := crossing_of_constant_floor_polynomial_ceiling hB hq ht0
    (hfloor t ⟨htw, hte⟩) (hceil t ⟨htw, hte⟩)
  linarith

/-- **Shell-uniform floor route (abstract core, proven).**  A floor that is
uniform across frequency bands defeats any fixed bound on the summed
functional: if every band flux satisfies `B ≤ Π_j(t)` on a common window,
then for any threshold `M` finitely many bands already push the summed
flux above `M` throughout the window.  Empirical basis: in the dyadic
blowup regime the per-band persistence window and constants are *the same
at every shell and every truncation* (front_probe.py); a scalar floor
saturating its crossing is compatible with regularity, but simultaneous
saturation at all scales is not — for NS, `Σ_j Π_j = ∞` on a window means
the solution has left `H^{1/3+ε}` there (Onsager-critical roughness), and
the windowed engine then ends the epoch inside the window. -/
theorem uniform_band_floor_defeats_bound {Pi : ℕ → ℝ → ℝ} {S : Set ℝ}
    {B : ℝ} (hB : 0 < B) (hfloor : ∀ j, ∀ t ∈ S, B ≤ Pi j t) (M : ℝ) :
    ∃ J : ℕ, ∀ t ∈ S, M ≤ ∑ j ∈ Finset.range J, Pi j t := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (M / B)
  refine ⟨J, fun t ht => ?_⟩
  have h1 : (J : ℝ) * B ≤ ∑ j ∈ Finset.range J, Pi j t := by
    calc (J : ℝ) * B = ∑ _j ∈ Finset.range J, B := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ j ∈ Finset.range J, Pi j t :=
          Finset.sum_le_sum fun j _ => hfloor j t ht
  have h2 : M ≤ (J : ℝ) * B := by
    rw [div_le_iff₀ hB] at hJ
    linarith
  linarith

end EnergyDefect
