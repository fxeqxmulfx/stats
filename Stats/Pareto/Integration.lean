module

/-
  Integration against the actual supported Pareto law. These bridges
  connect the density integrals in arXiv:2004.05894v1, Eq. 2 and its
  preceding moment decomposition, with genuine expectations and L1.
-/
public import Stats.Pareto.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

private noncomputable def paretoLawWeight (l α s : ℝ) : ENNReal :=
  if l < s then ENNReal.ofReal (paretoDensity l α s) else 0

private theorem measurable_paretoLawWeight (l α : ℝ) : Measurable (paretoLawWeight l α) :=
  Measurable.ite measurableSet_Ioi
    (ENNReal.measurable_ofReal.comp (paretoDensity_measurable l α)) measurable_const

private theorem paretoLawWeight_finite (l α : ℝ) :
    ∀ᵐ s ∂volume, paretoLawWeight l α s < ⊤ := by
  apply Filter.Eventually.of_forall
  intro s
  unfold paretoLawWeight
  split_ifs <;> finiteness

private theorem paretoLawWeight_mul {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (g : ℝ → ℝ) :
    (fun s => g s * (paretoLawWeight l α s).toReal) =
      (Ioi l).indicator (fun s => g s * paretoDensity l α s) := by
  funext s
  by_cases hs : l < s
  · have hs0 : 0 < s := hl.trans hs
    have hd : 0 ≤ paretoDensity l α s := by
      unfold paretoDensity
      exact div_nonneg (mul_nonneg hα.le (Real.rpow_nonneg hl.le _))
        (Real.rpow_nonneg hs0.le _)
    rw [paretoLawWeight, ite_eq_left hs, ENNReal.toReal_ofReal hd,
      indicator_of_mem (show s ∈ Ioi l from hs)]
  · rw [paretoLawWeight, ite_eq_right hs, ENNReal.toReal_zero, mul_zero,
      indicator_of_notMem (show s ∉ Ioi l from hs)]

/-- An actual Pareto expectation equals the supported density integral.
Both sides use Lean's total integral; finite-expectation claims must also
establish integrability, as in `paretoMeasure_integrable_iff`. -/
theorem paretoMeasure_integral {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (g : ℝ → ℝ) :
    (∫ s, g s ∂paretoMeasure l α) = ∫ s in Ioi l, g s * paretoDensity l α s := by
  change (∫ s, g s ∂volume.withDensity (paretoLawWeight l α)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_paretoLawWeight l α)
    (paretoLawWeight_finite l α)]
  have he : (fun s => (paretoLawWeight l α s).toReal • g s) =
      (Ioi l).indicator (fun s => g s * paretoDensity l α s) := by
    simpa only [smul_eq_mul, mul_comm] using paretoLawWeight_mul hl hα g
  rw [he, integral_indicator measurableSet_Ioi]

/-- Exact integrability bridge, so finite Pareto expectations are not
inferred merely by rearranging total-integral formulas. -/
theorem paretoMeasure_integrable_iff {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (g : ℝ → ℝ) :
    Integrable g (paretoMeasure l α) ↔
      IntegrableOn (fun s => g s * paretoDensity l α s) (Ioi l) volume := by
  change Integrable g (volume.withDensity (paretoLawWeight l α)) ↔ _
  rw [integrable_withDensity_iff (measurable_paretoLawWeight l α) (paretoLawWeight_finite l α),
    paretoLawWeight_mul hl hα g, integrable_indicator_iff measurableSet_Ioi]

/-- An actual restricted expectation equals its supported density integral. -/
theorem paretoMeasure_setIntegral {l α : ℝ} (hl : 0 < l) (hα : 0 < α)
    (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ t in s, g t ∂paretoMeasure l α) =
      ∫ t in Ioi l ∩ s, g t * paretoDensity l α t := by
  rw [← integral_indicator hs, paretoMeasure_integral hl hα]
  have he : (fun t => s.indicator g t * paretoDensity l α t) =
      s.indicator (fun t => g t * paretoDensity l α t) := by
    funext t
    exact (indicator_mul_left s g (paretoDensity l α)).symm
  rw [he, setIntegral_indicator hs]

end TailOptionPricing
