module

/-
  Nondegenerate witnesses for the actual population moment decomposition
  of arXiv:2004.05894v1. Every integrability input is proved for a genuine
  Pareto law; no desired expectation or decomposition is assumed.
-/
public import Stats.HiddenMoments.Decomposition

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

local notation "ν" => paretoMeasure (1 : ℝ) 2
local notation "μ" => iidSampleLaw 2 ν

local instance decompositionExampleLaw_probability : IsProbabilityMeasure ν :=
  instIsProbabilityMeasureParetoMeasure 1 2 (by norm_num) (by norm_num)

private theorem integrable_power_one : Integrable (fun s : ℝ => s ^ (1 : ℝ)) ν :=
  (paretoMeasure_integrable_rpow_iff (by norm_num) (by norm_num)).mpr (by norm_num)

example : (∫ s : ℝ, s ∂ν) = ∫ s in Ioi (1 : ℝ), s * paretoDensity 1 2 s :=
  paretoMeasure_integral (by norm_num) (by norm_num) id

example : Integrable (fun s : ℝ => s) ν ↔
    IntegrableOn (fun s : ℝ => s * paretoDensity 1 2 s) (Ioi 1) volume :=
  paretoMeasure_integrable_iff (by norm_num) (by norm_num) id

example : (∫ s in Ioi (2 : ℝ), s ∂ν) =
    ∫ s in Ioi (1 : ℝ) ∩ Ioi 2, s * paretoDensity 1 2 s :=
  paretoMeasure_setIntegral (by norm_num) (by norm_num) id measurableSet_Ioi

example : Measurable (sampleHiddenMoment ν 1 : (Fin 2 → ℝ) → ℝ) :=
  measurable_sampleHiddenMoment ν 1

example : Measurable (sampleVisibleMoment ν 1 : (Fin 2 → ℝ) → ℝ) :=
  measurable_sampleVisibleMoment ν 1

example (x : Fin 2 → ℝ) : (∫ s : ℝ, s ^ (1 : ℝ) ∂ν) =
    sampleVisibleMoment ν 1 x + sampleHiddenMoment ν 1 x :=
  sampleMoment_decomposition ν 1 integrable_power_one x

example (x : Fin 2 → ℝ) : (2 : ℝ) =
    sampleVisibleMoment ν 1 x + sampleHiddenMoment ν 1 x := by
  have h := paretoSample_moment_decomposition (l := 1) (α := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num) x
  norm_num at h
  exact h

example : Integrable (sampleHiddenMoment ν 1 : (Fin 2 → ℝ) → ℝ) μ :=
  paretoSample_hiddenMoment_integrable (by norm_num) (by norm_num) (by norm_num)

example : Integrable (sampleVisibleMoment ν 1 : (Fin 2 → ℝ) → ℝ) μ :=
  paretoSample_visibleMoment_integrable (by norm_num) (by norm_num) (by norm_num)

example : ∀ᵐ x ∂μ, sampleHiddenMoment ν 1 x = paretoTailMoment 1 2 1 (sampleMaximum x) :=
  sampleHiddenMoment_pareto_eq_tailMoment (by norm_num) (by norm_num) 1

example (x : Fin 2 → ℝ) : sampleVisibleMoment ν 1 x =
    ∫ s in Ioc (1 : ℝ) (sampleMaximum x), s ^ (1 : ℝ) * paretoDensity 1 2 s :=
  sampleVisibleMoment_pareto_density (by norm_num) (by norm_num) 1 x

example : ∀ᵐ x ∂μ, sampleHiddenMoment ν 1 x = 2 / sampleMaximum x := by
  have h := sampleHiddenMoment_pareto_closed_form (n := 2) (l := 1) (α := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h] with x hx
  norm_num [Real.rpow_neg_one, div_eq_mul_inv] at hx ⊢
  exact hx

example : ∀ᵐ x ∂μ, sampleVisibleMoment ν 1 x < 2 := by
  have h := paretoSample_visibleMoment_lt_population (n := 2) (l := 1) (α := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : (∫ x : Fin 2 → ℝ, sampleVisibleMoment ν 1 x ∂μ) +
    (∫ x : Fin 2 → ℝ, sampleHiddenMoment ν 1 x ∂μ) = 2 := by
  rw [expected_sampleMoment_decomposition ν 1 integrable_power_one,
    paretoMeasure_integral_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example (x : Fin 2 → ℝ) : sampleHiddenMoment ν 0 x = sampleHiddenMass ν x :=
  sampleHiddenMoment_zero ν x

#print axioms paretoMeasure_integrable_rpow_iff
#print axioms paretoMeasure_integral_rpow
#print axioms paretoSample_moment_decomposition
#print axioms sampleHiddenMoment_pareto_closed_form

end TailOptionPricing
