module

/-
  Concrete, nondegenerate law witnesses for the actual maximum and
  hidden-mass results of arXiv:2004.05894v1, Remark 1's corrected version.
-/
public import Stats.HiddenMoments.Counterexample

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

local notation "ν" => paretoMeasure (1 : ℝ) 2
local notation "μ" => iidSampleLaw 2 ν

local instance : IsProbabilityMeasure ν :=
  instIsProbabilityMeasureParetoMeasure 1 2 (by norm_num) (by norm_num)

example : IsProbabilityMeasure μ := inferInstance

example : Measurable (sampleMaximum : (Fin 2 → ℝ) → ℝ) := measurable_sampleMaximum

example : iIndepFun (fun i (x : Fin 2 → ℝ) => x i) μ := iidSample_indep 2 ν

example : IdentDistrib (fun x : Fin 2 → ℝ => x 1) id μ ν := iidSample_identDistrib 2 ν 1

example : (μ).real {x | sampleMaximum x < 2} = 9 / 16 := by
  rw [sampleMaximum_cdf_lt, measureReal_congr Iio_ae_eq_Iic,
    paretoMeasure_real_Iic (by norm_num) (by norm_num)]
  norm_num [Real.rpow_ofNat]

example : ∀ᵐ x ∂μ, 1 < sampleMaximum x :=
  paretoSampleMaximum_ae_gt (by norm_num) (by norm_num)

example : Measurable (sampleHiddenMass ν : (Fin 2 → ℝ) → ℝ) := measurable_sampleHiddenMass ν

example : Integrable (sampleHiddenMass ν : (Fin 2 → ℝ) → ℝ) μ := sampleHiddenMass_integrable ν

example : ∀ᵐ x ∂μ, sampleHiddenMass ν x = (1 / sampleMaximum x) ^ (2 : ℝ) :=
  sampleHiddenMass_pareto_eq (by norm_num) (by norm_num)

example : ∀ᵐ x ∂μ, 0 < sampleHiddenMass ν x :=
  sampleHiddenMass_pareto_ae_pos (by norm_num) (by norm_num)

example : 0 < paretoSurvivalThreshold 1 2 (1 / 4) :=
  paretoSurvivalThreshold_pos (by norm_num) (by norm_num)

example : 1 ≤ paretoSurvivalThreshold 1 2 (1 / 4) :=
  paretoSurvivalThreshold_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 : ℝ) ↔ 2 ≤ paretoSurvivalThreshold 1 2 (1 / 4) :=
  paretoSurvival_ge_iff_le_threshold (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (1 / 4 : ℝ) < (1 / 2 : ℝ) ^ (2 : ℝ) ↔ 2 < paretoSurvivalThreshold 1 2 (1 / 4) :=
  paretoSurvival_gt_iff_lt_threshold (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (μ).real {x | (1 / 4 : ℝ) ≤ sampleHiddenMass ν x} = 9 / 16 := by
  rw [paretoHiddenMass_tail_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : (μ).real {x | (1 / 4 : ℝ) < sampleHiddenMass ν x} = 9 / 16 := by
  rw [paretoHiddenMass_tail_gt (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : (μ).real {x | sampleHiddenMass ν x ≤ 1 / 4} = 7 / 16 := by
  rw [paretoHiddenMass_cdf (by norm_num) (by norm_num)]
  norm_num [paretoSampleSurvivalRatioCDF]

example : (μ).real {x | (1 / sampleMaximum x) ^ (2 : ℝ) ≤ 1 / 4} = 7 / 16 := by
  rw [paretoSampleSurvivalRatio_cdf (by norm_num) (by norm_num)]
  norm_num [paretoSampleSurvivalRatioCDF]

example : (μ).real {x | sampleHiddenMass ν x ≤ 0} = 0 := by
  rw [paretoHiddenMass_cdf (by norm_num) (by norm_num)]
  norm_num

example : (μ).real {x | sampleHiddenMass ν x ≤ 1} = 1 := by
  rw [paretoHiddenMass_cdf (by norm_num) (by norm_num)]
  norm_num

example : ((μ).map (sampleHiddenMass ν)) ≠ expMeasure 2 := by
  have h := paretoHiddenMass_not_exponential (n := 2) (l := 1) (α := 2)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

#print axioms paretoSampleMaximum_cdf
#print axioms paretoHiddenMass_cdf
#print axioms paretoHiddenMass_mean
#print axioms paretoHiddenMass_not_exponential

end TailOptionPricing
