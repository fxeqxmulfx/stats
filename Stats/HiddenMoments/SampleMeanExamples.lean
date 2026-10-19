module

/-
  Actual iid Pareto witnesses refuting necessary sample-mean
  underestimation (arXiv:2004.05894v1, conclusion, line 278).
  A finite mean suffices, even though the variance here is infinite.
-/
public import Stats.HiddenMoments.SampleMean

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

local notation "ν" => paretoMeasure (1 : ℝ) 2
local notation "μ" => iidSampleLaw 2 ν

local instance sampleMeanExampleLaw_probability : IsProbabilityMeasure ν :=
  instIsProbabilityMeasureParetoMeasure 1 2 (by norm_num) (by norm_num)

example : Measurable (sampleMean : (Fin 2 → ℝ) → ℝ) := measurable_sampleMean

example : Integrable (sampleMean : (Fin 2 → ℝ) → ℝ) μ :=
  sampleMean_integrable ν
    ((paretoMeasure_integrable_id_iff (by norm_num) (by norm_num)).mpr (by norm_num))

example : (∫ x : Fin 2 → ℝ, sampleMean x ∂μ) = 2 := by
  rw [paretoSampleMean_unbiased (by norm_num) (by norm_num)]
  norm_num

example : ∀ᵐ s ∂ν, 1 < s := paretoMeasure_ae_gt (by norm_num) (by norm_num)

example : ∀ᵐ x ∂μ, ∀ i : Fin 2, 0 ≤ x i := by
  apply iidSample_ae_nonneg
  filter_upwards [paretoMeasure_ae_gt (l := 1) (α := 2) (by norm_num) (by norm_num)] with s hs
  linarith

example : 1 / 16 ≤ (μ).real {x | 2 < sampleMean x} := by
  have h := paretoSampleMean_upper_tail_lower (n := 2) (l := 1) (α := 2)
    (by norm_num) (by norm_num)
  norm_num [Real.rpow_ofNat] at h
  exact h

example : 0 < (μ).real {x | 2 < sampleMean x} := by
  have h := paretoSampleMean_can_exceed_mean (n := 2) (l := 1) (α := 2)
    (by norm_num) (by norm_num)
  rw [paretoMeasure_mean (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h

example : ¬ ∀ᵐ x ∂μ, sampleMean x ≤ ∫ s : ℝ, s ∂ν :=
  paretoSampleMean_not_always_below_mean (by norm_num) (by norm_num)

-- The one-observation counterexample has an exact positive probability.
example : (iidSampleLaw 1 ν).real {x | 2 < sampleMean x} = 1 / 4 := by
  calc (iidSampleLaw 1 ν).real {x | 2 < sampleMean x}
      = (iidSampleLaw 1 ν).real {x | 2 < x 0} := by
        congr 1
        ext x
        simp only [mem_ofPred_eq, sampleMean_one]
    _ = (ν).real (Ioi 2) := congrArg ENNReal.toReal
        ((iidSample_identDistrib 1 ν 0).measure_mem_eq (s := Ioi 2) measurableSet_Ioi)
    _ = 1 / 4 := by
      rw [paretoMeasure_real_Ioi_eq_survival (by norm_num) (by norm_num) (by norm_num)]
      norm_num [Real.rpow_ofNat]

#print axioms sampleMean_unbiased
#print axioms paretoSampleMean_upper_tail_lower
#print axioms paretoSampleMean_not_always_below_mean

end TailOptionPricing
