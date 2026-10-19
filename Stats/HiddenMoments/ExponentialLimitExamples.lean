module

/-
  Concrete actual-law certificates for the scaled exponential weak limit
  correcting arXiv:2004.05894v1, Remark 1. They check positive sample
  indexing, scale factors, support endpoints and an infinite-mean population.
-/
public import Stats.HiddenMoments.ExponentialLimit
public import Stats.HiddenMoments.ContinuousLawExamples
public import Stats.Pareto.Moments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

local notation "ν" => expMeasure (1 : ℝ)
local notation "ρ" => paretoMeasure (1 : ℝ) (1 / 2)

local instance exponentialLimitExampleLaw_probability : IsProbabilityMeasure ν :=
  isProbabilityMeasure_expMeasure (by norm_num)

local instance infiniteMeanLimitExampleLaw_probability : IsProbabilityMeasure ρ :=
  instIsProbabilityMeasureParetoMeasure 1 (1 / 2) (by norm_num) (by norm_num)

example : IsProbabilityMeasure (scaledHiddenMassLaw ν 1 : Measure ℝ) := inferInstance

example : cdf (unitExponentialLaw : Measure ℝ) 1 = 1 - Real.exp (-1) := by
  change cdf (expMeasure 1) 1 = _
  rw [cdf_expMeasure_eq (by norm_num)]
  norm_num

-- Index zero is a genuine sample of size one, scaled by one.
example : cdf (scaledHiddenMassLaw ν 0 : Measure ℝ) (1 / 2) = 1 / 2 := by
  rw [scaledHiddenMassLaw_cdf ν (continuous_expMeasure_cdf (by norm_num))]
  have h := betaMeasure_one_nat_cdf (n := 1) (by norm_num) (1 / 2)
  norm_num [paretoSampleSurvivalRatioCDF] at h ⊢
  exact h

-- Index one uses two observations and scale two, so its upper support is two.
example : cdf (scaledHiddenMassLaw ν 1 : Measure ℝ) 1 = 3 / 4 := by
  rw [scaledHiddenMassLaw_cdf ν (continuous_expMeasure_cdf (by norm_num))]
  have h := betaMeasure_one_nat_cdf (n := 2) (by norm_num) (1 / 2)
  norm_num [paretoSampleSurvivalRatioCDF] at h ⊢
  exact h

example : cdf (scaledHiddenMassLaw ν 1 : Measure ℝ) (-1) = 0 := by
  rw [scaledHiddenMassLaw_cdf ν (continuous_expMeasure_cdf (by norm_num))]
  have h := betaMeasure_one_nat_cdf (n := 2) (by norm_num) (-1 / 2)
  norm_num at h ⊢
  exact h

example : cdf (scaledHiddenMassLaw ν 1 : Measure ℝ) 0 = 0 := by
  rw [scaledHiddenMassLaw_cdf ν (continuous_expMeasure_cdf (by norm_num))]
  have h := betaMeasure_one_nat_cdf (n := 2) (by norm_num) 0
  norm_num at h ⊢
  exact h

example : cdf (scaledHiddenMassLaw ν 1 : Measure ℝ) 2 = 1 := by
  rw [scaledHiddenMassLaw_cdf ν (continuous_expMeasure_cdf (by norm_num))]
  have h := betaMeasure_one_nat_cdf (n := 2) (by norm_num) 1
  norm_num at h ⊢
  exact h

example (t : ℝ) : Tendsto (fun n : ℕ => cdf (scaledHiddenMassLaw ν n : Measure ℝ) t)
    atTop (𝓝 (cdf (unitExponentialLaw : Measure ℝ) t)) :=
  scaledHiddenMassLaw_cdf_tendsto ν (continuous_expMeasure_cdf (by norm_num)) t

-- The CDF-convergence hypothesis has an actual varying-law witness.
example : Tendsto (scaledHiddenMassLaw ν) atTop (𝓝 unitExponentialLaw) :=
  probabilityMeasure_tendsto_of_cdf (fun t =>
    scaledHiddenMassLaw_cdf_tendsto ν (continuous_expMeasure_cdf (by norm_num)) t)

example : Tendsto (scaledHiddenMassLaw ν) atTop (𝓝 unitExponentialLaw) :=
  scaledHiddenMassLaw_tendsto ν (continuous_expMeasure_cdf (by norm_num))

example : Continuous (cdf ρ : ℝ → ℝ) :=
  continuous_paretoMeasure_cdf (by norm_num) (by norm_num)

example : ¬ Integrable (fun s : ℝ => s) ρ := by
  rw [paretoMeasure_integrable_id_iff (by norm_num) (by norm_num)]
  norm_num

example : Tendsto (scaledHiddenMassLaw ρ) atTop (𝓝 unitExponentialLaw) :=
  paretoScaledHiddenMassLaw_tendsto (by norm_num) (by norm_num)

#print axioms probabilityMeasure_tendsto_of_cdf
#print axioms scaledHiddenMassLaw_cdf
#print axioms scaledHiddenMassLaw_tendsto
#print axioms paretoScaledHiddenMassLaw_tendsto

end TailOptionPricing
