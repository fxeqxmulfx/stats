module

/-
  The actual iid Pareto maximum for arXiv:2004.05894v1, before
  Proposition 1. The exact finite-sample CDF includes its full support;
  no Fréchet approximation is substituted for the probability law.
-/
public import Stats.Pareto.Measure
public import Stats.RiskMeasures.Drawdown
public import Stats.Probability.SampleMaximum

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

instance paretoMeasure_nullSingletonClass (l α : ℝ) :
    NullSingletonClass (paretoMeasure l α) := by
  unfold paretoMeasure
  infer_instance

/-- Full supported CDF of the density-defined Pareto probability measure. -/
theorem paretoMeasure_real_Iic {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (t : ℝ) :
    (paretoMeasure l α).real (Iic t) = if t < l then 0 else 1 - (l / t) ^ α := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  have hc (s : ℝ) : (paretoMeasure l α).real (Iic s) =
      1 - (paretoMeasure l α).real (Ioi s) := by
    rw [← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ]
  have hl0 : (paretoMeasure l α).real (Iic l) = 0 := by
    rw [hc, paretoMeasure_real_Ioi_eq_survival hl hα le_rfl, div_self hl.ne', Real.one_rpow]
    norm_num
  split_ifs with ht
  · exact measureReal_mono_null (Iic_subset_Iic.mpr ht.le) hl0
  · rw [hc, paretoMeasure_real_Ioi_eq_survival hl hα (le_of_not_gt ht)]

/-- Actual finite iid maximum CDF, including the region below support
(arXiv:2004.05894v1, sample maximum before Proposition 1). -/
theorem paretoSampleMaximum_cdf {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) (t : ℝ) :
    (iidSampleLaw n (paretoMeasure l α)).real {x | sampleMaximum x ≤ t} =
      if t < l then 0 else paretoSampleMaxCDF n l α t := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  rw [sampleMaximum_cdf, paretoMeasure_real_Iic hl hα]
  split_ifs <;> simp [paretoSampleMaxCDF, NeZero.ne n]

/-- Above support, the candidate expression is now identified with the
tail of the actual maximum, under its genuine product sample law. -/
theorem paretoSampleMaximum_survival {n : ℕ} [NeZero n] {l α t : ℝ}
    (hl : 0 < l) (hα : 0 < α) (ht : l ≤ t) :
    (iidSampleLaw n (paretoMeasure l α)).real {x | t < sampleMaximum x} =
      paretoSampleMaxSurvival n l α t := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  rw [sampleMaximum_survival, paretoMeasure_real_Iic hl hα, ite_eq_right (not_lt.mpr ht)]
  rfl

/-- The observed maximum lies strictly above the Pareto support boundary
almost surely; in particular, evaluating a power at it has positive base. -/
theorem paretoSampleMaximum_ae_gt {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α), l < sampleMaximum x := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  apply ae_iff.mpr
  rw [← measureReal_eq_zero_iff]
  simp only [not_lt]
  rw [paretoSampleMaximum_cdf hl hα, ite_eq_right (lt_irrefl l)]
  simp [paretoSampleMaxCDF, div_self hl.ne', NeZero.ne n]

example : (paretoMeasure 1 2).real (Iic 0) = 0 := by
  rw [paretoMeasure_real_Iic (by norm_num) (by norm_num)]
  norm_num

example : (iidSampleLaw 2 (paretoMeasure 1 2)).real
    {x | sampleMaximum x ≤ 2} = 9 / 16 := by
  rw [paretoSampleMaximum_cdf (by norm_num) (by norm_num)]
  norm_num [paretoSampleMaxCDF, Real.rpow_ofNat]

example : (iidSampleLaw 2 (paretoMeasure 1 2)).real
    {x | 2 < sampleMaximum x} = 7 / 16 := by
  rw [paretoSampleMaximum_survival (by norm_num) (by norm_num) (by norm_num)]
  norm_num [paretoSampleMaxSurvival, paretoSampleMaxCDF, Real.rpow_ofNat]

end TailOptionPricing
