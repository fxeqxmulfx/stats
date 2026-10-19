module

/-
  The actual hidden probability mass beyond an iid Pareto sample maximum.
  Its finite-sample Beta(1,n) CDF corrects the exact exponential-law claim
  in arXiv:2004.05894v1, Remark 1. The variable is defined from a measure
  and actual observations, not from its proposed distribution.
-/
public import Stats.HiddenMoments.Maximum
public import Stats.HiddenMoments.Threshold
public import Stats.Probability.HiddenMass

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual population hidden mass agrees with the Pareto tail
formula almost surely, since the observed maximum is in the support. -/
theorem sampleHiddenMass_pareto_eq {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α),
      sampleHiddenMass (paretoMeasure l α) x = (l / sampleMaximum x) ^ α := by
  filter_upwards [paretoSampleMaximum_ae_gt (n := n) hl hα] with x hx
  exact paretoMeasure_real_Ioi_eq_survival hl hα hx.le

theorem sampleHiddenMass_pareto_ae_pos {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α), 0 < sampleHiddenMass (paretoMeasure l α) x := by
  filter_upwards [sampleHiddenMass_pareto_eq (n := n) hl hα,
    paretoSampleMaximum_ae_gt (n := n) hl hα] with x he hx
  rw [he]
  exact Real.rpow_pos_of_pos (div_pos hl (hl.trans hx)) _

/-- Actual closed upper-tail probabilities of the hidden mass. -/
theorem paretoHiddenMass_tail_ge {n : ℕ} [NeZero n] {l α y : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) (hy1 : y ≤ 1) :
    (iidSampleLaw n (paretoMeasure l α)).real
      {x | y ≤ sampleHiddenMass (paretoMeasure l α) x} = (1 - y) ^ n := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  have he : {x : Fin n → ℝ | y ≤ sampleHiddenMass (paretoMeasure l α) x} =ᵐ[
      iidSampleLaw n (paretoMeasure l α)] {x | sampleMaximum x ≤ paretoSurvivalThreshold l α y} := by
    filter_upwards [sampleHiddenMass_pareto_eq (n := n) hl hα,
      paretoSampleMaximum_ae_gt (n := n) hl hα] with x he hx
    apply propext
    rw [he]
    exact paretoSurvival_ge_iff_le_threshold hl hα hy (hl.trans hx)
  rw [measureReal_congr he, sampleMaximum_cdf, paretoMeasure_real_Iic hl hα,
    ite_eq_right (not_lt.mpr (paretoSurvivalThreshold_ge hl hα hy hy1)),
    paretoSurvivalThreshold_survival hl hα hy]

/-- Actual strict upper-tail probabilities, with the endpoint `y=1`. -/
theorem paretoHiddenMass_tail_gt {n : ℕ} [NeZero n] {l α y : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) (hy1 : y ≤ 1) :
    (iidSampleLaw n (paretoMeasure l α)).real
      {x | y < sampleHiddenMass (paretoMeasure l α) x} = (1 - y) ^ n := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  have he : {x : Fin n → ℝ | y < sampleHiddenMass (paretoMeasure l α) x} =ᵐ[
      iidSampleLaw n (paretoMeasure l α)] {x | sampleMaximum x < paretoSurvivalThreshold l α y} := by
    filter_upwards [sampleHiddenMass_pareto_eq (n := n) hl hα,
      paretoSampleMaximum_ae_gt (n := n) hl hα] with x he hx
    apply propext
    rw [he]
    exact paretoSurvival_gt_iff_lt_threshold hl hα hy (hl.trans hx)
  rw [measureReal_congr he, sampleMaximum_cdf_lt,
    measureReal_congr Iio_ae_eq_Iic, paretoMeasure_real_Iic hl hα,
    ite_eq_right (not_lt.mpr (paretoSurvivalThreshold_ge hl hα hy hy1)),
    paretoSurvivalThreshold_survival hl hα hy]

/-- Full supported CDF of the genuine finite-sample hidden mass:
zero below zero, one above one, and `1-(1-y)^n` in between.
This is the Beta(1,n) CDF, correcting the exponential claim in Remark 1. -/
theorem paretoHiddenMass_cdf {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) (y : ℝ) :
    (iidSampleLaw n (paretoMeasure l α)).real
      {x | sampleHiddenMass (paretoMeasure l α) x ≤ y} =
      if y ≤ 0 then 0 else if 1 ≤ y then 1 else paretoSampleSurvivalRatioCDF n y := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  split_ifs with hy0 hy1
  · have hzero : (iidSampleLaw n (paretoMeasure l α)).real
        {x | sampleHiddenMass (paretoMeasure l α) x ≤ 0} = 0 := by
      rw [measureReal_eq_zero_iff]
      simpa only [not_lt] using ae_iff.mp (sampleHiddenMass_pareto_ae_pos (n := n) hl hα)
    exact measureReal_mono_null (fun x hx => hx.trans hy0) hzero
  · have he : {x : Fin n → ℝ | sampleHiddenMass (paretoMeasure l α) x ≤ y} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (sampleHiddenMass_le_one _ x).trans hy1
    rw [he, probReal_univ]
  · have he : {x : Fin n → ℝ | sampleHiddenMass (paretoMeasure l α) x ≤ y} =
        {x | y < sampleHiddenMass (paretoMeasure l α) x}ᶜ := by ext x; simp
    rw [he, measureReal_compl
      (measurableSet_lt measurable_const (measurable_sampleHiddenMass _)),
      probReal_univ, paretoHiddenMass_tail_gt hl hα (lt_of_not_ge hy0) (le_of_not_ge hy1)]
    rfl

/-- The source's explicit sample-survival ratio has that same actual CDF,
by its almost-sure identification with the population hidden mass. -/
theorem paretoSampleSurvivalRatio_cdf {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) (y : ℝ) :
    (iidSampleLaw n (paretoMeasure l α)).real {x | (l / sampleMaximum x) ^ α ≤ y} =
      if y ≤ 0 then 0 else if 1 ≤ y then 1 else paretoSampleSurvivalRatioCDF n y := by
  have he : {x : Fin n → ℝ | (l / sampleMaximum x) ^ α ≤ y} =ᵐ[
      iidSampleLaw n (paretoMeasure l α)] {x | sampleHiddenMass (paretoMeasure l α) x ≤ y} := by
    filter_upwards [sampleHiddenMass_pareto_eq (n := n) hl hα] with x hx
    simp only [hx]
  rw [measureReal_congr he, paretoHiddenMass_cdf hl hα]

end TailOptionPricing
