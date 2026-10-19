module

/-
  Expected actual population probability beyond an iid Pareto maximum.
  This proves the finite-sample correction 1/(n+1) to the 1/n printed
  in arXiv:2004.05894v1, abstract and Remark 1. The integral is under
  the actual product sample law, with integrability proved separately.
-/
public import Stats.HiddenMoments.SurvivalMass

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

theorem integral_one_sub_pow (n : ℕ) :
    (∫ y in (0 : ℝ)..1, (1 - y) ^ n) = 1 / ((n : ℝ) + 1) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hderiv (y : ℝ) :
      HasDerivAt (fun y : ℝ => -(1 - y) ^ (n + 1) / ((n : ℝ) + 1)) ((1 - y) ^ n) y := by
    have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) y :=
      (hasDerivAt_id y).const_sub 1
    have h := ((hb.pow (n + 1)).neg).div_const ((n : ℝ) + 1)
    convert h using 1
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    (Continuous.intervalIntegrable (by continuity) _ _)]
  simp
  ring

/-- The expected genuine zeroth hidden moment is `1/(n+1)`, for any
positive Pareto scale/index and any nonempty finite iid sample.
This corrects the literal finite-sample `1/n` in the source's Remark 1. -/
theorem paretoHiddenMass_mean {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    (∫ x : Fin n → ℝ, sampleHiddenMass (paretoMeasure l α) x
      ∂iidSampleLaw n (paretoMeasure l α)) = 1 / ((n : ℝ) + 1) := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  rw [(sampleHiddenMass_integrable (n := n) (paretoMeasure l α)).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall (sampleHiddenMass_nonneg _))
    (Filter.Eventually.of_forall (sampleHiddenMass_le_one _))]
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun y hy => paretoHiddenMass_tail_ge hl hα hy.1 hy.2)]
  rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1), integral_one_sub_pow]

example : (∫ x : Fin 2 → ℝ, sampleHiddenMass (paretoMeasure 1 2) x
    ∂iidSampleLaw 2 (paretoMeasure 1 2)) = 1 / 3 := by
  rw [paretoHiddenMass_mean (by norm_num) (by norm_num)]
  norm_num

end TailOptionPricing
