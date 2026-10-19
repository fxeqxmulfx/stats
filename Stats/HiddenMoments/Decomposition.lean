module

/-
  Actual visible-plus-hidden population moments at the iid Pareto maximum.
  This assembles the opening decomposition of arXiv:2004.05894v1 and Eq. 2,
  with the moment integrability threshold and actual measurable samples.
-/
public import Stats.Pareto.Moments
public import Stats.HiddenMoments.Maximum
public import Stats.Probability.TruncatedMoments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The source's population moment split at the actual observed maximum.
It holds for every sample value; finite moments require `p < α`. -/
theorem paretoSample_moment_decomposition {n : ℕ} [NeZero n] {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) (x : Fin n → ℝ) :
    α * l ^ p / (α - p) = sampleVisibleMoment (paretoMeasure l α) p x +
      sampleHiddenMoment (paretoMeasure l α) p x := by
  rw [← paretoMeasure_integral_rpow hl hα hp]
  exact sampleMoment_decomposition _ _ ((paretoMeasure_integrable_rpow_iff hl hα).mpr hp) x

/-- The population hidden integral agrees with the density tail integral
almost surely. This equality of total integrals alone asserts no finiteness. -/
theorem sampleHiddenMoment_pareto_eq_tailMoment {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) (p : ℝ) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α),
      sampleHiddenMoment (paretoMeasure l α) p x = paretoTailMoment l α p (sampleMaximum x) := by
  filter_upwards [paretoSampleMaximum_ae_gt (n := n) hl hα] with x hx
  exact paretoMeasure_tailMoment hl hα p hx.le

/-- The visible moment is the source's unrescaled density integral from
the support boundary to the observed maximum. -/
theorem sampleVisibleMoment_pareto_density {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) (p : ℝ) (x : Fin n → ℝ) :
    sampleVisibleMoment (paretoMeasure l α) p x =
      ∫ s in Ioc l (sampleMaximum x), s ^ p * paretoDensity l α s := by
  unfold sampleVisibleMoment
  rw [paretoMeasure_setIntegral hl hα _ measurableSet_Iic]
  rfl

/-- Eq. 2 applied to the actual random threshold, with its support and
moment conditions derived from the actual sample and parameter domain. -/
theorem sampleHiddenMoment_pareto_closed_form {n : ℕ} [NeZero n] {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α),
      sampleHiddenMoment (paretoMeasure l α) p x =
        α * l ^ α * (sampleMaximum x) ^ (p - α) / (α - p) := by
  filter_upwards [sampleHiddenMoment_pareto_eq_tailMoment (n := n) hl hα p,
    paretoSampleMaximum_ae_gt (n := n) hl hα] with x he hx
  rw [he, paretoTailMoment_eq hl hp hx.le]

theorem paretoSample_hiddenMoment_integrable {n : ℕ} [NeZero n] {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) :
    Integrable (sampleHiddenMoment (paretoMeasure l α) p : (Fin n → ℝ) → ℝ)
      (iidSampleLaw n (paretoMeasure l α)) := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  exact sampleHiddenMoment_integrable _ _ ((paretoMeasure_integrable_rpow_iff hl hα).mpr hp)

theorem paretoSample_visibleMoment_integrable {n : ℕ} [NeZero n] {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) :
    Integrable (sampleVisibleMoment (paretoMeasure l α) p : (Fin n → ℝ) → ℝ)
      (iidSampleLaw n (paretoMeasure l α)) := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  exact sampleVisibleMoment_integrable _ _ ((paretoMeasure_integrable_rpow_iff hl hα).mpr hp)

/-- A corrected population-truncation claim: the visible integral is
strictly below the finite population moment almost surely. This concerns
the source's truncated population integral, not the arithmetic sample mean. -/
theorem paretoSample_visibleMoment_lt_population {n : ℕ} [NeZero n] {l α p : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hp : p < α) :
    ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α),
      sampleVisibleMoment (paretoMeasure l α) p x < α * l ^ p / (α - p) := by
  filter_upwards [sampleHiddenMoment_pareto_closed_form (n := n) hl hα hp,
    paretoSampleMaximum_ae_gt (n := n) hl hα] with x he hx
  have hpos : 0 < sampleHiddenMoment (paretoMeasure l α) p x := by
    rw [he]
    exact div_pos (mul_pos (mul_pos hα (Real.rpow_pos_of_pos hl _))
      (Real.rpow_pos_of_pos (hl.trans hx) _)) (sub_pos.mpr hp)
  linarith [paretoSample_moment_decomposition hl hα hp x]

end TailOptionPricing
