module

/-
  The actual finite-sample hidden-mass law cannot be exponential, contrary
  to the literal assertion in arXiv:2004.05894v1, Remark 1. The actual
  probability mass is bounded by one; an exponential law has a positive
  probability of exceeding one.
-/
public import Stats.HiddenMoments.Mean
public import Stats.Probability.Exponential

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- For every nonempty finite iid Pareto sample, the actual hidden
probability mass has a different law from the printed Exp(n) distribution. -/
theorem paretoHiddenMass_not_exponential {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 0 < α) :
    (iidSampleLaw n (paretoMeasure l α)).map (sampleHiddenMass (paretoMeasure l α)) ≠
      expMeasure (n : ℝ) := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  have hzero : ((iidSampleLaw n (paretoMeasure l α)).map
      (sampleHiddenMass (paretoMeasure l α))).real (Ioi 1) = 0 := by
    rw [Measure.real, Measure.map_apply (measurable_sampleHiddenMass _) measurableSet_Ioi]
    have he : (sampleHiddenMass (paretoMeasure l α) : (Fin n → ℝ) → ℝ) ⁻¹' Ioi 1 = ∅ := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false]
      exact not_lt.mpr (sampleHiddenMass_le_one _ x)
    rw [he, measure_empty, ENNReal.toReal_zero]
  intro he
  rw [he, expMeasure_real_Ioi (Nat.cast_pos.mpr (NeZero.pos n))] at hzero
  norm_num at hzero

end TailOptionPricing
