module

/-
  Distribution-free hidden probability mass for any law with a continuous CDF.
  This extends arXiv:2004.05894v1, Remark 1, beyond the power-law case.
  The exact finite-sample law is Beta(1,n); atoms require separate treatment.
-/
public import Stats.Probability.CDFTransform
public import Stats.HiddenMoments.BetaLaw
public import Stats.HiddenMoments.Mean

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual maximum transformed by the continuous population CDF
has CDF `q^n` on [0,1), allowing flat regions of the population CDF. -/
theorem sampleMaximum_cdf_transform {n : ℕ} [NeZero n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (iidSampleLaw n ν).real {x | cdf ν (sampleMaximum x) ≤ q} = q ^ n := by
  by_cases hne : {x : ℝ | cdf ν x ≤ q}.Nonempty
  · obtain ⟨t, ht, hS⟩ := exists_cdf_sublevel_boundary ν hc hq1 hne
    have he : {x : Fin n → ℝ | cdf ν (sampleMaximum x) ≤ q} =
        {x | sampleMaximum x ≤ t} := by
      ext x
      exact Set.ext_iff.mp hS (sampleMaximum x)
    rw [he, sampleMaximum_cdf, ← cdf_eq_real ν t, ht]
  · have hq : q = 0 := by
      by_contra hq
      have hpos := lt_of_le_of_ne hq0 (Ne.symm hq)
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually_lt_const hpos).exists
      exact hne ⟨a, ha.le⟩
    have he : {x : Fin n → ℝ | cdf ν (sampleMaximum x) ≤ q} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hx
      exact hne ⟨sampleMaximum x, hx⟩
    rw [he, measureReal_empty, hq, zero_pow (NeZero.ne n)]

/-- Closed upper tails of the actual hidden probability mass for every
continuous-CDF population, extending arXiv:2004.05894v1, Remark 1. -/
theorem continuousHiddenMass_tail_ge {n : ℕ} [NeZero n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    (iidSampleLaw n ν).real {x | y ≤ sampleHiddenMass ν x} = (1 - y) ^ n := by
  have he : {x : Fin n → ℝ | y ≤ sampleHiddenMass ν x} =
      {x | cdf ν (sampleMaximum x) ≤ 1 - y} := by
    ext x
    simp only [mem_ofPred_eq, sampleHiddenMass_eq_one_sub_cdf]
    constructor <;> intro hx <;> linarith
  rw [he, sampleMaximum_cdf_transform ν hc (by linarith) (by linarith)]

/-- Actual hidden probability mass has the supported Beta(1,n) law,
independent of the continuous-CDF population. This extends the power-law
parameter independence in arXiv:2004.05894v1, Remark 1. -/
theorem continuousHiddenMass_map_beta {n : ℕ} [NeZero n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) :
    (iidSampleLaw n ν).map (sampleHiddenMass ν) = betaMeasure 1 n := by
  let : IsProbabilityMeasure (paretoMeasure 1 2) :=
    instIsProbabilityMeasureParetoMeasure 1 2 (by norm_num) (by norm_num)
  rw [← paretoHiddenMass_map_beta (n := n) (l := 1) (a := 2) (by norm_num) (by norm_num)]
  apply Measure.ext_of_Ici
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [Measure.map_apply (measurable_sampleHiddenMass _) measurableSet_Ici,
    Measure.map_apply (measurable_sampleHiddenMass _) measurableSet_Ici]
  change (iidSampleLaw n ν).real {x | y ≤ sampleHiddenMass ν x} =
    (iidSampleLaw n (paretoMeasure 1 2)).real {x | y ≤ sampleHiddenMass (paretoMeasure 1 2) x}
  by_cases hy0 : y ≤ 0
  · have he (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
        {x : Fin n → ℝ | y ≤ sampleHiddenMass ρ x} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hy0.trans (sampleHiddenMass_nonneg _ _)
    rw [he ν, he (paretoMeasure 1 2), probReal_univ, probReal_univ]
  · by_cases hy1 : y ≤ 1
    · rw [continuousHiddenMass_tail_ge ν hc (lt_of_not_ge hy0) hy1,
        paretoHiddenMass_tail_ge (by norm_num) (by norm_num) (lt_of_not_ge hy0) hy1]
    · have he (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
          {x : Fin n → ℝ | y ≤ sampleHiddenMass ρ x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hx
        exact hy1 (hx.trans (sampleHiddenMass_le_one _ _))
      rw [he ν, he (paretoMeasure 1 2), measureReal_empty, measureReal_empty]

/-- The true expected hidden mass is distribution-free for continuous-CDF
populations. Its exact value corrects `1/n` in arXiv:2004.05894v1, Remark 1. -/
theorem continuousHiddenMass_mean {n : ℕ} [NeZero n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) :
    (∫ x : Fin n → ℝ, sampleHiddenMass ν x ∂iidSampleLaw n ν) = 1 / ((n : ℝ) + 1) := by
  rw [(sampleHiddenMass_integrable (n := n) ν).integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall (sampleHiddenMass_nonneg _))
    (Filter.Eventually.of_forall (sampleHiddenMass_le_one _))]
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun y hy => continuousHiddenMass_tail_ge ν hc hy.1 hy.2)]
  rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1), integral_one_sub_pow]

end TailOptionPricing
