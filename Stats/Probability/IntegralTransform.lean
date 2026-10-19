module

/-
  The actual probability integral transform as an equality of measures.
  Source: arXiv:1907.11162v3, Appendix B. Uniform means restricted Lebesgue
  measure on (0,1), identified with the supported normalized Beta(1,1) measure.
-/
public import Stats.Probability.CDFTransform
public import Stats.HiddenMoments.BetaKernel

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The pushforward by a continuous actual CDF is Beta(1,1),
the uniform law (arXiv:1907.11162v3, Appendix B). -/
theorem cdfTransform_map_beta (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) :
    ν.map (cdf ν : ℝ → ℝ) = betaMeasure 1 1 := by
  let : IsProbabilityMeasure (betaMeasure 1 1) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  apply Measure.ext_of_Iic
  intro q
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [Measure.map_apply hc.measurable measurableSet_Iic]
  change ν.real {x : ℝ | cdf ν x ≤ q} = (betaMeasure 1 1).real (Iic q)
  have hb := betaMeasure_one_nat_cdf (n := 1) (by norm_num) q
  norm_num only [Nat.cast_one, paretoSampleSurvivalRatioCDF, pow_one] at hb
  rw [hb]
  split_ifs with hq0 hq1
  · by_cases hq : q = 0
    · rw [hq, cdfTransform_probability_le ν hc (by norm_num) (by norm_num)]
    · have he : {x : ℝ | cdf ν x ≤ q} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hx
        exact hq (le_antisymm hq0 ((cdf_nonneg ν x).trans hx))
      rw [he, measureReal_empty]
  · have he : {x : ℝ | cdf ν x ≤ q} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (cdf_le_one ν x).trans hq1
    rw [he, probReal_univ]
  · rw [cdfTransform_probability_le ν hc (le_of_not_ge hq0) (lt_of_not_ge hq1)]
    ring

/-- For a measurable variable on any probability space, its actual CDF
transform has the uniform Beta(1,1) law (arXiv:1907.11162v3, Appendix B). -/
theorem cdfTransform_comp_map_beta {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hc : Continuous (cdf (μ.map X) : ℝ → ℝ)) :
    μ.map (fun ω => cdf (μ.map X) (X ω)) = betaMeasure 1 1 := by
  let : IsProbabilityMeasure (μ.map X) := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr
    inferInstance
  change μ.map ((cdf (μ.map X) : ℝ → ℝ) ∘ X) = _
  rw [← Measure.map_map hc.measurable hX, cdfTransform_map_beta _ hc]

/-- Beta(1,1) is precisely Lebesgue measure restricted to the unit interval.
The endpoints have zero Lebesgue mass, so the open support represents the uniform law. -/
theorem betaMeasure_one_one_eq_restrict : betaMeasure 1 1 = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hd : betaPDF 1 1 = (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ENNReal)) := by
    funext x
    have h := betaPDFReal_one_nat_eq 1 (by norm_num) x
    norm_num [paretoSampleSurvivalRatioPDF] at h
    rw [betaPDF, h]
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [hx]
  rw [betaMeasure, hd]
  simpa only [Pi.one_def] using
    (withDensity_indicator_one (μ := (volume : Measure ℝ)) measurableSet_Ioo)

/-- The literal uniform-measure formulation of the probability integral
transform (arXiv:1907.11162v3, Appendix B). The CDF belongs to the actual law of X. -/
theorem probabilityIntegralTransform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hc : Continuous (cdf (μ.map X) : ℝ → ℝ)) :
    μ.map (fun ω => cdf (μ.map X) (X ω)) = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [cdfTransform_comp_map_beta μ hX hc, betaMeasure_one_one_eq_restrict]

end TailOptionPricing
