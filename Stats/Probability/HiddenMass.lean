module

/-
  The actual population mass beyond an observed sample maximum.
  This is the zeroth hidden moment of arXiv:2004.05894v1, Remark 1.
  It is evaluated from the marginal measure, rather than defined by
  a proposed Beta/exponential formula.
-/
public import Stats.Probability.SampleMaximum
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Population probability beyond the observed maximum. -/
noncomputable def sampleHiddenMass {n : ℕ} [NeZero n] (ν : Measure ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ν.real (Ioi (sampleMaximum x))

theorem sampleHiddenMass_nonneg {n : ℕ} [NeZero n] (ν : Measure ℝ) (x : Fin n → ℝ) :
    0 ≤ sampleHiddenMass ν x := measureReal_nonneg

theorem sampleHiddenMass_le_one {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : Fin n → ℝ) : sampleHiddenMass ν x ≤ 1 :=
  measureReal_le_one

/-- Relation to the actual marginal CDF, including atoms. -/
theorem sampleHiddenMass_eq_one_sub_cdf {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : Fin n → ℝ) :
    sampleHiddenMass ν x = 1 - cdf ν (sampleMaximum x) := by
  rw [cdf_eq_real]
  unfold sampleHiddenMass
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]

theorem measurable_sampleHiddenMass {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    Measurable (sampleHiddenMass ν : (Fin n → ℝ) → ℝ) := by
  have he : (sampleHiddenMass ν : (Fin n → ℝ) → ℝ) =
      fun x => 1 - cdf ν (sampleMaximum x) :=
    funext (sampleHiddenMass_eq_one_sub_cdf ν)
  rw [he]
  exact measurable_const.sub ((monotone_cdf ν).measurable.comp measurable_sampleMaximum)

/-- The genuine hidden mass is integrable under its actual sample law,
without moment assumptions on the sampled values. -/
theorem sampleHiddenMass_integrable {n : ℕ} [NeZero n] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    Integrable (sampleHiddenMass ν : (Fin n → ℝ) → ℝ) (iidSampleLaw n ν) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_sampleHiddenMass ν).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sampleHiddenMass_nonneg ν x)]
    exact sampleHiddenMass_le_one ν x

end TailOptionPricing
