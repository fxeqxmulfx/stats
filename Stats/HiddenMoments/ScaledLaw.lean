module

/-
  Actual scaled hidden-mass probability measures for the correction to
  arXiv:2004.05894v1, Remark 1. Index n uses n+1 observations, so every
  maximum is nonempty. The limit law is Mathlib's actual exponential measure.
-/
public import Stats.HiddenMoments.ContinuousLaw
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The pushforward of the actual iid sample law by `(n+1)*H_(n+1)`.
The definition uses observations and the population tail probability, not a Beta formula. -/
noncomputable def scaledHiddenMassLaw (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨(iidSampleLaw (n + 1) ν).map (fun x : Fin (n + 1) → ℝ =>
    ((n + 1 : ℕ) : ℝ) * sampleHiddenMass ν x),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_const.mul (measurable_sampleHiddenMass ν)).aemeasurable).mpr inferInstance⟩

/-- The normalized actual exponential measure of rate one. -/
noncomputable def unitExponentialLaw : ProbabilityMeasure ℝ :=
  ⟨expMeasure 1, isProbabilityMeasure_expMeasure (by norm_num)⟩

/-- Exact CDF of the scaled actual hidden mass via its proved Beta law
(arXiv:2004.05894v1, Remark 1 correction). The statement includes all real thresholds. -/
theorem scaledHiddenMassLaw_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) (n : ℕ) (t : ℝ) :
    cdf (scaledHiddenMassLaw ν n : Measure ℝ) t =
      (betaMeasure 1 (n + 1 : ℕ)).real (Iic (t / ((n + 1 : ℕ) : ℝ))) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  rw [cdf_eq_real]
  change ((iidSampleLaw (n + 1) ν).map (fun x : Fin (n + 1) → ℝ =>
    ((n + 1 : ℕ) : ℝ) * sampleHiddenMass ν x)).real (Iic t) = _
  have hmeas : Measurable (fun x : Fin (n + 1) → ℝ =>
      ((n + 1 : ℕ) : ℝ) * sampleHiddenMass ν x) :=
    measurable_const.mul (measurable_sampleHiddenMass ν)
  rw [measureReal_def, Measure.map_apply hmeas measurableSet_Iic]
  change (iidSampleLaw (n + 1) ν).real
    {x | ((n + 1 : ℕ) : ℝ) * sampleHiddenMass ν x ≤ t} = _
  have he : {x : Fin (n + 1) → ℝ | ((n + 1 : ℕ) : ℝ) * sampleHiddenMass ν x ≤ t} =
      {x | sampleHiddenMass ν x ≤ t / ((n + 1 : ℕ) : ℝ)} := by
    ext x
    simp only [mem_ofPred_eq, le_div_iff₀ hn]
    rw [mul_comm]
  rw [he]
  have hm := congrArg (fun ρ : Measure ℝ => ρ.real (Iic (t / ((n + 1 : ℕ) : ℝ))))
    (continuousHiddenMass_map_beta (n := n + 1) ν hc)
  rw [measureReal_def, Measure.map_apply (measurable_sampleHiddenMass ν) measurableSet_Iic] at hm
  exact hm

end TailOptionPricing
