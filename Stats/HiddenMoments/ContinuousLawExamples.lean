module

/-
  Actual exponential-law witnesses for the probability integral transform
  (arXiv:1907.11162v3, Appendix B) and the continuous-law extension of
  hidden-mass parameter independence (arXiv:2004.05894v1, Remark 1).
-/
public import Stats.HiddenMoments.ContinuousLaw
public import Stats.Probability.IntegralTransform
public import Mathlib.Probability.Distributions.Exponential

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual exponential CDF is continuous, including its support boundary.
This witnesses the continuity condition in the two papers' transform claims. -/
theorem continuous_expMeasure_cdf {r : ℝ} (hr : 0 < r) :
    Continuous (cdf (expMeasure r) : ℝ → ℝ) := by
  have he : (cdf (expMeasure r) : ℝ → ℝ) = fun x : ℝ => 1 - Real.exp (-(r * max 0 x)) := by
    funext x
    rw [cdf_expMeasure_eq hr]
    split_ifs with hx
    · rw [max_eq_right hx]
    · rw [max_eq_left (le_of_not_ge hx)]
      norm_num
  rw [he]
  fun_prop

local notation "ν" => expMeasure (1 : ℝ)
local notation "μ" => iidSampleLaw 2 ν

local instance continuousLawExampleLaw_probability : IsProbabilityMeasure ν :=
  isProbabilityMeasure_expMeasure (by norm_num)

example : Continuous (cdf ν : ℝ → ℝ) := continuous_expMeasure_cdf (by norm_num)

example : ∃ t : ℝ, cdf ν t = 1 / 2 ∧ {x : ℝ | cdf ν x ≤ 1 / 2} = Iic t := by
  apply exists_cdf_sublevel_boundary ν (continuous_expMeasure_cdf (by norm_num)) (by norm_num)
  refine ⟨0, ?_⟩
  change cdf ν 0 ≤ 1 / 2
  rw [cdf_expMeasure_eq (by norm_num)]
  norm_num

example : (ν).real {x : ℝ | cdf ν x ≤ 1 / 2} = 1 / 2 :=
  cdfTransform_probability_le ν (continuous_expMeasure_cdf (by norm_num))
    (by norm_num) (by norm_num)

-- The zero endpoint is included, despite the CDF's flat negative half-line.
example : (ν).real {x : ℝ | cdf ν x ≤ 0} = 0 :=
  cdfTransform_probability_le ν (continuous_expMeasure_cdf (by norm_num))
    (by norm_num) (by norm_num)

example : (ν).map (cdf ν : ℝ → ℝ) = betaMeasure 1 1 :=
  cdfTransform_map_beta ν (continuous_expMeasure_cdf (by norm_num))

example : (ν).map (cdf ν : ℝ → ℝ) = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [cdfTransform_map_beta ν (continuous_expMeasure_cdf (by norm_num)),
    betaMeasure_one_one_eq_restrict]

example : (μ).real {x | cdf ν (sampleMaximum x) ≤ 1 / 2} = 1 / 4 := by
  rw [sampleMaximum_cdf_transform ν (continuous_expMeasure_cdf (by norm_num))
    (by norm_num) (by norm_num)]
  norm_num

example : (μ).real {x | 1 / 4 ≤ sampleHiddenMass ν x} = 9 / 16 := by
  rw [continuousHiddenMass_tail_ge ν (continuous_expMeasure_cdf (by norm_num))
    (by norm_num) (by norm_num)]
  norm_num

example : (μ).map (sampleHiddenMass ν) = betaMeasure 1 2 := by
  have h := continuousHiddenMass_map_beta (n := 2) ν (continuous_expMeasure_cdf (by norm_num))
  norm_num at h
  exact h

example : (∫ x : Fin 2 → ℝ, sampleHiddenMass ν x ∂μ) = 1 / 3 := by
  rw [continuousHiddenMass_mean ν (continuous_expMeasure_cdf (by norm_num))]
  norm_num

-- A nonconstant observation on an actual product probability space.
example : (μ).map (fun x : Fin 2 → ℝ =>
    cdf ((μ).map (fun z : Fin 2 → ℝ => z 0)) (x 0)) = betaMeasure 1 1 := by
  have hmap : (μ).map (fun z : Fin 2 → ℝ => z 0) = ν := by
    simpa using (iidSample_identDistrib 2 ν 0).map_eq
  apply cdfTransform_comp_map_beta μ (measurable_pi_apply 0)
  rw [hmap]
  exact continuous_expMeasure_cdf (by norm_num)

example : (μ).map (fun x : Fin 2 → ℝ =>
    cdf ((μ).map (fun z : Fin 2 → ℝ => z 0)) (x 0)) = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hmap : (μ).map (fun z : Fin 2 → ℝ => z 0) = ν := by
    simpa using (iidSample_identDistrib 2 ν 0).map_eq
  apply probabilityIntegralTransform μ (measurable_pi_apply 0)
  rw [hmap]
  exact continuous_expMeasure_cdf (by norm_num)

#print axioms exists_cdf_sublevel_boundary
#print axioms probabilityIntegralTransform
#print axioms continuousHiddenMass_map_beta
#print axioms continuousHiddenMass_mean

end TailOptionPricing
