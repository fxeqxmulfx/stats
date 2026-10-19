module

/-
  Actual nondegenerate Pareto and Beta witnesses for the exact finite-sample
  correction to arXiv:2004.05894v1, Proposition 1, Eq. 2 and Remark 1.
  These certify law normalization, integrability and concrete expectations.
-/
public import Stats.HiddenMoments.MomentMean
public import Stats.HiddenMoments.MomentAsymptotic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

local notation "ν" => paretoMeasure (1 : ℝ) 2
local notation "μ" => iidSampleLaw 2 ν

local instance momentMeanExampleLaw_probability : IsProbabilityMeasure ν :=
  instIsProbabilityMeasureParetoMeasure 1 2 (by norm_num) (by norm_num)

example : 0 ≤ betaPDFReal 1 2 (1 / 4) := betaPDFReal_nonneg (by norm_num) (by norm_num) _

example : (∫ y : ℝ, betaPDFReal 1 2 y) = 1 :=
  integral_betaPDFReal (by norm_num) (by norm_num)

example : betaPDFReal 1 2 (1 / 4) * (1 / 4 : ℝ) ^ (1 : ℝ) =
    (ProbabilityTheory.beta (1 + 1) 2 / ProbabilityTheory.beta 1 2) *
      betaPDFReal (1 + 1) 2 (1 / 4) :=
  betaPDFReal_mul_rpow (by norm_num) (by norm_num) (by norm_num) _

example : Integrable (fun y : ℝ => y ^ (-1 / 2 : ℝ)) (betaMeasure 1 2) :=
  betaMeasure_integrable_rpow (by norm_num) (by norm_num) (by norm_num)

example : (∫ y : ℝ, y ^ (1 : ℝ) ∂betaMeasure 1 2) = 1 / 3 := by
  rw [betaMeasure_integral_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num [ProbabilityTheory.beta, Real.Gamma_nat_eq_factorial]

example : ProbabilityTheory.beta 1 2 = 1 / 2 := beta_one_nat 2 (by norm_num)

example : betaPDFReal 1 2 (1 / 4) = 3 / 2 := by
  have h := betaPDFReal_one_nat_eq 2 (by norm_num) (1 / 4)
  norm_num [paretoSampleSurvivalRatioPDF] at h
  exact h

example : (∫ y in Ioc (0 : ℝ) (1 / 4), paretoSampleSurvivalRatioPDF 2 y) = 7 / 16 := by
  rw [paretoSampleSurvivalRatioPDF_integral (by norm_num)]
  norm_num [paretoSampleSurvivalRatioCDF]

example : (betaMeasure 1 2).real (Iic (1 / 4)) = 7 / 16 := by
  have h := betaMeasure_one_nat_cdf (n := 2) (by norm_num) (1 / 4)
  norm_num [paretoSampleSurvivalRatioCDF] at h
  exact h

example : (μ).map (sampleHiddenMass ν) = betaMeasure 1 2 :=
  paretoHiddenMass_map_beta (by norm_num) (by norm_num)

example : IdentDistrib (sampleHiddenMass ν) (id : ℝ → ℝ) μ (betaMeasure 1 2) :=
  paretoHiddenMass_identDistrib_beta (by norm_num) (by norm_num)

example : Integrable (fun x : Fin 2 → ℝ => (sampleHiddenMass ν x) ^ (-1 / 2 : ℝ)) μ :=
  paretoHiddenMass_integrable_rpow (by norm_num) (by norm_num) (by norm_num)

example : (∫ x : Fin 2 → ℝ, (sampleHiddenMass ν x) ^ (1 : ℝ) ∂μ) = 1 / 3 := by
  rw [paretoHiddenMass_integral_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num [ProbabilityTheory.beta, Real.Gamma_nat_eq_factorial]

example : ∀ᵐ x ∂μ, sampleHiddenMoment ν 1 x = 2 * (sampleHiddenMass ν x) ^ (1 / 2 : ℝ) := by
  have h := sampleHiddenMoment_pareto_eq_hiddenMass_rpow (n := 2) (l := 1) (a := 2)
    (p := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : (μ).map (sampleHiddenMoment ν 1) =
    (betaMeasure 1 2).map (fun y : ℝ => 2 * y ^ (1 / 2 : ℝ)) := by
  have h := paretoHiddenMoment_map_beta_rpow (n := 2) (l := 1) (a := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : (∫ x : Fin 2 → ℝ, sampleHiddenMoment ν 1 x ∂μ) =
    2 * (ProbabilityTheory.beta (3 / 2) 2 / ProbabilityTheory.beta 1 2) := by
  have h := paretoHiddenMoment_mean_beta (n := 2) (l := 1) (a := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : (∫ x : Fin 2 → ℝ, sampleHiddenMoment ν (-2) x ∂μ) = 1 / 12 := by
  rw [paretoHiddenMoment_mean_gamma (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_nat_eq_factorial]

example : (∫ x : Fin 1 → ℝ, sampleHiddenMoment ν 1 x ∂iidSampleLaw 1 ν) = 4 / 3 := by
  rw [paretoHiddenMoment_mean_gamma (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  have hg : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h1 := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  have h2 := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  norm_num at h1 h2
  rw [h2, h1]
  field_simp
  norm_num

example : (∫ x : Fin 2 → ℝ, sampleHiddenMoment ν 1 x ∂μ) = 16 / 15 := by
  rw [paretoHiddenMoment_mean_gamma (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_nat_eq_factorial]
  have hg : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h1 := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  have h2 := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  have h3 := Real.Gamma_add_one (s := (5 / 2 : ℝ)) (by norm_num)
  norm_num at h1 h2 h3
  rw [h3, h2, h1]
  field_simp
  norm_num

#print axioms betaMeasure_integrable_rpow
#print axioms paretoHiddenMass_map_beta
#print axioms paretoHiddenMoment_map_beta_rpow
#print axioms paretoHiddenMoment_mean_gamma

example : Real.GammaSeq (1 / 2) 2 =
    (2 : ℝ) ^ (1 / 2 : ℝ) * ProbabilityTheory.beta (1 / 2) 3 := by
  have h := realGammaSeq_eq_beta (r := 1 / 2) (by norm_num) 2
  norm_num at h
  exact h

example : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
    ∫ x : Fin (n + 1) → ℝ, sampleHiddenMoment ν 1 x ∂iidSampleLaw (n + 1) ν)
      atTop (𝓝 (Real.Gamma (1 / 2))) := by
  convert paretoHiddenMoment_mean_scaled_tendsto (l := 1) (a := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

example : Tendsto (fun n : ℕ =>
    (∫ x : Fin (n + 1) → ℝ, sampleHiddenMoment ν 1 x ∂iidSampleLaw (n + 1) ν) /
      (((n + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * Real.Gamma (1 / 2))) atTop (𝓝 1) := by
  convert paretoHiddenMoment_mean_ratio_tendsto (l := 1) (a := 2) (p := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num

#print axioms paretoHiddenMoment_mean_scaled_tendsto
#print axioms paretoHiddenMoment_mean_ratio_tendsto

end TailOptionPricing
