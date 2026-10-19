module

/-
  An actual independent random-scale Gaussian model for
  arXiv:1907.11162v3, Remark 1. The scale has two equally likely positive
  values. The corrected Definition 5 payoff gap strictly increases
  relative to the Gaussian at the mean scale when those values differ.
-/
public import Stats.Probability.EqualMixture
public import Stats.BinaryForecasts.GaussianGap

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual equal mixture of centered Gaussians, representing the
two-point scale uncertainty specialization of Remark 1. -/
noncomputable def gaussianScaleMixture (a b : ℝ) : Measure ℝ :=
  equalMixture (gaussianScaleLaw a) (gaussianScaleLaw b)

instance gaussianScaleMixture_probability (a b : ℝ) :
    IsProbabilityMeasure (gaussianScaleMixture a b) := by
  unfold gaussianScaleMixture
  infer_instance

/-- A genuine latent-parameter model: sample a scale from two equal
Dirac masses independently of a standard Gaussian, then multiply.
Its resulting law is the actual Gaussian mixture, not a moment proxy. -/
theorem gaussianScaleMixture_eq_parameter_model (a b : ℝ) :
    ((equalMixture (Measure.dirac a) (Measure.dirac b)).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => p.1 * p.2) = gaussianScaleMixture a b := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  rw [equalMixture_prod, equalMixture_map _ _ hm, Measure.dirac_prod,
    Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left,
    Measure.map_map hm measurable_prodMk_left]
  rfl

/-- The uncertain scale's actual mean is the scale used for the
baseline Gaussian in the corrected Jensen comparison (Remark 1). -/
theorem gaussianScaleMixture_parameter_mean (a b : ℝ) :
    (∫ s : ℝ, s ∂equalMixture (Measure.dirac a) (Measure.dirac b)) = (a + b) / 2 := by
  rw [equalMixture_integral (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp only [integral_dirac]

/-- Actual observations from the mixture are L1 for all real scales. -/
theorem gaussianScaleMixture_integrable_id (a b : ℝ) :
    Integrable (fun x : ℝ => x) (gaussianScaleMixture a b) := by
  rw [gaussianScaleMixture, equalMixture_integrable_iff]
  exact ⟨gaussianScaleLaw_integrable_id a, gaussianScaleLaw_integrable_id b⟩

/-- Actual mixture survival on the positive-scale source domain. -/
theorem gaussianScaleMixture_real_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (K : ℝ) :
    (gaussianScaleMixture a b).real (Ioi K) =
      ((1 - stdNormalCdf (K / a)) + (1 - stdNormalCdf (K / b))) / 2 := by
  rw [gaussianScaleMixture, equalMixture_real, gaussianScaleLaw_real_Ioi ha,
    gaussianScaleLaw_real_Ioi hb]

/-- Actual mixture tail moment, computed from independently proved
component L1 and actual Gaussian tail moments. -/
theorem gaussianScaleMixture_tail_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (K : ℝ) :
    (∫ x in Ioi K, x ∂gaussianScaleMixture a b) =
      (a * gaussianPDFReal 0 1 (K / a) + b * gaussianPDFReal 0 1 (K / b)) / 2 := by
  rw [gaussianScaleMixture, equalMixture_setIntegral
    (gaussianScaleLaw_integrable_id a).integrableOn
    (gaussianScaleLaw_integrable_id b).integrableOn,
    gaussianScaleLaw_tail_mean ha, gaussianScaleLaw_tail_mean hb]

/-- Definition 5's actual gap under the uncertain-scale population. -/
noncomputable def gaussianMixturePayoffGap (K a b : ℝ) : ℝ :=
  (∫ x in Ioi K, x ∂gaussianScaleMixture a b) -
    K * (gaussianScaleMixture a b).real (Ioi K)

/-- The mixture gap is an actual restricted excess expectation. -/
theorem gaussianMixturePayoffGap_eq_integral_excess (K a b : ℝ) :
    gaussianMixturePayoffGap K a b = ∫ x in Ioi K, x - K ∂gaussianScaleMixture a b :=
  tailPayoff_gap_eq_integral _ (gaussianScaleMixture_integrable_id a b).integrableOn

/-- Mixture-law bridge for Remark 1: actual payoff discrepancies average
because actual probability and integrable tail moments average. -/
theorem gaussianMixturePayoffGap_eq_average (K a b : ℝ) :
    gaussianMixturePayoffGap K a b = (gaussianPayoffGap K a + gaussianPayoffGap K b) / 2 := by
  rw [gaussianMixturePayoffGap, gaussianScaleMixture, equalMixture_setIntegral
    (gaussianScaleLaw_integrable_id a).integrableOn
    (gaussianScaleLaw_integrable_id b).integrableOn, equalMixture_real]
  simp only [gaussianPayoffGap]
  ring

/-- Correct actual-law form of Remark 1 for two equally likely distinct
positive Gaussian scales and positive threshold. Definition 5's threshold
factor is retained, correcting the omitted K in the source's Eq. 8 proof. -/
theorem gaussianMixturePayoffGap_gt_mean_scale {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    gaussianPayoffGap K ((a + b) / 2) < gaussianMixturePayoffGap K a b := by
  rw [gaussianMixturePayoffGap_eq_average]
  exact gaussianPayoffGap_midpoint_lt hK ha hb hab

example : IsProbabilityMeasure (gaussianScaleMixture 3 7) := inferInstance

example : ((equalMixture (Measure.dirac (3 : ℝ)) (Measure.dirac 7)).prod
    (gaussianReal 0 1)).map (fun p : ℝ × ℝ => p.1 * p.2) = gaussianScaleMixture 3 7 :=
  gaussianScaleMixture_eq_parameter_model _ _

example : (∫ s : ℝ, s ∂equalMixture (Measure.dirac 3) (Measure.dirac 7)) = 5 := by
  rw [gaussianScaleMixture_parameter_mean]
  norm_num

example : Integrable (fun x : ℝ => x) (gaussianScaleMixture 3 7) :=
  gaussianScaleMixture_integrable_id _ _

example : (gaussianScaleMixture 3 7).real (Ioi 3) =
    ((1 - stdNormalCdf (3 / 3)) + (1 - stdNormalCdf (3 / 7))) / 2 :=
  gaussianScaleMixture_real_Ioi (by norm_num) (by norm_num) _

example : (∫ x in Ioi (3 : ℝ), x ∂gaussianScaleMixture 3 7) =
    (3 * gaussianPDFReal 0 1 (3 / 3) + 7 * gaussianPDFReal 0 1 (3 / 7)) / 2 :=
  gaussianScaleMixture_tail_mean (by norm_num) (by norm_num) _

example : gaussianPayoffGap 3 5 < gaussianMixturePayoffGap 3 3 7 := by
  have h := gaussianMixturePayoffGap_gt_mean_scale (K := 3) (a := 3) (b := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

#print axioms gaussianScaleMixture_eq_parameter_model
#print axioms gaussianScaleMixture_tail_mean
#print axioms gaussianMixturePayoffGap_eq_average
#print axioms gaussianMixturePayoffGap_gt_mean_scale

end TailOptionPricing
