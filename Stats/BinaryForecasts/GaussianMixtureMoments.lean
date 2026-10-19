module

/-
  Actual moments and kurtosis of the independent two-point Gaussian
  scale mixture in arXiv:1907.11162v3, Remark 1. Also identifies the
  centered specialization of arXiv:1802.05495v3, Eq. 17, with genuine
  central moments. Positive distinct scales give kurtosis above three.
-/
public import Stats.BinaryForecasts.GaussianMixture
public import Stats.Probability.GaussianMoments
public import Stats.Kappa.GaussianMixture

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual Gaussian scale-family powers are L1 before moment evaluation. -/
theorem gaussianScaleLaw_integrable_pow (σ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianScaleLaw σ) := by
  rw [gaussianScaleLaw_eq]
  exact gaussianReal_integrable_pow _ _ _

/-- Actual mean of the centered scale law used in Remark 1. -/
theorem gaussianScaleLaw_mean (σ : ℝ) : (∫ x : ℝ, x ∂gaussianScaleLaw σ) = 0 := by
  rw [gaussianScaleLaw_eq, integral_id_gaussianReal]

/-- Actual second moment, with the independent L1 proof above. -/
theorem gaussianScaleLaw_moment_two (σ : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂gaussianScaleLaw σ) = σ ^ 2 := by
  rw [gaussianScaleLaw_eq, gaussianReal_zero_moment_two, NNReal.coe_mk]

/-- Actual fourth moment of each centered Gaussian component. -/
theorem gaussianScaleLaw_moment_four (σ : ℝ) :
    (∫ x : ℝ, x ^ 4 ∂gaussianScaleLaw σ) = 3 * σ ^ 4 := by
  rw [gaussianScaleLaw_eq, gaussianReal_zero_moment_four, NNReal.coe_mk]
  ring

/-- The baseline Gaussian has actual Pearson kurtosis three, for a
positive scale as in Remark 1. This uses its genuine central moments. -/
theorem gaussianScaleLaw_kurtosis {σ : ℝ} (hσ : 0 < σ) :
    centralMoment (fun x : ℝ => x) 4 (gaussianScaleLaw σ) /
      variance (fun x : ℝ => x) (gaussianScaleLaw σ) ^ 2 = 3 := by
  have hm : AEMeasurable (fun x : ℝ => x) (gaussianScaleLaw σ) := measurable_id.aemeasurable
  rw [variance_eq_integral hm, gaussianScaleLaw_mean]
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, gaussianScaleLaw_mean, sub_zero]
  rw [gaussianScaleLaw_moment_four, gaussianScaleLaw_moment_two]
  field_simp

/-- Every natural mixture moment is genuinely integrable. -/
theorem gaussianScaleMixture_integrable_pow (a b : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianScaleMixture a b) := by
  rw [gaussianScaleMixture, equalMixture_integrable_iff]
  exact ⟨gaussianScaleLaw_integrable_pow a n, gaussianScaleLaw_integrable_pow b n⟩

/-- Actual mixture mean; randomizing a centered scale keeps the mean zero. -/
theorem gaussianScaleMixture_mean (a b : ℝ) :
    (∫ x : ℝ, x ∂gaussianScaleMixture a b) = 0 := by
  rw [gaussianScaleMixture, equalMixture_integral (gaussianScaleLaw_integrable_id a)
    (gaussianScaleLaw_integrable_id b), gaussianScaleLaw_mean, gaussianScaleLaw_mean]
  norm_num

/-- Actual second mixture moment in Remark 1's two-point model. -/
theorem gaussianScaleMixture_moment_two (a b : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂gaussianScaleMixture a b) = (a ^ 2 + b ^ 2) / 2 := by
  rw [gaussianScaleMixture, equalMixture_integral (gaussianScaleLaw_integrable_pow a 2)
    (gaussianScaleLaw_integrable_pow b 2), gaussianScaleLaw_moment_two,
    gaussianScaleLaw_moment_two]

/-- Actual fourth mixture moment, rather than a moment proxy. -/
theorem gaussianScaleMixture_moment_four (a b : ℝ) :
    (∫ x : ℝ, x ^ 4 ∂gaussianScaleMixture a b) = 3 * (a ^ 4 + b ^ 4) / 2 := by
  rw [gaussianScaleMixture, equalMixture_integral (gaussianScaleLaw_integrable_pow a 4)
    (gaussianScaleLaw_integrable_pow b 4), gaussianScaleLaw_moment_four,
    gaussianScaleLaw_moment_four]
  ring

/-- Actual variance of the centered Gaussian scale mixture. -/
theorem gaussianScaleMixture_variance (a b : ℝ) :
    variance (fun x : ℝ => x) (gaussianScaleMixture a b) = (a ^ 2 + b ^ 2) / 2 := by
  have hm : AEMeasurable (fun x : ℝ => x) (gaussianScaleMixture a b) :=
    measurable_id.aemeasurable
  rw [variance_eq_integral hm, gaussianScaleMixture_mean]
  simp only [sub_zero]
  exact gaussianScaleMixture_moment_two _ _

/-- Actual fourth central moment for the source's common-center model. -/
theorem gaussianScaleMixture_centralMoment_four (a b : ℝ) :
    centralMoment (fun x : ℝ => x) 4 (gaussianScaleMixture a b) =
      3 * (a ^ 4 + b ^ 4) / 2 := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, gaussianScaleMixture_mean, sub_zero]
  exact gaussianScaleMixture_moment_four _ _

/-- Pearson kurtosis defined by actual central moments of the mixture,
as used in Remark 1; its closed expression is proved below. -/
noncomputable def gaussianScaleMixtureKurtosis (a b : ℝ) : ℝ :=
  centralMoment (fun x : ℝ => x) 4 (gaussianScaleMixture a b) /
    variance (fun x : ℝ => x) (gaussianScaleMixture a b) ^ 2

/-- Actual kurtosis formula under explicit nondegeneracy. This is the
common-center specialization of arXiv:1802.05495v3, Eq. 17. -/
theorem gaussianScaleMixtureKurtosis_eq {a b : ℝ} (h : 0 < a ^ 2 + b ^ 2) :
    gaussianScaleMixtureKurtosis a b = 6 * (a ^ 4 + b ^ 4) / (a ^ 2 + b ^ 2) ^ 2 := by
  rw [gaussianScaleMixtureKurtosis, gaussianScaleMixture_centralMoment_four,
    gaussianScaleMixture_variance]
  field_simp
  ring

/-- The earlier Eq. 17 scalar expression is now identified with actual
Pearson kurtosis for the centered, nondegenerate equal mixture. -/
theorem gaussianScaleMixtureKurtosis_eq_eq17 {a b : ℝ} (h : 0 < a ^ 2 + b ^ 2) :
    gaussianScaleMixtureKurtosis a b = gaussianMixtureKurtosis 0 0 a b := by
  rw [gaussianScaleMixtureKurtosis_eq h, gaussianMixtureKurtosis]
  field_simp
  nlinarith [sq_pos_of_pos h]

/-- Genuine higher kurtosis in Remark 1's independent two-point scale
model: positive distinct scales give actual Pearson kurtosis above 3. -/
theorem gaussianScaleMixtureKurtosis_gt_three {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    3 < gaussianScaleMixtureKurtosis a b := by
  have hs : 0 < a ^ 2 + b ^ 2 := by positivity
  have hd : a ^ 2 ≠ b ^ 2 := fun he => hab ((sq_eq_sq₀ ha.le hb.le).mp he)
  rw [gaussianScaleMixtureKurtosis_eq hs, lt_div_iff₀ (sq_pos_of_pos hs)]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hd)]

/-- The same actual law simultaneously has a larger corrected payoff
gap than the Gaussian at mean scale and kurtosis above 3 (Remark 1).
This does not infer an ordering of arbitrary laws from kurtosis alone. -/
theorem gaussianScaleMixture_uncertainty {K a b : ℝ} (hK : 0 < K)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    gaussianPayoffGap K ((a + b) / 2) < gaussianMixturePayoffGap K a b ∧
      3 < gaussianScaleMixtureKurtosis a b :=
  ⟨gaussianMixturePayoffGap_gt_mean_scale hK ha hb hab,
    gaussianScaleMixtureKurtosis_gt_three ha hb hab⟩

example : Integrable (fun x : ℝ => x ^ 4) (gaussianScaleMixture 3 7) :=
  gaussianScaleMixture_integrable_pow _ _ _

example : centralMoment (fun x : ℝ => x) 4 (gaussianScaleLaw 5) /
    variance (fun x : ℝ => x) (gaussianScaleLaw 5) ^ 2 = 3 :=
  gaussianScaleLaw_kurtosis (by norm_num)

example : variance (fun x : ℝ => x) (gaussianScaleMixture 3 7) = 29 := by
  rw [gaussianScaleMixture_variance]
  norm_num

example : centralMoment (fun x : ℝ => x) 4 (gaussianScaleMixture 3 7) = 3723 := by
  rw [gaussianScaleMixture_centralMoment_four]
  norm_num

example : gaussianScaleMixtureKurtosis 3 7 = 3723 / 841 := by
  rw [gaussianScaleMixtureKurtosis_eq (by norm_num)]
  norm_num

example : gaussianScaleMixtureKurtosis 3 7 = gaussianMixtureKurtosis 0 0 3 7 :=
  gaussianScaleMixtureKurtosis_eq_eq17 (by norm_num)

example : gaussianPayoffGap 3 5 < gaussianMixturePayoffGap 3 3 7 ∧
    3 < gaussianScaleMixtureKurtosis 3 7 := by
  have h := gaussianScaleMixture_uncertainty (K := 3) (a := 3) (b := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

#print axioms gaussianScaleMixture_moment_four
#print axioms gaussianScaleMixtureKurtosis_eq_eq17
#print axioms gaussianScaleMixture_uncertainty

end TailOptionPricing
