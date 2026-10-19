module

/-
  Actual Gaussian switching-mean/variance population for
  arXiv:1802.05495v3, Eq. 17 and its kurtosis threshold. The probability
  law, L1, mean, variance and fourth central moment precede the formula.
  No claim about the actual MAD-based kappa follows from kurtosis alone.
-/
public import Stats.Probability.EqualMixture
public import Stats.Probability.GaussianShiftedMoments
public import Stats.Kappa.GaussianMixture

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual Eq. 17 population: with equal probability choose the
Gaussian with mean mu1 and scale sigma1 or mean mu2 and scale sigma2. -/
noncomputable def gaussianMixtureLaw (μ₁ μ₂ σ₁ σ₂ : ℝ) : Measure ℝ :=
  equalMixture (gaussianReal μ₁ (NNReal.mk (σ₁ ^ 2) (sq_nonneg σ₁)))
    (gaussianReal μ₂ (NNReal.mk (σ₂ ^ 2) (sq_nonneg σ₂)))

instance gaussianMixtureLaw_probability (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    IsProbabilityMeasure (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) := by
  unfold gaussianMixtureLaw
  infer_instance

/-- Every natural power about every center is L1 under the actual
switching law, including both moment orders used in Eq. 17. -/
theorem gaussianMixtureLaw_integrable_sub_pow (μ₁ μ₂ σ₁ σ₂ c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => (x - c) ^ n) (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) := by
  rw [gaussianMixtureLaw, equalMixture_integrable_iff]
  exact ⟨gaussianReal_integrable_sub_pow _ _ _ _, gaussianReal_integrable_sub_pow _ _ _ _⟩

/-- The actual population mean in Eq. 17, computed with component L1. -/
theorem gaussianMixtureLaw_mean (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    (∫ x : ℝ, x ∂gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) = (μ₁ + μ₂) / 2 := by
  have h₁ : Integrable (fun x : ℝ => x)
      (gaussianReal μ₁ (NNReal.mk (σ₁ ^ 2) (sq_nonneg σ₁))) := by
    simpa only [pow_one] using gaussianReal_integrable_pow μ₁
      (NNReal.mk (σ₁ ^ 2) (sq_nonneg σ₁)) 1
  have h₂ : Integrable (fun x : ℝ => x)
      (gaussianReal μ₂ (NNReal.mk (σ₂ ^ 2) (sq_nonneg σ₂))) := by
    simpa only [pow_one] using gaussianReal_integrable_pow μ₂
      (NNReal.mk (σ₂ ^ 2) (sq_nonneg σ₂)) 1
  rw [gaussianMixtureLaw, equalMixture_integral h₁ h₂,
    integral_id_gaussianReal, integral_id_gaussianReal]

/-- Actual variance of the general switching law in Eq. 17. -/
theorem gaussianMixtureLaw_variance (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    variance (fun x : ℝ => x) (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) =
      ((μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) / 4 := by
  have hm : AEMeasurable (fun x : ℝ => x) (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) :=
    measurable_id.aemeasurable
  rw [variance_eq_integral hm, gaussianMixtureLaw_mean, gaussianMixtureLaw,
    equalMixture_integral (gaussianReal_integrable_sub_pow _ _ _ 2)
      (gaussianReal_integrable_sub_pow _ _ _ 2), gaussianReal_momentAbout_two,
    gaussianReal_momentAbout_two]
  simp only [NNReal.coe_mk]
  ring

/-- Actual fourth central moment of the switching law, Eq. 17. The
noncentral fourth powers arise by integrating the shifted polynomials. -/
theorem gaussianMixtureLaw_centralMoment_four (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    centralMoment (fun x : ℝ => x) 4 (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) =
      3 * (σ₁ ^ 4 + σ₂ ^ 4) / 2 +
        3 * (μ₁ - μ₂) ^ 2 * (σ₁ ^ 2 + σ₂ ^ 2) / 4 + (μ₁ - μ₂) ^ 4 / 16 := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, gaussianMixtureLaw_mean]
  rw [gaussianMixtureLaw, equalMixture_integral (gaussianReal_integrable_sub_pow _ _ _ 4)
    (gaussianReal_integrable_sub_pow _ _ _ 4), gaussianReal_momentAbout_four,
    gaussianReal_momentAbout_four]
  simp only [NNReal.coe_mk]
  ring

/-- Pearson kurtosis as a ratio of actual central moments of the
Eq. 17 population. Its equality to the printed expression is proved. -/
noncomputable def gaussianMixtureLawKurtosis (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ :=
  centralMoment (fun x : ℝ => x) 4 (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) /
    variance (fun x : ℝ => x) (gaussianMixtureLaw μ₁ μ₂ σ₁ σ₂) ^ 2

/-- Full actual-law identification of arXiv:1802.05495v3, Eq. 17.
The nondegenerate denominator is four times the actual variance. -/
theorem gaussianMixtureLawKurtosis_eq_eq17 {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    gaussianMixtureLawKurtosis μ₁ μ₂ σ₁ σ₂ = gaussianMixtureKurtosis μ₁ μ₂ σ₁ σ₂ := by
  rw [gaussianMixtureLawKurtosis, gaussianMixtureLaw_centralMoment_four,
    gaussianMixtureLaw_variance, gaussianMixtureKurtosis]
  field_simp
  nlinarith [sq_pos_of_pos h]

/-- Eq. 17's polynomial threshold now concerns actual Pearson kurtosis,
under the source's nondegeneracy condition. -/
theorem gaussianMixtureLawKurtosis_ge_three_iff_poly {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureLawKurtosis μ₁ μ₂ σ₁ σ₂ ↔
      (μ₁ - μ₂) ^ 4 ≤ 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2 := by
  rw [gaussianMixtureLawKurtosis_eq_eq17 h]
  exact gaussianMixtureKurtosis_ge_three_iff_poly h

/-- Eq. 17's fourth-root threshold, identified with actual moments. -/
theorem gaussianMixtureLawKurtosis_ge_three_iff {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureLawKurtosis μ₁ μ₂ σ₁ σ₂ ↔
      |μ₁ - μ₂| ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) * sqrt |σ₁ ^ 2 - σ₂ ^ 2| := by
  rw [gaussianMixtureLawKurtosis_eq_eq17 h]
  exact gaussianMixtureKurtosis_ge_three_iff h

/-- The source's equal-scale, distinct-mean observation: actual Pearson
kurtosis lies strictly below three. This asserts no MAD-based kappa sign. -/
theorem gaussianMixtureLawKurtosis_lt_three_same_scale {μ₁ μ₂ : ℝ}
    (hne : μ₁ ≠ μ₂) (σ : ℝ) : gaussianMixtureLawKurtosis μ₁ μ₂ σ σ < 3 := by
  have hd : 0 < (μ₁ - μ₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hv : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ ^ 2 + σ ^ 2) := by nlinarith [sq_nonneg σ]
  apply lt_of_not_ge
  intro h
  have hp := (gaussianMixtureLawKurtosis_ge_three_iff_poly hv).mp h
  simp only [sub_self] at hp
  nlinarith [pow_pos hd 2]

example : IsProbabilityMeasure (gaussianMixtureLaw (-2) 2 1 1) := inferInstance

example : Integrable (fun x : ℝ => (x - 0) ^ 4) (gaussianMixtureLaw (-2) 2 1 1) :=
  gaussianMixtureLaw_integrable_sub_pow _ _ _ _ _ _

example : (∫ x : ℝ, x ∂gaussianMixtureLaw (-2) 2 1 1) = 0 := by
  rw [gaussianMixtureLaw_mean]
  norm_num

example : variance (fun x : ℝ => x) (gaussianMixtureLaw (-2) 2 1 1) = 5 := by
  rw [gaussianMixtureLaw_variance]
  norm_num

example : centralMoment (fun x : ℝ => x) 4 (gaussianMixtureLaw (-2) 2 1 1) = 43 := by
  rw [gaussianMixtureLaw_centralMoment_four]
  norm_num

example : gaussianMixtureLawKurtosis (-2) 2 1 1 = 43 / 25 := by
  rw [gaussianMixtureLawKurtosis_eq_eq17 (by norm_num)]
  norm_num [gaussianMixtureKurtosis]

example : gaussianMixtureLawKurtosis (-2) 2 1 1 < 3 :=
  gaussianMixtureLawKurtosis_lt_three_same_scale (by norm_num) _

example : 3 ≤ gaussianMixtureLawKurtosis 0 0 3 7 := by
  rw [gaussianMixtureLawKurtosis_ge_three_iff_poly (by norm_num)]
  norm_num

example : 3 ≤ gaussianMixtureLawKurtosis 0 0 3 7 ↔
    |(0 : ℝ) - 0| ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) * sqrt |(3 : ℝ) ^ 2 - 7 ^ 2| :=
  gaussianMixtureLawKurtosis_ge_three_iff (by norm_num)

#print axioms gaussianMixtureLaw_variance
#print axioms gaussianMixtureLaw_centralMoment_four
#print axioms gaussianMixtureLawKurtosis_eq_eq17
#print axioms gaussianMixtureLawKurtosis_lt_three_same_scale

end TailOptionPricing
