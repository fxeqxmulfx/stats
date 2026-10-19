module

/-
  Actual moments of the Normal–Lognormal precision mixture,
  arXiv:1912.00277v2, Section V, following Eq. compound. The actual
  variance and fourth central moment give Pearson kurtosis 3*exp(v).
  The source's 3*(exp(v)-1) is the EXCESS kurtosis, not Pearson's.
-/
public import Stats.EpistemicUncertainty.CompoundLaw

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual compound mean, Section V. The scale prior's first moment
is proved integrable before applying the general mixture identity. -/
theorem epistemicNormalLognormalLaw_mean (μ m : ℝ) (v : NNReal) :
    (∫ x : ℝ, x ∂epistemicNormalLognormalLaw μ m v) = μ :=
  epistemicGaussianMixtureLaw_mean μ _
    (by simpa only [pow_one] using epistemicLognormalScaleLaw_integrable_pow m v 1)

/-- Actual compound variance E[1/Lambda], with the precision prior
specified independently of this conclusion (Section V). -/
theorem epistemicNormalLognormalLaw_variance (μ m : ℝ) (v : NNReal) :
    variance (fun x : ℝ => x) (epistemicNormalLognormalLaw μ m v) =
      Real.exp (-m + (v : ℝ) / 2) := by
  rw [epistemicNormalLognormalLaw,
    epistemicGaussianMixtureLaw_variance μ _ (epistemicLognormalScaleLaw_integrable_pow m v 2),
    epistemicLognormalScaleLaw_moment_pow]
  congr 1
  norm_num
  ring

/-- Actual fourth central moment, centered by the actual compound
mean and justified by independently proved L1 (Section V). -/
theorem epistemicNormalLognormalLaw_centralMoment_four (μ m : ℝ) (v : NNReal) :
    (∫ x : ℝ, (x - ∫ y : ℝ, y ∂epistemicNormalLognormalLaw μ m v) ^ 4
      ∂epistemicNormalLognormalLaw μ m v) = 3 * Real.exp (-2 * m + 2 * (v : ℝ)) := by
  rw [epistemicNormalLognormalLaw_mean, epistemicNormalLognormalLaw,
    epistemicGaussianMixtureLaw_momentAbout_four μ _
      (epistemicLognormalScaleLaw_integrable_pow m v 4), epistemicLognormalScaleLaw_moment_pow]
  congr 2
  norm_num
  ring

/-- Pearson kurtosis is defined from actual central moments and
actual variance, not as the source's desired exponential expression. -/
noncomputable def epistemicNormalLognormalKurtosis (μ m : ℝ) (v : NNReal) : ℝ :=
  (∫ x : ℝ, (x - ∫ y : ℝ, y ∂epistemicNormalLognormalLaw μ m v) ^ 4
    ∂epistemicNormalLognormalLaw μ m v) /
      (variance (fun x : ℝ => x) (epistemicNormalLognormalLaw μ m v)) ^ 2

/-- Correct Pearson kurtosis of the actual compound in Section V.
The printed 3*(exp(v)-1) becomes correct after subtracting three. -/
theorem epistemicNormalLognormalKurtosis_eq (μ m : ℝ) (v : NNReal) :
    epistemicNormalLognormalKurtosis μ m v = 3 * Real.exp (v : ℝ) := by
  rw [epistemicNormalLognormalKurtosis, epistemicNormalLognormalLaw_centralMoment_four,
    epistemicNormalLognormalLaw_variance, ← Real.exp_nat_mul]
  have he : -2 * m + 2 * (v : ℝ) = (v : ℝ) + (2 : ℕ) * (-m + (v : ℝ) / 2) := by
    push_cast
    ring
  rw [he, Real.exp_add, ← mul_assoc, mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]

/-- The source's displayed compound “kurtosis” is the actual excess
kurtosis. The convention correction is explicit (Section V). -/
theorem epistemicNormalLognormalKurtosis_excess (μ m : ℝ) (v : NNReal) :
    epistemicNormalLognormalKurtosis μ m v - 3 = 3 * (Real.exp (v : ℝ) - 1) := by
  rw [epistemicNormalLognormalKurtosis_eq]
  ring

/-- A proper standard-log-precision compound refutes the printed
value if “kurtosis” means Pearson kurtosis (Section V). -/
theorem epistemic_compound_raw_kurtosis_counterexample :
    epistemicNormalLognormalKurtosis 0 0 1 ≠ 3 * (Real.exp 1 - 1) := by
  rw [epistemicNormalLognormalKurtosis_eq]
  norm_num only [NNReal.coe_one]
  intro h
  linarith

example : (∫ x : ℝ, x ∂epistemicNormalLognormalLaw 1 0 1) = 1 :=
  epistemicNormalLognormalLaw_mean _ _ _

example : variance (fun x : ℝ => x) (epistemicNormalLognormalLaw 1 0 1) = Real.exp (1 / 2) := by
  simpa using epistemicNormalLognormalLaw_variance 1 0 1

#print axioms epistemicNormalLognormalLaw_mean
#print axioms epistemicNormalLognormalLaw_variance
#print axioms epistemicNormalLognormalLaw_centralMoment_four
#print axioms epistemicNormalLognormalKurtosis_eq
#print axioms epistemic_compound_raw_kurtosis_counterexample

end TailOptionPricing
