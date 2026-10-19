module

/-
  Actual Gaussian tail moments and normalized conditional laws for
  arXiv:1907.11162v3, Definition 4, Theorem 1 and Eq. 6.
  The population is the actual centered normalized Gaussian measure;
  its L1, tail normalization and conditional-mean limit are proved.
-/
public import Stats.BlackScholes.MillsLimit
public import Stats.BlackScholes.CallPrice.ClosedForm
public import Stats.BinaryForecasts.Conflation
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

private theorem integrable_stdNormal_id : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  apply memLp_one_iff_integrable.mp
  exact memLp_id_gaussianReal' 1 (by norm_num)

/-- Actual standard Gaussian upper tails have positive probability at
every finite threshold (arXiv:1907.11162v3, Definition 4). -/
theorem stdNormal_real_Ioi_pos (K : ℝ) : 0 < (gaussianReal 0 1).real (Ioi K) := by
  rw [← one_sub_stdNormalCdf]
  exact sub_pos.mpr (stdNormalCdf_lt_one K)

/-- The actual normalized Gaussian upper-tail law is a probability
measure at every finite threshold (paper Definition 4). -/
theorem stdNormal_cond_probability (K : ℝ) :
    IsProbabilityMeasure ((gaussianReal 0 1)[|Ioi K]) := by
  have h := ENNReal.toReal_pos_iff.mp (stdNormal_real_Ioi_pos K)
  exact cond_isProbabilityMeasure_of_finite h.1.ne' h.2.ne

/-- The conditional observation is genuinely L1 under the actual
normalized Gaussian tail law, as required in Definition 4. -/
theorem stdNormal_cond_integrable_id (K : ℝ) :
    Integrable (fun x : ℝ => x) ((gaussianReal 0 1)[|Ioi K]) := by
  rw [ProbabilityTheory.cond]
  exact integrable_stdNormal_id.integrableOn.smul_measure
    (ENNReal.inv_ne_top.mpr (ENNReal.toReal_pos_iff.mp (stdNormal_real_Ioi_pos K)).1.ne')

/-- Actual first tail moment in the paper's centered normalized Gaussian
case (Eq. 6). The L1 proof permits every finite real threshold. -/
theorem stdNormal_tail_mean (K : ℝ) :
    (∫ x in Ioi K, x ∂gaussianReal 0 1) = gaussianPDFReal 0 1 K := by
  have hi : Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
    have h := integrable_stdNormal_id
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))] at h
    simpa only [toReal_gaussianPDF] using h
  rw [setIntegral_gaussianReal_eq_setIntegral_pdf_mul one_ne_zero _ measurableSet_Ioi]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x * x) =
      (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
    funext x
    ring
  rw [he, integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => -gaussianPDFReal 0 1 x) (m := 0)
    (hasDerivAt_neg_gaussianPDFReal_std K).continuousAt.continuousWithinAt
    (fun x _ => hasDerivAt_neg_gaussianPDFReal_std x) hi.integrableOn
    (by simpa only [neg_zero] using tendsto_gaussianPDFReal_std_atTop.neg)]
  ring

/-- Actual conditional mean under the normalized standard Gaussian
tail law (paper Definition 4 and Eq. 6), with normalization and L1 proved. -/
theorem stdNormal_cond_mean (K : ℝ) :
    (∫ x : ℝ, x ∂(gaussianReal 0 1)[|Ioi K]) =
      gaussianPDFReal 0 1 K / (1 - stdNormalCdf K) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change ((gaussianReal 0 1).real (Ioi K))⁻¹ * (∫ x in Ioi K, x ∂gaussianReal 0 1) = _
  rw [stdNormal_tail_mean, ← one_sub_stdNormalCdf, div_eq_mul_inv, mul_comm]

/-- Actual upper-tail first-moment ratio tends to one for the centered
normalized Gaussian in arXiv:1907.11162v3, Theorem 1. -/
theorem stdNormal_tailMean_ratio_tendsto :
    Tendsto (fun K : ℝ => (∫ x in Ioi K, x ∂gaussianReal 0 1) /
      (K * (gaussianReal 0 1).real (Ioi K))) atTop (𝓝 1) := by
  simpa only [stdNormal_tail_mean, ← one_sub_stdNormalCdf] using
    stdNormal_characteristicScale_tendsto

/-- The actual Gaussian conditional-mean ratio tends to one,
verifying Definition 4's operational property for this population. -/
theorem stdNormal_condMean_ratio_tendsto :
    Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(gaussianReal 0 1)[|Ioi K]) / K)
      atTop (𝓝 1) := by
  apply stdNormal_characteristicScale_tendsto.congr
  intro K
  rw [stdNormal_cond_mean]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The written Gaussian density I1/I2 limit in Theorem 1. The PDF
integrals are identified with actual probability and the actual tail mean. -/
theorem stdNormal_I1_div_I2_tendsto :
    Tendsto (fun K : ℝ => I1 id (gaussianPDFReal 0 1) K /
      I2 id (gaussianPDFReal 0 1) K) atTop (𝓝 1) := by
  have hi (K : ℝ) : (∫ x in Ioi K, x ∂gaussianReal 0 1) = I1 id (gaussianPDFReal 0 1) K := by
    rw [setIntegral_gaussianReal_eq_setIntegral_pdf_mul one_ne_zero _ measurableSet_Ioi]
    unfold I1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact mul_comm _ _
  have hs (K : ℝ) : (gaussianReal 0 1).real (Ioi K) =
      ∫ x in Ioi K, gaussianPDFReal 0 1 x := by
    have h := setIntegral_gaussianReal_eq_setIntegral_pdf_mul (μ := 0) (v := 1)
      one_ne_zero (fun _ => 1) (s := Ioi K) measurableSet_Ioi
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using h
  apply stdNormal_tailMean_ratio_tendsto.congr
  intro K
  rw [hi, hs]
  rfl

example : 0 < (gaussianReal 0 1).real (Ioi (-1)) := stdNormal_real_Ioi_pos _

example : IsProbabilityMeasure ((gaussianReal 0 1)[|Ioi (1 : ℝ)]) :=
  stdNormal_cond_probability _

example : ∀ᵐ x ∂(gaussianReal 0 1)[|Ioi (1 : ℝ)], 1 < x := ae_cond_mem measurableSet_Ioi

example : Integrable (fun x : ℝ => x) ((gaussianReal 0 1)[|Ioi 1]) :=
  stdNormal_cond_integrable_id _

example : (∫ x in Ioi (-1 : ℝ), x ∂gaussianReal 0 1) = gaussianPDFReal 0 1 (-1) :=
  stdNormal_tail_mean _

example : (∫ x : ℝ, x ∂(gaussianReal 0 1)[|Ioi 0]) = 2 * gaussianPDFReal 0 1 0 := by
  rw [stdNormal_cond_mean]
  have h := stdNormalCdf_neg 0
  have hc : stdNormalCdf 0 = 1 / 2 := by
    norm_num only [neg_zero] at h
    linarith
  rw [hc]
  ring

#print axioms stdNormal_cond_probability
#print axioms stdNormal_cond_integrable_id
#print axioms stdNormal_tail_mean
#print axioms stdNormal_condMean_ratio_tendsto
#print axioms stdNormal_I1_div_I2_tendsto

end TailOptionPricing
