module

/-
  Actual centered Gaussian scale laws and the corrected linear-payoff gap
  for arXiv:1907.11162v3, Definition 5 and Remark 1 / Eq. 8.
  The law is a pushforward of the actual standard Gaussian; its variance,
  normalization, L1 and tail moments are proved before differentiating.
-/
public import Stats.BinaryForecasts.GaussianLaw
public import Stats.BinaryForecasts.PayoffGap
public import Stats.BinaryForecasts.SigmaClosures

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual centered Gaussian of scale sigma, constructed as the
pushforward of the actual standard Gaussian, not from a moment formula. -/
noncomputable def gaussianScaleLaw (σ : ℝ) : Measure ℝ :=
  (gaussianReal 0 1).map (fun x : ℝ => σ * x)

instance gaussianScaleLaw_probability (σ : ℝ) : IsProbabilityMeasure (gaussianScaleLaw σ) := by
  unfold gaussianScaleLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_const_mul σ).aemeasurable).mpr inferInstance

/-- The pushforward has exactly the variance sigma squared used in
arXiv:1907.11162v3, Eq. 8, including its degenerate scale-zero case. -/
theorem gaussianScaleLaw_eq (σ : ℝ) :
    gaussianScaleLaw σ = gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ)) := by
  simpa only [gaussianScaleLaw, mul_zero, mul_one] using
    gaussianReal_map_const_mul (μ := 0) (v := 1) σ

private theorem scale_preimage_Ioi {σ : ℝ} (hσ : 0 < σ) (K : ℝ) :
    (fun x : ℝ => σ * x) ⁻¹' Ioi K = Ioi (K / σ) := by
  ext x
  simp only [mem_preimage, mem_Ioi, div_lt_iff₀ hσ, mul_comm σ x]

/-- Actual Gaussian upper-tail probability on the positive-scale
source domain (Eq. 8's distribution). -/
theorem gaussianScaleLaw_real_Ioi {σ : ℝ} (hσ : 0 < σ) (K : ℝ) :
    (gaussianScaleLaw σ).real (Ioi K) = 1 - stdNormalCdf (K / σ) := by
  unfold gaussianScaleLaw Measure.real
  rw [Measure.map_apply (measurable_const_mul σ) measurableSet_Ioi, scale_preimage_Ioi hσ K]
  exact (one_sub_stdNormalCdf _).symm

/-- The actual scale-family observation is L1, before computing a
truncated moment or differentiating it (Eq. 8). -/
theorem gaussianScaleLaw_integrable_id (σ : ℝ) :
    Integrable (fun x : ℝ => x) (gaussianScaleLaw σ) := by
  unfold gaussianScaleLaw
  have hm : AEStronglyMeasurable (fun x : ℝ => x)
      ((gaussianReal 0 1).map (fun x : ℝ => σ * x)) := measurable_id.aestronglyMeasurable
  rw [integrable_map_measure hm (measurable_const_mul σ).aemeasurable]
  change Integrable (fun x : ℝ => σ * x) (gaussianReal 0 1)
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by norm_num))
  exact hi.const_mul σ

/-- Actual first tail moment for the scale-sigma Gaussian (Eq. 8).
The actual law's integrability is proved independently above. -/
theorem gaussianScaleLaw_tail_mean {σ : ℝ} (hσ : 0 < σ) (K : ℝ) :
    (∫ x in Ioi K, x ∂gaussianScaleLaw σ) = σ * gaussianPDFReal 0 1 (K / σ) := by
  unfold gaussianScaleLaw
  have hm : AEStronglyMeasurable (fun x : ℝ => x)
      ((gaussianReal 0 1).map (fun x : ℝ => σ * x)) := measurable_id.aestronglyMeasurable
  rw [setIntegral_map measurableSet_Ioi hm
    (measurable_const_mul σ).aemeasurable, scale_preimage_Ioi hσ K]
  rw [integral_const_mul, stdNormal_tail_mean]

/-- Definition 5's actual linear-payoff gap for the scale-Gaussian
population. The threshold payoff K multiplies the actual tail probability. -/
noncomputable def gaussianPayoffGap (K σ : ℝ) : ℝ :=
  (∫ x in Ioi K, x ∂gaussianScaleLaw σ) - K * (gaussianScaleLaw σ).real (Ioi K)

/-- The actual gap is the actual restricted expectation of excess,
with its L1 condition supplied by the genuine Gaussian law. -/
theorem gaussianPayoffGap_eq_integral_excess (K σ : ℝ) :
    gaussianPayoffGap K σ = ∫ x in Ioi K, x - K ∂gaussianScaleLaw σ := by
  exact tailPayoff_gap_eq_integral (gaussianScaleLaw σ)
    (gaussianScaleLaw_integrable_id σ).integrableOn

/-- Correct actual-law closed form for the linear-payoff gap used in
arXiv:1907.11162v3, Remark 1. Eq. 8 omits the K in its second term. -/
theorem gaussianPayoffGap_eq_closed {σ : ℝ} (hσ : 0 < σ) (K : ℝ) :
    gaussianPayoffGap K σ = σ * gaussianPDFReal 0 1 (K / σ) -
      K * (1 - stdNormalCdf (K / σ)) := by
  rw [gaussianPayoffGap, gaussianScaleLaw_tail_mean hσ, gaussianScaleLaw_real_Ioi hσ]

/-- The actual excess-payoff expectation is nonnegative. -/
theorem gaussianPayoffGap_nonneg (K σ : ℝ) : 0 ≤ gaussianPayoffGap K σ := by
  rw [gaussianPayoffGap_eq_integral_excess]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact sub_nonneg.mpr hx.le

/-- Definition 5's written Gaussian-density gap is the same actual-law
quantity on the paper's positive-scale, nonnegative-threshold domain. -/
theorem gaussianDensityPayoffGap_eq_actual {K σ : ℝ} (hσ : 0 < σ) (hK : 0 ≤ K) :
    I1 id (gaussianPDF_σ σ) K - I2 id (gaussianPDF_σ σ) K = gaussianPayoffGap K σ := by
  simp only [I1, I2, id]
  rw [integral_x_gaussianPDF_σ hσ hK, integral_gaussianPDF_σ hσ,
    gaussianPayoffGap_eq_closed hσ]

example : gaussianScaleLaw 5 = gaussianReal 0 25 := by
  rw [gaussianScaleLaw_eq]
  have hv : NNReal.mk ((5 : ℝ) ^ 2) (sq_nonneg (5 : ℝ)) = 25 := by
    apply NNReal.eq
    norm_num
  rw [hv]

example : IsProbabilityMeasure (gaussianScaleLaw 5) := inferInstance

example : Integrable (fun x : ℝ => x) (gaussianScaleLaw 5) := gaussianScaleLaw_integrable_id _

example : (gaussianScaleLaw 5).real (Ioi 3) = 1 - stdNormalCdf (3 / 5) :=
  gaussianScaleLaw_real_Ioi (by norm_num) _

example : (∫ x in Ioi (3 : ℝ), x ∂gaussianScaleLaw 5) = 5 * gaussianPDFReal 0 1 (3 / 5) :=
  gaussianScaleLaw_tail_mean (by norm_num) _

example : gaussianPayoffGap 3 5 = ∫ x in Ioi (3 : ℝ), x - 3 ∂gaussianScaleLaw 5 :=
  gaussianPayoffGap_eq_integral_excess _ _

example : gaussianPayoffGap 3 5 = 5 * gaussianPDFReal 0 1 (3 / 5) -
    3 * (1 - stdNormalCdf (3 / 5)) := gaussianPayoffGap_eq_closed (by norm_num) _

example : I1 id (gaussianPDF_σ 5) 3 - I2 id (gaussianPDF_σ 5) 3 = gaussianPayoffGap 3 5 :=
  gaussianDensityPayoffGap_eq_actual (by norm_num) (by norm_num)

#print axioms gaussianDensityPayoffGap_eq_actual
#print axioms gaussianPayoffGap_eq_closed
#print axioms gaussianScaleLaw_eq
#print axioms gaussianScaleLaw_real_Ioi
#print axioms gaussianScaleLaw_integrable_id
#print axioms gaussianScaleLaw_tail_mean

end TailOptionPricing
