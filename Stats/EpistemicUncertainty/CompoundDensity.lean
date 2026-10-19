module

/-
  Actual density of the Normal–Lognormal precision mixture,
  arXiv:1912.00277v2, Section V, Eq. compound. The independently
  normalized compound law has the conditional Gaussian density
  integrated against its actual precision prior. Nonzero log variance
  gives the positive Lebesgue integral of the two source densities.
-/
public import Stats.EpistemicUncertainty.CompoundLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

open LognormalMeasure

/-- Prior-averaged actual Gaussian density of Section V's compound,
with the standard deviation induced by the random precision. -/
noncomputable def epistemicNormalLognormalDensity (μ m : ℝ) (v : NNReal) (x : ℝ) : ENNReal :=
  epistemicGaussianMixtureDensity μ (epistemicLognormalScaleLaw m v) x

theorem epistemicNormalLognormalDensity_measurable (μ m : ℝ) (v : NNReal) :
    Measurable (epistemicNormalLognormalDensity μ m v) :=
  epistemicGaussianMixtureDensity_measurable _ _

/-- Equality of actual compound measures with the averaged density;
positive scale support supplies the component density hypotheses.
This includes the prior's zero-log-variance boundary (Section V). -/
theorem epistemicNormalLognormalLaw_eq_withDensity (μ m : ℝ) (v : NNReal) :
    epistemicNormalLognormalLaw μ m v =
      volume.withDensity (epistemicNormalLognormalDensity μ m v) :=
  epistemicGaussianMixtureLaw_eq_withDensity _ _ (epistemicLognormalScaleLaw_ae_pos m v)

/-- The actual density integrates the conditional Gaussian against
the actual precision law, without replacing that law by a formula
or assuming an integral interchange (Section V, Eq. compound). -/
theorem epistemicNormalLognormalDensity_eq_precisionIntegral (μ m : ℝ) (v : NNReal) (x : ℝ) :
    epistemicNormalLognormalDensity μ m v x =
      ∫⁻ l : ℝ, gaussianPDF μ (NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _)) x
        ∂lognormalReal m v := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x) := by
    unfold gaussianPDF gaussianPDFReal
    simp only [NNReal.coe_mk]
    fun_prop
  unfold epistemicNormalLognormalDensity epistemicGaussianMixtureDensity epistemicLognormalScaleLaw
  exact lintegral_map hf hm

/-- Section V's literal compound integral: integrate the lognormal
precision density times the Gaussian density with variance 1/lambda
over strictly positive precision. The prior must have nonzero log
variance for its Lebesgue-density representation to hold. -/
theorem epistemicNormalLognormalDensity_eq_lintegral (μ m : ℝ) {v : NNReal}
    (hv : v ≠ 0) (x : ℝ) :
    epistemicNormalLognormalDensity μ m v x =
      ∫⁻ l : ℝ in Ioi 0, lognormalPDF m v l * gaussianPDF μ (l⁻¹).toNNReal x := by
  have hf : Measurable (fun l : ℝ =>
      gaussianPDF μ (NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _)) x) := by
    unfold gaussianPDF gaussianPDFReal
    simp only [NNReal.coe_mk]
    fun_prop
  rw [epistemicNormalLognormalDensity_eq_precisionIntegral,
    lognormalReal_eq_withDensity m hv,
    lintegral_withDensity_eq_lintegral_mul volume (lognormalPDF_measurable m v) hf,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro l
  by_cases hl : l ∈ Ioi (0 : ℝ)
  · have he : NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _) = (l⁻¹).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_mk, Real.coe_toNNReal _ (inv_nonneg.mpr hl.le), epistemic_inverseSqrt_sq hl]
    simp only [Pi.mul_apply, indicator_of_mem hl, he]
  · simp [lognormalPDF, hl]

/-- Normalization is derived from the actual compound probability
law, not assumed of the candidate density (Section V). -/
theorem epistemicNormalLognormalDensity_lintegral (μ m : ℝ) (v : NNReal) :
    (∫⁻ x : ℝ, epistemicNormalLognormalDensity μ m v x) = 1 :=
  epistemicGaussianMixtureDensity_lintegral _ _ (epistemicLognormalScaleLaw_ae_pos m v)

theorem epistemicNormalLognormalDensity_ae_lt_top (μ m : ℝ) (v : NNReal) :
    ∀ᵐ x : ℝ, epistemicNormalLognormalDensity μ m v x < ⊤ :=
  epistemicGaussianMixtureDensity_ae_lt_top _ _ (epistemicLognormalScaleLaw_ae_pos m v)

/-- Actual event probabilities of the compound are integrals of the
proved normalized density (Section V, Eq. compound). -/
theorem epistemicNormalLognormalLaw_apply_density (μ m : ℝ) (v : NNReal)
    {A : Set ℝ} (hA : MeasurableSet A) :
    epistemicNormalLognormalLaw μ m v A = ∫⁻ x in A, epistemicNormalLognormalDensity μ m v x := by
  rw [epistemicNormalLognormalLaw_eq_withDensity, withDensity_apply _ hA]

example (x : ℝ) : epistemicNormalLognormalDensity 0 0 1 x =
    ∫⁻ l : ℝ in Ioi 0, lognormalPDF 0 1 l * gaussianPDF 0 (l⁻¹).toNNReal x :=
  epistemicNormalLognormalDensity_eq_lintegral _ _ (by norm_num) _

example : epistemicNormalLognormalLaw 0 0 1 (Ici 2) =
    ∫⁻ x in Ici 2, epistemicNormalLognormalDensity 0 0 1 x :=
  epistemicNormalLognormalLaw_apply_density _ _ _ measurableSet_Ici

#print axioms epistemicNormalLognormalLaw_eq_withDensity
#print axioms epistemicNormalLognormalDensity_eq_lintegral
#print axioms epistemicNormalLognormalDensity_lintegral

end TailOptionPricing
