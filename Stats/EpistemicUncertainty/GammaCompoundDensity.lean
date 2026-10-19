module

/-
  The actual Normal--Gamma density, arXiv:1912.00277v2, Section VI,
  Eq. compoundGamma. The independently normalized population law has
  the conditional Gaussian density averaged over actual Gamma precision.
  Tonelli and the proved positive support justify its positive-axis
  Lebesgue integral. No Student formula or output moment is assumed.
-/
public import Stats.EpistemicUncertainty.GammaCompoundLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual prior-averaged conditional Gaussian density for the
Section VI Normal--Gamma precision mixture. The second Gamma parameter
is a rate; conditional variance is inverse precision. -/
noncomputable def epistemicNormalGammaDensity (μ a r x : ℝ) : ENNReal :=
  epistemicGaussianMixtureDensity μ (epistemicGammaScaleLaw a r) x

theorem epistemicNormalGammaDensity_measurable (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) : Measurable (epistemicNormalGammaDensity μ a r) := by
  let := epistemicGammaScaleLaw_probability ha hr
  exact epistemicGaussianMixtureDensity_measurable _ _

/-- Equality of the whole actual Normal--Gamma law and the proved
prior-averaged Lebesgue density, for every positive shape and rate.
Normalization is independent of the later Euler evaluation. -/
theorem epistemicNormalGammaLaw_eq_withDensity (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    epistemicNormalGammaLaw μ a r = volume.withDensity (epistemicNormalGammaDensity μ a r) := by
  let := epistemicGammaScaleLaw_probability ha hr
  exact epistemicGaussianMixtureLaw_eq_withDensity _ _ (epistemicGammaScaleLaw_ae_pos a r)

/-- The actual compound density integrates conditional Gaussian
densities against the actual Gamma precision probability law, via
the proved inverse-square-root dispersion transformation (Section VI). -/
theorem epistemicNormalGammaDensity_eq_precisionIntegral (μ a r x : ℝ) :
    epistemicNormalGammaDensity μ a r x =
      ∫⁻ l : ℝ, gaussianPDF μ (NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _)) x
        ∂gammaMeasure a r := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x) := by
    unfold gaussianPDF gaussianPDFReal
    simp only [NNReal.coe_mk]
    fun_prop
  unfold epistemicNormalGammaDensity epistemicGaussianMixtureDensity epistemicGammaScaleLaw
  exact lintegral_map hf hm

/-- Eq. compoundGamma as an actual positive-axis Lebesgue integral.
The boundary precision zero is Lebesgue-null; on positive precision
the conditional Gaussian variance is exactly 1/lambda. -/
theorem epistemicNormalGammaDensity_eq_lintegral (μ a r x : ℝ) :
    epistemicNormalGammaDensity μ a r x =
      ∫⁻ l : ℝ in Ioi 0, gammaPDF a r l * gaussianPDF μ (l⁻¹).toNNReal x := by
  have hf : Measurable (fun l : ℝ =>
      gaussianPDF μ (NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _)) x) := by
    unfold gaussianPDF gaussianPDFReal
    simp only [NNReal.coe_mk]
    fun_prop
  have hg : Measurable (gammaPDF a r) := by unfold gammaPDF; fun_prop
  rw [epistemicNormalGammaDensity_eq_precisionIntegral, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume hg hf,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  have hz : ∀ᵐ l : ℝ ∂volume, l ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hz] with l hl₀
  by_cases hl : l ∈ Ioi (0 : ℝ)
  · have he : NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _) = (l⁻¹).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_mk, Real.coe_toNNReal _ (inv_nonneg.mpr hl.le), epistemic_inverseSqrt_sq hl]
    simp only [Pi.mul_apply, indicator_of_mem hl, he]
  · have hn : l < 0 := lt_of_le_of_ne (not_lt.mp hl) hl₀
    simp [Pi.mul_apply, gammaPDF, gammaPDFReal, hl, not_le.mpr hn]

/-- The actual compound density integrates to one, derived from the
independently proper Gamma prior and Gaussian Markov mixture. Even
shapes without a finite outcome mean are included (Section VI). -/
theorem epistemicNormalGammaDensity_lintegral (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ x : ℝ, epistemicNormalGammaDensity μ a r x) = 1 := by
  let := epistemicGammaScaleLaw_probability ha hr
  exact epistemicGaussianMixtureDensity_lintegral _ _ (epistemicGammaScaleLaw_ae_pos a r)

theorem epistemicNormalGammaDensity_ae_lt_top (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x : ℝ, epistemicNormalGammaDensity μ a r x < ⊤ := by
  let := epistemicGammaScaleLaw_probability ha hr
  exact epistemicGaussianMixtureDensity_ae_lt_top _ _ (epistemicGammaScaleLaw_ae_pos a r)

/-- Actual measurable event probabilities are integrals of the proved
normalized compound density (Section VI, Eq. compoundGamma). -/
theorem epistemicNormalGammaLaw_apply_density (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) {A : Set ℝ} (hA : MeasurableSet A) :
    epistemicNormalGammaLaw μ a r A = ∫⁻ x in A, epistemicNormalGammaDensity μ a r x := by
  rw [epistemicNormalGammaLaw_eq_withDensity μ ha hr, withDensity_apply _ hA]

/-- The density representation also computes the actual real-valued
event probability, retaining the genuine compound measure. -/
theorem epistemicNormalGammaLaw_real_apply_density (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) {A : Set ℝ} (hA : MeasurableSet A) :
    (epistemicNormalGammaLaw μ a r).real A =
      (∫⁻ x in A, epistemicNormalGammaDensity μ a r x).toReal := by
  exact congrArg ENNReal.toReal (epistemicNormalGammaLaw_apply_density μ ha hr hA)

/-- The actual outcome population is absolutely continuous for every
proper Gamma prior, independently of its finite moments (Section VI). -/
theorem epistemicNormalGammaLaw_absolutelyContinuous (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) : epistemicNormalGammaLaw μ a r ≪ volume := by
  rw [epistemicNormalGammaLaw_eq_withDensity μ ha hr]
  exact withDensity_absolutelyContinuous _ _

example : Measurable (epistemicNormalGammaDensity 1 3 2) :=
  epistemicNormalGammaDensity_measurable 1 (by norm_num) (by norm_num)

example : epistemicNormalGammaLaw 0 (1 / 4) 2 =
    volume.withDensity (epistemicNormalGammaDensity 0 (1 / 4) 2) :=
  epistemicNormalGammaLaw_eq_withDensity 0 (by norm_num) (by norm_num)

example (x : ℝ) : epistemicNormalGammaDensity 1 3 2 x =
    ∫⁻ l : ℝ, gaussianPDF 1 (NNReal.mk ((l ^ (-1 / 2 : ℝ)) ^ 2) (sq_nonneg _)) x
      ∂gammaMeasure 3 2 := epistemicNormalGammaDensity_eq_precisionIntegral 1 3 2 x

example (x : ℝ) : epistemicNormalGammaDensity 1 3 2 x =
    ∫⁻ l : ℝ in Ioi 0, gammaPDF 3 2 l * gaussianPDF 1 (l⁻¹).toNNReal x :=
  epistemicNormalGammaDensity_eq_lintegral 1 3 2 x

example : (∫⁻ x : ℝ, epistemicNormalGammaDensity 0 (1 / 4) 2 x) = 1 :=
  epistemicNormalGammaDensity_lintegral 0 (by norm_num) (by norm_num)

example : ∀ᵐ x : ℝ, epistemicNormalGammaDensity 1 3 2 x < ⊤ :=
  epistemicNormalGammaDensity_ae_lt_top 1 (by norm_num) (by norm_num)

example : epistemicNormalGammaLaw 1 3 2 (Ici 2) =
    ∫⁻ x in Ici 2, epistemicNormalGammaDensity 1 3 2 x :=
  epistemicNormalGammaLaw_apply_density 1 (by norm_num) (by norm_num) measurableSet_Ici

example : (epistemicNormalGammaLaw 1 3 2).real (Ici 2) =
    (∫⁻ x in Ici 2, epistemicNormalGammaDensity 1 3 2 x).toReal :=
  epistemicNormalGammaLaw_real_apply_density 1 (by norm_num) (by norm_num) measurableSet_Ici

example : epistemicNormalGammaLaw 0 (1 / 4) 2 ≪ volume :=
  epistemicNormalGammaLaw_absolutelyContinuous 0 (by norm_num) (by norm_num)

#print axioms epistemicNormalGammaLaw_eq_withDensity
#print axioms epistemicNormalGammaDensity_eq_lintegral
#print axioms epistemicNormalGammaDensity_lintegral
#print axioms epistemicNormalGammaLaw_absolutelyContinuous

end TailOptionPricing
