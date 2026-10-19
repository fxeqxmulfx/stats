module

/-
  Actual Gaussian scale mixtures with general positive dispersion laws,
  arXiv:1912.00277v2, Section II, Eq. 1. The Gaussian conditional law is
  a genuine measurable Markov kernel. Tonelli identifies its actual
  marginal density without assuming pointwise finite density integrals.
-/
public import Stats.EpistemicUncertainty.LayerLaw
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The conditional Gaussian in Section II, Eq. 1, as a measurable
kernel from dispersion to outcome. Variance is dispersion squared. -/
noncomputable def epistemicGaussianScaleKernel (μ : ℝ) : Kernel ℝ ℝ where
  toFun s := gaussianReal μ (NNReal.mk (s ^ 2) (sq_nonneg s))
  measurable' := by
    have hv : Measurable (fun s : ℝ => NNReal.mk (s ^ 2) (sq_nonneg s)) :=
      (measurable_id.pow_const 2).subtype_mk
    exact measurable_gaussianReal.comp (measurable_const.prodMk hv)

instance epistemicGaussianScaleKernel_markov (μ : ℝ) :
    IsMarkovKernel (epistemicGaussianScaleKernel μ) := by
  constructor
  intro s
  change IsProbabilityMeasure (gaussianReal μ (NNReal.mk (s ^ 2) (sq_nonneg s)))
  infer_instance

/-- Actual marginal outcome law with general dispersion prior nu,
Section II, Eq. 1. Its independent-innovation representation is proved below. -/
noncomputable def epistemicGaussianMixtureLaw (μ : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ν.bind (epistemicGaussianScaleKernel μ)

instance epistemicGaussianMixtureLaw_probability (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (epistemicGaussianMixtureLaw μ ν) := by
  unfold epistemicGaussianMixtureLaw
  infer_instance

/-- Actual event probabilities of the kernel mixture, before replacing
the Gaussian components by density integrals (Section II, Eq. 1). -/
theorem epistemicGaussianMixtureLaw_apply (μ : ℝ) (ν : Measure ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    epistemicGaussianMixtureLaw μ ν A =
      ∫⁻ s : ℝ, gaussianReal μ (NNReal.mk (s ^ 2) (sq_nonneg s)) A ∂ν := by
  rw [epistemicGaussianMixtureLaw,
    Measure.bind_apply hA (epistemicGaussianScaleKernel μ).measurable.aemeasurable]
  rfl

/-- Independently sample the actual dispersion law and a standard
Gaussian innovation. The resulting mu+scale*z law is the actual kernel
mixture, not merely a density expression (Section II, Eq. 1). -/
theorem epistemicGaussianMixtureLaw_outcome_model (μ : ℝ) (ν : Measure ℝ) :
    (ν.prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => μ + p.1 * p.2) =
      epistemicGaussianMixtureLaw μ ν := by
  have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) :=
    (measurable_fst.mul measurable_snd).const_add μ
  ext A hA
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA),
    epistemicGaussianMixtureLaw_apply μ ν hA]
  apply lintegral_congr
  intro s
  have h := congrArg (fun ρ : Measure ℝ => ρ A) (gaussianReal_map_affine_scale μ s)
  rw [Measure.map_apply ((measurable_const_mul s).const_add μ) hA] at h
  exact h

/-- General kernel mixing recovers the actual varying-error Gaussian
population when its genuine finite dispersion law is used (Sections II–IV). -/
theorem epistemicGaussianMixtureLaw_eq_layer (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) :
    epistemicGaussianMixtureLaw μ (epistemicLayerScaleLaw n σ ε) =
      epistemicLayerBranchLaw n μ σ ε := by
  rw [← epistemicGaussianMixtureLaw_outcome_model, epistemicLayerScaleLaw_outcome_model]

/-- Joint measurability of the actual Gaussian conditional density,
needed for the source's interchange of scale and outcome integration. -/
theorem epistemicGaussianScalePDF_measurable (μ : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      gaussianPDF μ (NNReal.mk (p.1 ^ 2) (sq_nonneg _)) p.2) := by
  unfold gaussianPDF gaussianPDFReal
  simp only [NNReal.coe_mk]
  fun_prop

/-- The nonnegative density integral of Section II, Eq. 1, with respect
to the actual scale prior. It may be infinite at exceptional points;
normalization below concerns the actual Lebesgue density. -/
noncomputable def epistemicGaussianMixtureDensity (μ : ℝ) (ν : Measure ℝ) (x : ℝ) : ENNReal :=
  ∫⁻ s : ℝ, gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x ∂ν

/-- Measurability of the actual prior-averaged Gaussian density. -/
theorem epistemicGaussianMixtureDensity_measurable (μ : ℝ) (ν : Measure ℝ) [SFinite ν] :
    Measurable (epistemicGaussianMixtureDensity μ ν) :=
  (epistemicGaussianScalePDF_measurable μ).lintegral_prod_left

/-- Eq. 1 is the actual marginal Lebesgue density for every probability
dispersion prior concentrated on positive scales. Tonelli is justified
by joint measurability, without assuming the desired marginal formula. -/
theorem epistemicGaussianMixtureLaw_eq_withDensity (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, 0 < s) :
    epistemicGaussianMixtureLaw μ ν = volume.withDensity (epistemicGaussianMixtureDensity μ ν) := by
  ext A hA
  rw [epistemicGaussianMixtureLaw_apply μ ν hA, withDensity_apply _ hA]
  change (∫⁻ s : ℝ, gaussianReal μ (NNReal.mk (s ^ 2) (sq_nonneg s)) A ∂ν) =
    ∫⁻ x in A, ∫⁻ s : ℝ, gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x ∂ν
  calc _ = ∫⁻ s : ℝ, (∫⁻ x in A, gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hν] with s hs
        have hv : (NNReal.mk (s ^ 2) (sq_nonneg s) : NNReal) ≠ 0 := by
          intro hz
          have hz' : s ^ 2 = 0 := congrArg (fun v : NNReal => (v : ℝ)) hz
          exact (ne_of_gt (sq_pos_of_pos hs)) hz'
        exact gaussianReal_apply μ hv A
    _ = _ := lintegral_lintegral_swap (μ := ν) (ν := volume.restrict A)
      (epistemicGaussianScalePDF_measurable μ).aemeasurable

/-- Actual measurable event probabilities are integrals of Eq. 1's
prior-averaged density, for every positive dispersion probability law. -/
theorem epistemicGaussianMixtureLaw_apply_density (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, 0 < s) {A : Set ℝ} (hA : MeasurableSet A) :
    epistemicGaussianMixtureLaw μ ν A = ∫⁻ x in A, epistemicGaussianMixtureDensity μ ν x := by
  rw [epistemicGaussianMixtureLaw_eq_withDensity μ ν hν, withDensity_apply _ hA]

/-- The actual general-prior mixture density integrates to one,
derived from the independently normalized Markov mixture (Eq. 1). -/
theorem epistemicGaussianMixtureDensity_lintegral (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, 0 < s) :
    (∫⁻ x : ℝ, epistemicGaussianMixtureDensity μ ν x) = 1 := by
  have h := congrArg (fun ρ : Measure ℝ => ρ univ)
    (epistemicGaussianMixtureLaw_eq_withDensity μ ν hν)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

/-- The actual mixture density is finite Lebesgue-a.e., even when
the scale integral can diverge at an exceptional outcome (Eq. 1). -/
theorem epistemicGaussianMixtureDensity_ae_lt_top (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, 0 < s) :
    ∀ᵐ x : ℝ, epistemicGaussianMixtureDensity μ ν x < ⊤ := by
  apply ae_lt_top (epistemicGaussianMixtureDensity_measurable μ ν)
  rw [epistemicGaussianMixtureDensity_lintegral μ ν hν]
  norm_num

example : IsProbabilityMeasure (epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) :=
  inferInstance

example : epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ)) (Ici 3) =
    ∫⁻ s : ℝ, gaussianReal 1 (NNReal.mk (s ^ 2) (sq_nonneg s)) (Ici 3)
      ∂Measure.dirac (2 : ℝ) := epistemicGaussianMixtureLaw_apply _ _ measurableSet_Ici

example : epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ)) =
    volume.withDensity (epistemicGaussianMixtureDensity 1 (Measure.dirac (2 : ℝ))) := by
  apply epistemicGaussianMixtureLaw_eq_withDensity
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

example : epistemicGaussianMixtureLaw 1
    (epistemicLayerScaleLaw 2 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) =
      volume.withDensity (epistemicGaussianMixtureDensity 1
        (epistemicLayerScaleLaw 2 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i))) := by
  apply epistemicGaussianMixtureLaw_eq_withDensity
  apply epistemicLayerScaleLaw_ae_pos _ (by norm_num)
  intro i hi
  interval_cases i <;> norm_num

example : epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ)) (Ici 3) =
    ∫⁻ x in Ici 3, epistemicGaussianMixtureDensity 1 (Measure.dirac (2 : ℝ)) x := by
  apply epistemicGaussianMixtureLaw_apply_density _ _ ?_ measurableSet_Ici
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

example : (∫⁻ x : ℝ, epistemicGaussianMixtureDensity 1 (Measure.dirac (2 : ℝ)) x) = 1 := by
  apply epistemicGaussianMixtureDensity_lintegral
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

example : ∀ᵐ x : ℝ, epistemicGaussianMixtureDensity 1 (Measure.dirac (2 : ℝ)) x < ⊤ := by
  apply epistemicGaussianMixtureDensity_ae_lt_top
  simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)

#print axioms epistemicGaussianScaleKernel_markov
#print axioms epistemicGaussianMixtureLaw_outcome_model
#print axioms epistemicGaussianMixtureLaw_eq_withDensity

end TailOptionPricing
