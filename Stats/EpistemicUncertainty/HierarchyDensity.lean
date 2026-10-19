module

/-
  Actual iterated conditional mixture densities, arXiv:1912.00277v2,
  Section II's display following Eq. 1. The source's fixed Gaussian
  sigma must be the sampled conditional scale. Here the prior and
  transition kernels explicitly encode all conditional dependencies;
  the Gaussian uses the last sampled dispersion. Transitions run from
  outer uncertainty toward the observation scale. All densities and
  integrals are nonnegative, so Tonelli needs no pointwise L1 assumption.
-/
public import Stats.EpistemicUncertainty.HierarchyLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The source's finite iterated conditional integral, with the prior
sampled first and transition kappa_i supplying the next dispersion.
The identity with an actual hierarchy integral is proved below. -/
noncomputable def epistemicHierarchyIntegral : ℕ → Measure ℝ → (ℕ → Kernel ℝ ℝ) →
    (ℝ → ENNReal) → ENNReal
  | 0, ν, _, f => ∫⁻ s : ℝ, f s ∂ν
  | n + 1, ν, κ, f => epistemicHierarchyIntegral n ν κ (fun s => ∫⁻ t : ℝ, f t ∂κ n s)

/-- Actual integration under the conditional scale hierarchy equals
the complete repeated integral (Section II). Measurability propagates
through each kernel before applying the genuine measure-bind identity. -/
theorem epistemicScaleHierarchy_lintegral (n : ℕ) (ν : Measure ℝ) (κ : ℕ → Kernel ℝ ℝ)
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ s : ℝ, f s ∂epistemicScaleHierarchy n ν κ) = epistemicHierarchyIntegral n ν κ f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [epistemicScaleHierarchy,
      Measure.lintegral_bind (κ n).measurable.aemeasurable hf.aemeasurable]
    exact ih _ ((Measure.measurable_lintegral hf).comp (κ n).measurable)

/-- Actual Gaussian outcome population after n conditional uncertainty
transitions, Section II. Its normalization comes from the actual
Markov hierarchy and Gaussian conditional law. -/
noncomputable def epistemicHierarchyOutcomeLaw (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) : Measure ℝ :=
  epistemicGaussianMixtureLaw μ (epistemicScaleHierarchy n ν κ)

instance epistemicHierarchyOutcomeLaw_probability (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)] :
    IsProbabilityMeasure (epistemicHierarchyOutcomeLaw n μ ν κ) := by
  unfold epistemicHierarchyOutcomeLaw
  infer_instance

/-- Corrected repeated Gaussian density integral of Section II. The
Gaussian depends on the final sampled dispersion, and each intervening
conditional law may depend on its parent scale. -/
noncomputable def epistemicHierarchyDensity (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) (x : ℝ) : ENNReal :=
  epistemicHierarchyIntegral n ν κ
    (fun s => gaussianPDF μ (NNReal.mk (s ^ 2) (sq_nonneg s)) x)

/-- The actual final dispersion density integral equals the source's
full repeated conditional integral, with all interchanges justified. -/
theorem epistemicHierarchyDensity_eq (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) (x : ℝ) :
    epistemicGaussianMixtureDensity μ (epistemicScaleHierarchy n ν κ) x =
      epistemicHierarchyDensity n μ ν κ x := by
  unfold epistemicGaussianMixtureDensity epistemicHierarchyDensity
  apply epistemicScaleHierarchy_lintegral
  unfold gaussianPDF gaussianPDFReal
  simp only [NNReal.coe_mk]
  fun_prop

/-- Measurability of the actual iterated Gaussian mixture density. -/
theorem epistemicHierarchyDensity_measurable (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)] :
    Measurable (epistemicHierarchyDensity n μ ν κ) := by
  have he : epistemicGaussianMixtureDensity μ (epistemicScaleHierarchy n ν κ) =
      epistemicHierarchyDensity n μ ν κ := funext (epistemicHierarchyDensity_eq n μ ν κ)
  rw [← he]
  exact epistemicGaussianMixtureDensity_measurable _ _

/-- The actual normalized hierarchy outcome law has the corrected
repeated density integral of Section II. Positive conditional support
is propagated from the prior through every transition, then Tonelli
identifies the actual Gaussian marginal density. -/
theorem epistemicHierarchyOutcomeLaw_eq_withDensity (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)]
    (hν : ∀ᵐ s ∂ν, 0 < s)
    (hκ : ∀ i < n, ∀ s, 0 < s → ∀ᵐ t ∂κ i s, 0 < t) :
    epistemicHierarchyOutcomeLaw n μ ν κ = volume.withDensity (epistemicHierarchyDensity n μ ν κ) := by
  unfold epistemicHierarchyOutcomeLaw
  rw [epistemicGaussianMixtureLaw_eq_withDensity μ _ (epistemicScaleHierarchy_ae_pos n ν κ hν hκ)]
  congr 1
  exact funext (epistemicHierarchyDensity_eq n μ ν κ)

/-- Every measurable event probability in the actual uncertainty
hierarchy is the corresponding repeated density integral (Section II). -/
theorem epistemicHierarchyOutcomeLaw_apply_density (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)]
    (hν : ∀ᵐ s ∂ν, 0 < s)
    (hκ : ∀ i < n, ∀ s, 0 < s → ∀ᵐ t ∂κ i s, 0 < t) {A : Set ℝ} (hA : MeasurableSet A) :
    epistemicHierarchyOutcomeLaw n μ ν κ A = ∫⁻ x in A, epistemicHierarchyDensity n μ ν κ x := by
  rw [epistemicHierarchyOutcomeLaw_eq_withDensity n μ ν κ hν hκ, withDensity_apply _ hA]

/-- The actual complete repeated conditional density integrates to
one, from the independently normalized hierarchy population (Section II). -/
theorem epistemicHierarchyDensity_lintegral (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)]
    (hν : ∀ᵐ s ∂ν, 0 < s)
    (hκ : ∀ i < n, ∀ s, 0 < s → ∀ᵐ t ∂κ i s, 0 < t) :
    (∫⁻ x : ℝ, epistemicHierarchyDensity n μ ν κ x) = 1 := by
  have h := congrArg (fun ρ : Measure ℝ => ρ univ)
    (epistemicHierarchyOutcomeLaw_eq_withDensity n μ ν κ hν hκ)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

/-- The actual repeated conditional density is finite Lebesgue-a.e.;
exceptional pointwise infinite density values need not be excluded. -/
theorem epistemicHierarchyDensity_ae_lt_top (n : ℕ) (μ : ℝ) (ν : Measure ℝ)
    (κ : ℕ → Kernel ℝ ℝ) [IsProbabilityMeasure ν] [∀ i, IsMarkovKernel (κ i)]
    (hν : ∀ᵐ s ∂ν, 0 < s)
    (hκ : ∀ i < n, ∀ s, 0 < s → ∀ᵐ t ∂κ i s, 0 < t) :
    ∀ᵐ x : ℝ, epistemicHierarchyDensity n μ ν κ x < ⊤ := by
  apply ae_lt_top (epistemicHierarchyDensity_measurable n μ ν κ)
  rw [epistemicHierarchyDensity_lintegral n μ ν κ hν hκ]
  norm_num

example : IsProbabilityMeasure (epistemicHierarchyOutcomeLaw 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2))) := inferInstance

example : (∫⁻ s : ℝ, ENNReal.ofReal (s ^ 2) ∂epistemicScaleHierarchy 2 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2))) =
      epistemicHierarchyIntegral 2 (Measure.dirac (2 : ℝ))
        (fun _ => epistemicFairScaleKernel (1 / 2)) (fun s => ENNReal.ofReal (s ^ 2)) := by
  apply epistemicScaleHierarchy_lintegral
  fun_prop

example (n : ℕ) : (∫⁻ x : ℝ, epistemicHierarchyDensity n 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)) x) = 1 := by
  apply epistemicHierarchyDensity_lintegral
  · simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)
  · intro i hi s hs
    exact epistemicFairScaleKernel_ae_pos hs (by norm_num) (by norm_num)

example : epistemicHierarchyOutcomeLaw 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)) (Ici 3) =
      ∫⁻ x in Ici 3, epistemicHierarchyDensity 2 1 (Measure.dirac (2 : ℝ))
        (fun _ => epistemicFairScaleKernel (1 / 2)) x := by
  apply epistemicHierarchyOutcomeLaw_apply_density _ _ _ _ ?_ ?_ measurableSet_Ici
  · simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)
  · intro i hi s hs
    exact epistemicFairScaleKernel_ae_pos hs (by norm_num) (by norm_num)

example : ∀ᵐ x : ℝ, epistemicHierarchyDensity 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)) x < ⊤ := by
  apply epistemicHierarchyDensity_ae_lt_top
  · simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)
  · intro i hi s hs
    exact epistemicFairScaleKernel_ae_pos hs (by norm_num) (by norm_num)

example : epistemicHierarchyOutcomeLaw 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)) = volume.withDensity (fun x =>
      ∫⁻ s₀ : ℝ, (∫⁻ s₁ : ℝ, (∫⁻ s₂ : ℝ,
        gaussianPDF 1 (NNReal.mk (s₂ ^ 2) (sq_nonneg s₂)) x
          ∂epistemicFairScaleKernel (1 / 2) s₁)
            ∂epistemicFairScaleKernel (1 / 2) s₀) ∂Measure.dirac (2 : ℝ)) := by
  change epistemicHierarchyOutcomeLaw 2 1 (Measure.dirac (2 : ℝ))
    (fun _ => epistemicFairScaleKernel (1 / 2)) = volume.withDensity
      (epistemicHierarchyDensity 2 1 (Measure.dirac (2 : ℝ)) (fun _ => epistemicFairScaleKernel (1 / 2)))
  apply epistemicHierarchyOutcomeLaw_eq_withDensity
  · simpa only [ae_dirac_iff measurableSet_Ioi] using (show (0 : ℝ) < 2 by norm_num)
  · intro i hi s hs
    exact epistemicFairScaleKernel_ae_pos hs (by norm_num) (by norm_num)

#print axioms epistemicScaleHierarchy_lintegral
#print axioms epistemicHierarchyOutcomeLaw_eq_withDensity
#print axioms epistemicHierarchyDensity_lintegral

end TailOptionPricing
