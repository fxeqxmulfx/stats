module

/-
  Correct unscaled weak depth limit of the actual populations in
  arXiv:1912.00277v2, Section III. With fixed positive base scale and
  fixed error in (0,1), the Gaussian outcome laws converge to a point
  mass at their common mean. Their variances nevertheless diverge.
  This replaces a nondegenerate weak power-law interpretation of the
  source's graphical depth discussion; it asserts no rescaled limit.
-/
public import Stats.EpistemicUncertainty.ScaleConcentration
public import Stats.EpistemicUncertainty.BranchingLimits
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual Section III outcome law bundled with its normalization. -/
noncomputable def epistemicOutcomeProba (n : ℕ) (μ σ ε : ℝ) : ProbabilityMeasure ℝ :=
  ⟨epistemicBranchLaw n μ σ ε, inferInstance⟩

/-- The actual unscaled outcome populations converge weakly to the
point mass at mu for fixed positive scale and error in (0,1).
Section III's increasing moments do not give a nondegenerate weak
power-law limit. The actual independent Gaussian generator is used. -/
theorem epistemicOutcomeProba_tendsto_dirac (μ : ℝ) {σ ε : ℝ} (hσ : 0 < σ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => epistemicOutcomeProba n μ σ ε) atTop
      (𝓝 (⟨Measure.dirac μ, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let g : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  let d : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  have hs : Tendsto (fun n => epistemicScaleProba n σ ε) atTop (𝓝 d) :=
    epistemicScaleProba_tendsto_dirac hσ hε₀ hε₁
  have hp : Tendsto (fun n => (epistemicScaleProba n σ ε).prod g) atTop (𝓝 (d.prod g)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hs.prodMk_nhds tendsto_const_nhds)
  have hc : Continuous (fun p : ℝ × ℝ => μ + p.1 * p.2) :=
    continuous_const.add (continuous_fst.mul continuous_snd)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp hc
  have he (n : ℕ) : ((epistemicScaleProba n σ ε).prod g).map
      (fun p : ℝ × ℝ => μ + p.1 * p.2) = epistemicOutcomeProba n μ σ ε := by
    apply Subtype.ext
    exact epistemicScaleLaw_outcome_model n μ σ ε
  have hd : (d.prod g).map (fun p : ℝ × ℝ => μ + p.1 * p.2) =
      (⟨Measure.dirac μ, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change ((Measure.dirac (0 : ℝ)).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => μ + p.1 * p.2) = Measure.dirac μ
    have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) :=
      (measurable_fst.mul measurable_snd).const_add μ
    rw [Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
    simp only [Function.comp_def, zero_mul, add_zero, Measure.map_const, measure_univ, one_smul]
  simpa only [he, hd] using ht

/-- Every weak limit of these unscaled populations is the same point
mass. In particular a different nondegenerate weak power-law limit is
excluded for Section III's fixed positive scale and error in (0,1). -/
theorem epistemicOutcomeProba_weak_limit_unique (μ : ℝ) {σ ε : ℝ} (hσ : 0 < σ)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto (fun n => epistemicOutcomeProba n μ σ ε) atTop (𝓝 ν)) :
    ν = (⟨Measure.dirac μ, inferInstance⟩ : ProbabilityMeasure ℝ) :=
  tendsto_nhds_unique hν (epistemicOutcomeProba_tendsto_dirac μ hσ hε₀ hε₁)

/-- The same actual population sequence has a point-mass weak limit
and divergent actual variance (Section III). This states the moment
sequence explicitly, rather than assigning a variance to an unproved limit. -/
theorem epistemicOutcomeProba_weak_limit_and_variance_divergence (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => epistemicOutcomeProba n μ σ ε) atTop
      (𝓝 (⟨Measure.dirac μ, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
      Tendsto (fun n => variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε)) atTop atTop :=
  ⟨epistemicOutcomeProba_tendsto_dirac μ hσ hε₀ hε₁,
    epistemicBranchLaw_variance_tendsto_atTop μ hσ.ne' hε₀.ne'⟩

example : Tendsto (fun n => epistemicOutcomeProba n 1 2 (1 / 2)) atTop
    (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  epistemicOutcomeProba_tendsto_dirac _ (by norm_num) (by norm_num) (by norm_num)

example : ∃ ν : ProbabilityMeasure ℝ,
    Tendsto (fun n => epistemicOutcomeProba n 1 2 (1 / 2)) atTop (𝓝 ν) ∧
      ν = (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  have hν := epistemicOutcomeProba_tendsto_dirac 1 (σ := 2) (ε := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, hν, epistemicOutcomeProba_weak_limit_unique _
    (by norm_num) (by norm_num) (by norm_num) hν⟩

example : Tendsto (fun n => epistemicOutcomeProba n 1 2 (1 / 2)) atTop
    (𝓝 (⟨Measure.dirac 1, inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    Tendsto (fun n => variance (fun x : ℝ => x) (epistemicBranchLaw n 1 2 (1 / 2)))
      atTop atTop :=
  epistemicOutcomeProba_weak_limit_and_variance_divergence _
    (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemicOutcomeProba_tendsto_dirac
#print axioms epistemicOutcomeProba_weak_limit_unique
#print axioms epistemicOutcomeProba_weak_limit_and_variance_divergence

end TailOptionPricing
