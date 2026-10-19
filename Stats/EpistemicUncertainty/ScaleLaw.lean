module

/-
  Actual finite random-dispersion law for arXiv:1912.00277v2,
  Sections II–III. Its natural moments are computed as genuine integrals.
  An independent standard Gaussian innovation generates exactly the
  recursively constructed outcome law. Binomial counting is separate.
-/
public import Stats.EpistemicUncertainty

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual dispersion population: recursively choose either scale
perturbation with equal probability (Sections II–III). -/
noncomputable def epistemicScaleLaw : ℕ → ℝ → ℝ → Measure ℝ
  | 0, σ, _ => Measure.dirac σ
  | n + 1, σ, ε => equalMixture (epistemicScaleLaw n (σ * (1 + ε)) ε)
      (epistemicScaleLaw n (σ * (1 - ε)) ε)

instance epistemicScaleLaw_probability (n : ℕ) (σ ε : ℝ) :
    IsProbabilityMeasure (epistemicScaleLaw n σ ε) := by
  induction n generalizing σ with
  | zero => unfold epistemicScaleLaw; infer_instance
  | succ n ih =>
    let := ih (σ * (1 + ε))
    let := ih (σ * (1 - ε))
    unfold epistemicScaleLaw
    infer_instance

/-- L1 of every actual natural-order dispersion power, before its
evaluation in Section III's formula. -/
theorem epistemicScaleLaw_integrable_pow (n k : ℕ) (σ ε : ℝ) :
    Integrable (fun s : ℝ => s ^ k) (epistemicScaleLaw n σ ε) := by
  induction n generalizing σ with
  | zero => exact integrable_dirac (by finiteness)
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture_integrable_iff]
    exact ⟨ih _, ih _⟩

/-- Actual natural-order dispersion moment, Section III. The recurrence
is integrated under its true probability law, not defined by this value. -/
theorem epistemicScaleLaw_moment (n k : ℕ) (σ ε : ℝ) :
    (∫ s : ℝ, s ^ k ∂epistemicScaleLaw n σ ε) = σ ^ k * (epistemicMomentFactor k ε) ^ n := by
  induction n generalizing σ with
  | zero => simp [epistemicScaleLaw]
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture_integral (epistemicScaleLaw_integrable_pow n k _ ε)
      (epistemicScaleLaw_integrable_pow n k _ ε), ih, ih,
      pow_succ (epistemicMomentFactor k ε) n]
    simp only [mul_pow]
    unfold epistemicMomentFactor
    ring

/-- The earlier binomial scale expression now equals an actual
dispersion expectation of every natural order (Section III). This
moment equality does not assert the missing branch-count pushforward. -/
theorem epistemicScaleLaw_moment_eq_sigmaMoment (n k : ℕ) (σ ε : ℝ) :
    (∫ s : ℝ, s ^ k ∂epistemicScaleLaw n σ ε) = epistemicSigmaMoment n k σ ε := by
  rw [epistemicScaleLaw_moment, epistemicSigmaMoment_eq]

/-- Actual unbiased mean dispersion, as required in Section II's model. -/
theorem epistemicScaleLaw_mean (n : ℕ) (σ ε : ℝ) :
    (∫ s : ℝ, s ∂epistemicScaleLaw n σ ε) = σ := by
  have hf : epistemicMomentFactor 1 ε = 1 := by unfold epistemicMomentFactor; ring
  simpa only [pow_one, hf, one_pow, mul_one] using epistemicScaleLaw_moment n 1 σ ε

/-- The actual dispersion is positive a.e. on the paper's domain,
so it really is a positive Gaussian standard deviation (Sections II–III). -/
theorem epistemicScaleLaw_ae_pos (n : ℕ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∀ᵐ s ∂epistemicScaleLaw n σ ε, 0 < s := by
  induction n generalizing σ with
  | zero => simpa only [epistemicScaleLaw, ae_dirac_iff measurableSet_Ioi] using hσ
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure (ih (mul_pos hσ (by linarith))) _
    · exact Measure.ae_smul_measure (ih (mul_pos hσ (by linarith))) _

/-- Actual collapse to an independent random-scale model (Sections
II–III): sample the genuine dispersion law and a standard Gaussian
independently, then form mu+scale*z. Its law equals the recursive
Gaussian population, including all finite depths. -/
theorem epistemicScaleLaw_outcome_model (n : ℕ) (μ σ ε : ℝ) :
    ((epistemicScaleLaw n σ ε).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => μ + p.1 * p.2) = epistemicBranchLaw n μ σ ε := by
  have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) :=
    (measurable_fst.mul measurable_snd).const_add μ
  induction n generalizing σ with
  | zero =>
    rw [epistemicScaleLaw, Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
    exact gaussianReal_map_affine_scale μ σ
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture_prod, equalMixture_map _ _ hm, ih, ih,
      epistemicBranchLaw]

example : IsProbabilityMeasure (epistemicScaleLaw 2 2 (1 / 2)) := inferInstance

example : Integrable (fun s : ℝ => s ^ 4) (epistemicScaleLaw 2 2 (1 / 2)) :=
  epistemicScaleLaw_integrable_pow _ _ _ _

example : (∫ s : ℝ, s ∂epistemicScaleLaw 2 2 (1 / 2)) = 2 := epistemicScaleLaw_mean _ _ _

example : (∫ s : ℝ, s ^ 4 ∂epistemicScaleLaw 2 2 (1 / 2)) = 1681 / 16 := by
  rw [epistemicScaleLaw_moment_eq_sigmaMoment, epistemicSigmaFourthMoment_eq]
  norm_num

example : ∀ᵐ s ∂epistemicScaleLaw 2 2 (1 / 2), 0 < s :=
  epistemicScaleLaw_ae_pos _ (by norm_num) (by norm_num) (by norm_num)

example : ((epistemicScaleLaw 2 2 (1 / 2)).prod (gaussianReal 0 1)).map
    (fun p : ℝ × ℝ => 1 + p.1 * p.2) = epistemicBranchLaw 2 1 2 (1 / 2) :=
  epistemicScaleLaw_outcome_model _ _ _ _

#print axioms epistemicScaleLaw_moment_eq_sigmaMoment
#print axioms epistemicScaleLaw_ae_pos
#print axioms epistemicScaleLaw_outcome_model

end TailOptionPricing
