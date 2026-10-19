module

/-
  Actual moments of general Gaussian scale mixtures,
  arXiv:1912.00277v2, Sections II and V, Eqs. 1 and compound.
  Independently established scale-moment integrability supplies L1
  of the actual population moment. Its independent Gaussian-innovation
  representation then justifies Fubini, rather than assuming moments
  of the compound as formulas or input certificates.
-/
public import Stats.EpistemicUncertainty.GaussianKernel

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual centered powers are L1 whenever the corresponding scale
power is L1 under the independently specified prior (Sections II,V). -/
theorem epistemicGaussianMixtureLaw_integrable_sub_pow (μ : ℝ) (ν : Measure ℝ) (k : ℕ)
    (hs : Integrable (fun s : ℝ => s ^ k) ν) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicGaussianMixtureLaw μ ν) := by
  have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) := by fun_prop
  have hf : Measurable (fun x : ℝ => (x - μ) ^ k) := by fun_prop
  rw [← epistemicGaussianMixtureLaw_outcome_model,
    integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable]
  change Integrable (fun p : ℝ × ℝ => (μ + p.1 * p.2 - μ) ^ k) (ν.prod (gaussianReal 0 1))
  simpa only [add_sub_cancel_left, mul_pow] using
    hs.mul_prod (gaussianReal_integrable_pow 0 1 k)

/-- Fubini for genuine integrable population moments: an actual
Gaussian-mixture moment factors into the scale and innovation moments.
The prior supplies L1, not the claimed compound moment (Sections II,V). -/
theorem epistemicGaussianMixtureLaw_momentAbout (μ : ℝ) (ν : Measure ℝ) [SFinite ν] (k : ℕ)
    (hs : Integrable (fun s : ℝ => s ^ k) ν) :
    (∫ x : ℝ, (x - μ) ^ k ∂epistemicGaussianMixtureLaw μ ν) =
      (∫ s : ℝ, s ^ k ∂ν) * (∫ z : ℝ, z ^ k ∂gaussianReal 0 1) := by
  have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) := by fun_prop
  have hf : Measurable (fun x : ℝ => (x - μ) ^ k) := by fun_prop
  rw [← epistemicGaussianMixtureLaw_outcome_model,
    integral_map hm.aemeasurable hf.aestronglyMeasurable]
  simp only [add_sub_cancel_left, mul_pow]
  rw [integral_prod _ (hs.mul_prod (gaussianReal_integrable_pow 0 1 k))]
  simp_rw [integral_const_mul]
  exact integral_mul_const _ _

/-- An L1 scale prior gives a genuinely integrable actual outcome,
before computing its mean (Section V's compound model). -/
theorem epistemicGaussianMixtureLaw_integrable (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : Integrable (fun s : ℝ => s) ν) :
    Integrable (fun x : ℝ => x) (epistemicGaussianMixtureLaw μ ν) := by
  have h1 : Integrable (fun x : ℝ => x - μ) (epistemicGaussianMixtureLaw μ ν) := by
    simpa only [pow_one] using
      epistemicGaussianMixtureLaw_integrable_sub_pow μ ν 1 (by simpa only [pow_one] using hs)
  simpa only [sub_add_cancel] using h1.fun_add (integrable_const μ)

/-- The actual general-prior compound has mean mu when the first
scale moment is finite (Section V). -/
theorem epistemicGaussianMixtureLaw_mean (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : Integrable (fun s : ℝ => s) ν) :
    (∫ x : ℝ, x ∂epistemicGaussianMixtureLaw μ ν) = μ := by
  have h1 := epistemicGaussianMixtureLaw_momentAbout μ ν 1 (by simpa using hs)
  simp only [pow_one, integral_id_gaussianReal, mul_zero] at h1
  rw [integral_sub (epistemicGaussianMixtureLaw_integrable μ ν hs) (integrable_const μ)] at h1
  simpa using (sub_eq_zero.mp h1)

/-- The actual mixture variance is the actual second scale moment.
Its first moment follows from the prior's L2 rather than being an
extra assumed output property (Section V, Eq. compound). -/
theorem epistemicGaussianMixtureLaw_variance (μ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hs : Integrable (fun s : ℝ => s ^ 2) ν) :
    variance (fun x : ℝ => x) (epistemicGaussianMixtureLaw μ ν) = ∫ s : ℝ, s ^ 2 ∂ν := by
  have h2 : MemLp (fun s : ℝ => s) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hs
  have h1 : Integrable (fun s : ℝ => s) ν := MemLp.integrable (by norm_num) h2
  have hm : AEMeasurable (fun x : ℝ => x) (epistemicGaussianMixtureLaw μ ν) := measurable_id.aemeasurable
  rw [variance_eq_integral hm, epistemicGaussianMixtureLaw_mean μ ν h1,
    epistemicGaussianMixtureLaw_momentAbout μ ν 2 hs, gaussianReal_zero_moment_two]
  simp

/-- The actual fourth moment about the Gaussian location equals three
times the fourth scale moment; L1 is supplied by that prior moment
(Section V). Whenever the mean is finite it equals this same location. -/
theorem epistemicGaussianMixtureLaw_momentAbout_four (μ : ℝ) (ν : Measure ℝ) [SFinite ν]
    (hs : Integrable (fun s : ℝ => s ^ 4) ν) :
    (∫ x : ℝ, (x - μ) ^ 4 ∂epistemicGaussianMixtureLaw μ ν) = 3 * ∫ s : ℝ, s ^ 4 ∂ν := by
  rw [epistemicGaussianMixtureLaw_momentAbout μ ν 4 hs, gaussianReal_zero_moment_four]
  norm_num
  ring

example : Integrable (fun x : ℝ => (x - 1) ^ 4)
    (epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) :=
  epistemicGaussianMixtureLaw_integrable_sub_pow _ _ _ (integrable_dirac (by finiteness))

example : (∫ x : ℝ, (x - 1) ^ 2 ∂epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) = 4 := by
  rw [epistemicGaussianMixtureLaw_momentAbout _ _ _ (integrable_dirac (by finiteness)),
    integral_dirac, gaussianReal_zero_moment_two]
  norm_num

example : Integrable (fun x : ℝ => x)
    (epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) :=
  epistemicGaussianMixtureLaw_integrable _ _ (integrable_dirac (by finiteness))

example : (∫ x : ℝ, x ∂epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) = 1 :=
  epistemicGaussianMixtureLaw_mean _ _ (integrable_dirac (by finiteness))

example : variance (fun x : ℝ => x)
    (epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) = 4 := by
  rw [epistemicGaussianMixtureLaw_variance _ _ (integrable_dirac (by finiteness)), integral_dirac]
  norm_num

example : (∫ x : ℝ, (x - 1) ^ 4 ∂epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) = 48 := by
  rw [epistemicGaussianMixtureLaw_momentAbout_four _ _ (integrable_dirac (by finiteness)), integral_dirac]
  norm_num

#print axioms epistemicGaussianMixtureLaw_integrable_sub_pow
#print axioms epistemicGaussianMixtureLaw_momentAbout
#print axioms epistemicGaussianMixtureLaw_variance

end TailOptionPricing
