module

/-
  Sharp actual Normal--Gamma and Student moment domains,
  arXiv:1912.00277v2, Section VI. Conditional Gaussian mixing preserves
  the scale-power L1 restriction in both directions. A nonzero Gaussian
  innovation section forces the scale moment to be integrable. The
  actual Gamma inverse-order criterion then proves sharpness, including
  the equality boundary and the restriction on the outcome mean.
-/
public import Stats.Probability.GammaMomentDomain
public import Stats.EpistemicUncertainty.GammaCompoundStudent

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter

namespace TailOptionPricing

/-- Centered Gaussian-mixture power L1 is equivalent to scale-power
L1. Necessity uses an actual nonzero Gaussian innovation section,
not a claimed compound moment or a formal cancellation (Section VI). -/
theorem epistemicGaussianMixtureLaw_integrable_sub_pow_iff (μ : ℝ) (ν : Measure ℝ)
    [SFinite ν] (k : ℕ) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicGaussianMixtureLaw μ ν) ↔
      Integrable (fun s : ℝ => s ^ k) ν := by
  refine ⟨?_, epistemicGaussianMixtureLaw_integrable_sub_pow μ ν k⟩
  intro h
  have hm : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) := by fun_prop
  have hf : Measurable (fun x : ℝ => (x - μ) ^ k) := by fun_prop
  rw [← epistemicGaussianMixtureLaw_outcome_model,
    integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable] at h
  change Integrable (fun p : ℝ × ℝ => (μ + p.1 * p.2 - μ) ^ k)
    (ν.prod (gaussianReal 0 1)) at h
  simp only [add_sub_cancel_left, mul_pow] at h
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hz : ∀ᵐ z : ℝ ∂gaussianReal 0 1, z ≠ 0 := by rw [ae_iff]; simp
  obtain ⟨z, hz₀, hzi⟩ := (hz.and h.prod_left_ae).exists
  change Integrable (fun s : ℝ => s ^ k * z ^ k) ν at hzi
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero k hz₀))
    (fun s : ℝ => s ^ k)).mp hzi

/-- The actual Gamma-induced dispersion power has exactly the
inverse-precision L1 domain a>k/2, including failure at equality. -/
theorem epistemicGammaScaleLaw_integrable_pow_iff {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (epistemicGammaScaleLaw a r) ↔ (k : ℝ) / 2 < a := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => s ^ k) := by fun_prop
  rw [epistemicGammaScaleLaw, integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable]
  change Integrable (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) (gammaMeasure a r) ↔ _
  have he : (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) =ᵐ[gammaMeasure a r]
      (fun l : ℝ => l ^ (-(k : ℝ) / 2)) := by
    filter_upwards [gammaMeasure_ae_pos a r] with l hl
    exact epistemic_inverseSqrt_pow hl k
  rw [integrable_congr he, gammaMeasure_inverse_order_integrable_iff ha hr]

/-- The actual Normal--Gamma centered power is L1 precisely when
a>k/2. This proves the sharp outcome restriction, not merely a
sufficient prior moment condition (Section VI). -/
theorem epistemicNormalGammaLaw_integrable_sub_pow_iff (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicNormalGammaLaw μ a r) ↔ (k : ℝ) / 2 < a := by
  let := epistemicGammaScaleLaw_probability ha hr
  rw [epistemicNormalGammaLaw, epistemicGaussianMixtureLaw_integrable_sub_pow_iff,
    epistemicGammaScaleLaw_integrable_pow_iff ha hr]

/-- At and below the shape boundary the actual compound moment fails
L1; symmetry does not provide a finite mean or odd moment there. -/
theorem epistemicNormalGammaLaw_not_integrable_sub_pow (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) (hk : a ≤ (k : ℝ) / 2) :
    ¬Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicNormalGammaLaw μ a r) := by
  rw [epistemicNormalGammaLaw_integrable_sub_pow_iff μ ha hr k]
  exact not_lt_of_ge hk

/-- Section VI's actual outcome has a finite first moment exactly
when a>1/2. Positive shape/rate alone do not imply the claimed mean. -/
theorem epistemicNormalGammaLaw_integrable_iff (μ : ℝ) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw μ a r) ↔ 1 / 2 < a := by
  let := epistemicNormalGammaLaw_probability μ ha hr
  have hc : Integrable (fun x : ℝ => x - μ) (epistemicNormalGammaLaw μ a r) ↔
      Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw μ a r) := by
    constructor
    · intro h
      simpa only [sub_add_cancel] using h.fun_add (integrable_const μ)
    · intro h
      exact h.sub' (integrable_const μ)
  exact hc.symm.trans (by simpa only [pow_one, Nat.cast_one] using
    epistemicNormalGammaLaw_integrable_sub_pow_iff μ ha hr 1)

/-- The conventional Student centered k-th power is L1 exactly for
degrees of freedom nu>k, with every positive scale allowed. -/
theorem studentMeasure_integrable_sub_pow_iff (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (k : ℕ) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (studentMeasure μ ν s) ↔ (k : ℝ) < ν := by
  rw [studentMeasure_eq_normalGamma μ hν hs,
    epistemicNormalGammaLaw_integrable_sub_pow_iff μ (by positivity) (by positivity)]
  constructor <;> intro h <;> linarith

/-- Conventional Student first-moment L1 holds exactly for nu>1.
The scale and location do not repair the small-df failure (Section VI). -/
theorem studentMeasure_integrable_iff (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Integrable (fun x : ℝ => x) (studentMeasure μ ν s) ↔ 1 < ν := by
  rw [studentMeasure_eq_normalGamma μ hν hs,
    epistemicNormalGammaLaw_integrable_iff μ (by positivity) (by positivity)]
  constructor <;> intro h <;> linarith

/-- Section VI's mean claim corrected to a>1/2. The actual first
moment exists by the sharp criterion, and independent mixture
integration gives the location, rather than a symmetry convention. -/
theorem epistemicNormalGammaLaw_mean (μ : ℝ) {a r : ℝ} (ha : 1 / 2 < a) (hr : 0 < r) :
    (∫ x : ℝ, x ∂epistemicNormalGammaLaw μ a r) = μ := by
  have ha₀ : 0 < a := by linarith
  let := epistemicGammaScaleLaw_probability ha₀ hr
  apply epistemicGaussianMixtureLaw_mean μ _
  simpa only [pow_one] using
    epistemicGammaScaleLaw_integrable_pow ha₀ hr 1 (by simpa only [Nat.cast_one] using ha)

/-- The actual conventional Student mean is its location for nu>1,
with first-moment L1 established above (Section VI's corrected mean). -/
theorem studentMeasure_mean (μ : ℝ) {ν s : ℝ} (hν : 1 < ν) (hs : 0 < s) :
    (∫ x : ℝ, x ∂studentMeasure μ ν s) = μ := by
  have hν₀ : 0 < ν := by linarith
  rw [studentMeasure_eq_normalGamma μ hν₀ hs]
  exact epistemicNormalGammaLaw_mean μ (by linarith) (by positivity)

/-- A proper shape-one-quarter, rate-two compound has no finite mean.
At location one its undefined Bochner integral is zero, so even the
literal unrestricted mean-equals-location formula in Section VI fails. -/
theorem epistemicNormalGamma_mean_counterexample :
    IsProbabilityMeasure (epistemicNormalGammaLaw 1 (1 / 4) 2) ∧
      ¬Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw 1 (1 / 4) 2) ∧
      (∫ x : ℝ, x ∂epistemicNormalGammaLaw 1 (1 / 4) 2) ≠ 1 := by
  have hi : ¬Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw 1 (1 / 4) 2) := by
    rw [epistemicNormalGammaLaw_integrable_iff 1 (by norm_num) (by norm_num)]
    norm_num
  refine ⟨epistemicNormalGammaLaw_probability 1 (by norm_num) (by norm_num), hi, ?_⟩
  rw [integral_undef hi]
  norm_num

example : Integrable (fun x : ℝ => (x - 1) ^ 4)
    (epistemicGaussianMixtureLaw 1 (Measure.dirac (2 : ℝ))) ↔
    Integrable (fun s : ℝ => s ^ 4) (Measure.dirac (2 : ℝ)) :=
  epistemicGaussianMixtureLaw_integrable_sub_pow_iff 1 _ 4

example : Integrable (fun s : ℝ => s ^ 4) (epistemicGammaScaleLaw 3 2) ↔ (4 : ℝ) / 2 < 3 :=
  epistemicGammaScaleLaw_integrable_pow_iff (by norm_num) (by norm_num) 4

example : Integrable (fun x : ℝ => (x - 1) ^ 4) (epistemicNormalGammaLaw 1 3 2) ↔ (4 : ℝ) / 2 < 3 :=
  epistemicNormalGammaLaw_integrable_sub_pow_iff 1 (by norm_num) (by norm_num) 4

example : ¬Integrable (fun x : ℝ => (x - 1) ^ 4) (epistemicNormalGammaLaw 1 2 3) :=
  epistemicNormalGammaLaw_not_integrable_sub_pow 1 (by norm_num) (by norm_num) 4 (by norm_num)

example : Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw 1 3 2) ↔ (1 : ℝ) / 2 < 3 :=
  epistemicNormalGammaLaw_integrable_iff 1 (by norm_num) (by norm_num)

example : Integrable (fun x : ℝ => (x - 1) ^ 4) (studentMeasure 1 6 2) ↔ (4 : ℝ) < 6 :=
  studentMeasure_integrable_sub_pow_iff 1 (by norm_num) (by norm_num) 4

example : Integrable (fun x : ℝ => x) (studentMeasure 1 (1 / 2) 2) ↔ (1 : ℝ) < 1 / 2 :=
  studentMeasure_integrable_iff 1 (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ∂epistemicNormalGammaLaw 1 3 2) = 1 :=
  epistemicNormalGammaLaw_mean 1 (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ∂studentMeasure 1 6 2) = 1 :=
  studentMeasure_mean 1 (by norm_num) (by norm_num)

example : ¬Integrable (fun x : ℝ => x) (epistemicNormalGammaLaw 0 (1 / 4) 2) := by
  rw [epistemicNormalGammaLaw_integrable_iff 0 (by norm_num) (by norm_num)]
  norm_num

#print axioms epistemicGaussianMixtureLaw_integrable_sub_pow_iff
#print axioms epistemicNormalGammaLaw_integrable_sub_pow_iff
#print axioms epistemicNormalGammaLaw_integrable_iff
#print axioms studentMeasure_integrable_sub_pow_iff
#print axioms studentMeasure_integrable_iff
#print axioms epistemicNormalGammaLaw_mean
#print axioms studentMeasure_mean
#print axioms epistemicNormalGamma_mean_counterexample

end TailOptionPricing
