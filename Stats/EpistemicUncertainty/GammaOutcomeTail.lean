module

/-
  Epistemic variance and actual matched Gamma-compound tails,
  arXiv:1912.00277v2, Section VI. The prior is the genuine Gamma
  moment match to lognormal precision. Greater positive variance
  strictly decreases the actual Student tail index and yields a
  larger eventual outcome tail on both sides. These statements are
  about the matched Gamma model; approximation error is not an input.
-/
public import Stats.EpistemicUncertainty.GammaTailIndex
public import Stats.EpistemicUncertainty.GammaCompoundMomentDomain
public import Stats.Probability.StudentTailAsymptotic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual Section VI outcome model with the source's Gamma
shape and rate matched to positive lognormal log variance v. -/
noncomputable def epistemicMatchedGammaOutcomeLaw (μ v : ℝ) : Measure ℝ :=
  epistemicNormalGammaLaw μ (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)

theorem epistemicMatchedGammaOutcomeLaw_probability (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    IsProbabilityMeasure (epistemicMatchedGammaOutcomeLaw μ v) :=
  epistemicNormalGammaLaw_probability μ (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv)

/-- Exact probability-law identification with the corrected Student
df and scale, so the parameter exponent describes actual tails. -/
theorem epistemicMatchedGammaOutcomeLaw_eq_studentMeasure (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    epistemicMatchedGammaOutcomeLaw μ v =
      studentMeasure μ (epistemicGammaTailIndex v) (epistemicGammaMatchScale v) :=
  epistemicNormalGammaLaw_eq_studentMeasure μ
    (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv)

/-- The actual matched-compound right survival has the source's
Student power exponent 2/(exp(v)-1), with a proved positive coefficient. -/
theorem epistemicMatchedGammaOutcomeLaw_survival_asymptotic (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun x : ℝ => (epistemicMatchedGammaOutcomeLaw μ v).real (Ioi x) /
      x ^ (-epistemicGammaTailIndex v)) atTop
      (𝓝 (studentSurvivalTailConstant (epistemicGammaTailIndex v) (epistemicGammaMatchScale v))) := by
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv]
  exact studentMeasure_survival_div_rpow_tendsto μ
    (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv)

theorem epistemicMatchedGammaOutcomeLaw_survival_regularlyVarying (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    IsRegularlyVarying (fun x => (epistemicMatchedGammaOutcomeLaw μ v).real (Ioi x))
      (-epistemicGammaTailIndex v) := by
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv]
  exact studentMeasure_survival_regularlyVarying μ
    (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv)

theorem epistemicMatchedGammaOutcomeLaw_leftTail_regularlyVarying (μ : ℝ) {v : ℝ} (hv : 0 < v) :
    IsRegularlyVarying (fun x => (epistemicMatchedGammaOutcomeLaw μ v).real (Iio (2 * μ - x)))
      (-epistemicGammaTailIndex v) := by
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv]
  exact studentMeasure_leftTail_regularlyVarying μ
    (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv)

/-- Section VI's heavier-tail conclusion for greater positive
epistemic variance, as a ratio of actual right-tail probabilities.
The scale changes too; the df comparison dominates asymptotically. -/
theorem epistemicMatchedGammaOutcomeLaw_survival_ratio_tendsto_zero (μ : ℝ)
    {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    Tendsto (fun x => (epistemicMatchedGammaOutcomeLaw μ v).real (Ioi x) /
      (epistemicMatchedGammaOutcomeLaw μ w).real (Ioi x)) atTop (𝓝 0) := by
  have hw : 0 < w := hv.trans hvw
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv,
    epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hw]
  exact studentMeasure_survival_ratio_tendsto_zero μ μ
    (epistemicGammaTailIndex_pos hv) (epistemicGammaTailIndex_pos hw)
    (epistemicGammaMatchScale_pos hv) (epistemicGammaMatchScale_pos hw)
    (epistemicGammaTailIndex_strictAnti hv hvw)

/-- Greater epistemic variance eventually makes the actual matched
Gamma outcome right-tail probability strictly larger (Section VI). -/
theorem eventually_epistemicMatchedGammaOutcomeLaw_survival_lt (μ : ℝ)
    {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    ∀ᶠ x in atTop, (epistemicMatchedGammaOutcomeLaw μ v).real (Ioi x) <
      (epistemicMatchedGammaOutcomeLaw μ w).real (Ioi x) := by
  have hw : 0 < w := hv.trans hvw
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv,
    epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hw]
  exact eventually_studentMeasure_survival_lt μ μ
    (epistemicGammaTailIndex_pos hv) (epistemicGammaTailIndex_pos hw)
    (epistemicGammaMatchScale_pos hv) (epistemicGammaMatchScale_pos hw)
    (epistemicGammaTailIndex_strictAnti hv hvw)

/-- Actual reflected left tails obey the same strict asymptotic
comparison, by whole-law reflection of the proper Student laws. -/
theorem epistemicMatchedGammaOutcomeLaw_leftTail_ratio_tendsto_zero (μ : ℝ)
    {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    Tendsto (fun x => (epistemicMatchedGammaOutcomeLaw μ v).real (Iio (2 * μ - x)) /
      (epistemicMatchedGammaOutcomeLaw μ w).real (Iio (2 * μ - x))) atTop (𝓝 0) := by
  have hw : 0 < w := hv.trans hvw
  have h := epistemicMatchedGammaOutcomeLaw_survival_ratio_tendsto_zero μ hv hvw
  rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hv,
    epistemicMatchedGammaOutcomeLaw_eq_studentMeasure μ hw] at h ⊢
  simpa only [studentMeasure_leftTail_eq_survival] using h

/-- At exactly zero epistemic log variance, the original source
Normal--Lognormal construction is a unit-variance Gaussian: precision
is the actual atom at one. The singular Gamma parameter values are
replaced by this boundary model, not a Student law of df zero. -/
theorem epistemicNormalLognormalLaw_zero_variance (μ : ℝ) :
    epistemicNormalLognormalLaw μ 0 0 = gaussianReal μ 1 := by
  have hp : epistemicLognormalScaleLaw 0 0 = Measure.dirac (1 : ℝ) := by
    unfold epistemicLognormalScaleLaw LognormalMeasure.lognormalReal
    simp only [gaussianReal_zero_var, Measure.map_dirac, Real.exp_zero, Real.one_rpow]
  rw [epistemicNormalLognormalLaw, hp]
  ext A hA
  rw [epistemicGaussianMixtureLaw_apply μ _ hA, lintegral_dirac]
  have he : NNReal.mk ((1 : ℝ) ^ 2) (sq_nonneg 1) = (1 : NNReal) := by ext; norm_num
  rw [he]

/-- The paper's exact matched Gamma approximation already loses a
finite mean at v=log(5), when its shape is 1/4. This proper centered
population refutes the unrestricted mean claim on the matched family. -/
theorem epistemicMatchedGammaOutcomeLaw_mean_counterexample :
    IsProbabilityMeasure (epistemicMatchedGammaOutcomeLaw 0 (Real.log 5)) ∧
      ¬Integrable (fun x : ℝ => x) (epistemicMatchedGammaOutcomeLaw 0 (Real.log 5)) := by
  have hv : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have ha : epistemicGammaMatchShape (Real.log 5) = 1 / 4 := by
    rw [epistemicGammaMatchShape, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    norm_num
  refine ⟨epistemicMatchedGammaOutcomeLaw_probability 0 hv, ?_⟩
  rw [epistemicMatchedGammaOutcomeLaw, epistemicNormalGammaLaw_integrable_iff 0
    (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv), ha]
  norm_num

example : IsProbabilityMeasure (epistemicMatchedGammaOutcomeLaw 1 1) :=
  epistemicMatchedGammaOutcomeLaw_probability 1 (by norm_num)

example : epistemicMatchedGammaOutcomeLaw 1 1 =
    studentMeasure 1 (epistemicGammaTailIndex 1) (epistemicGammaMatchScale 1) :=
  epistemicMatchedGammaOutcomeLaw_eq_studentMeasure 1 (by norm_num)

example : Tendsto (fun x : ℝ => (epistemicMatchedGammaOutcomeLaw 1 1).real (Ioi x) /
    x ^ (-epistemicGammaTailIndex 1)) atTop
    (𝓝 (studentSurvivalTailConstant (epistemicGammaTailIndex 1) (epistemicGammaMatchScale 1))) :=
  epistemicMatchedGammaOutcomeLaw_survival_asymptotic 1 (by norm_num)

example : IsRegularlyVarying (fun x => (epistemicMatchedGammaOutcomeLaw 1 1).real (Ioi x))
    (-epistemicGammaTailIndex 1) := epistemicMatchedGammaOutcomeLaw_survival_regularlyVarying 1 (by norm_num)

example : IsRegularlyVarying (fun x => (epistemicMatchedGammaOutcomeLaw 1 1).real (Iio (2 * 1 - x)))
    (-epistemicGammaTailIndex 1) := epistemicMatchedGammaOutcomeLaw_leftTail_regularlyVarying 1 (by norm_num)

example : Tendsto (fun x => (epistemicMatchedGammaOutcomeLaw 1 1).real (Ioi x) /
    (epistemicMatchedGammaOutcomeLaw 1 2).real (Ioi x)) atTop (𝓝 0) :=
  epistemicMatchedGammaOutcomeLaw_survival_ratio_tendsto_zero 1 (by norm_num) (by norm_num)

example : ∀ᶠ x in atTop, (epistemicMatchedGammaOutcomeLaw 1 1).real (Ioi x) <
    (epistemicMatchedGammaOutcomeLaw 1 2).real (Ioi x) :=
  eventually_epistemicMatchedGammaOutcomeLaw_survival_lt 1 (by norm_num) (by norm_num)

example : Tendsto (fun x => (epistemicMatchedGammaOutcomeLaw 1 1).real (Iio (2 * 1 - x)) /
    (epistemicMatchedGammaOutcomeLaw 1 2).real (Iio (2 * 1 - x))) atTop (𝓝 0) :=
  epistemicMatchedGammaOutcomeLaw_leftTail_ratio_tendsto_zero 1 (by norm_num) (by norm_num)

example : epistemicNormalLognormalLaw 1 0 0 = gaussianReal 1 1 :=
  epistemicNormalLognormalLaw_zero_variance 1

#print axioms epistemicMatchedGammaOutcomeLaw_survival_asymptotic
#print axioms epistemicMatchedGammaOutcomeLaw_survival_ratio_tendsto_zero
#print axioms epistemicMatchedGammaOutcomeLaw_leftTail_ratio_tendsto_zero
#print axioms epistemicNormalLognormalLaw_zero_variance
#print axioms epistemicMatchedGammaOutcomeLaw_mean_counterexample

end TailOptionPricing
