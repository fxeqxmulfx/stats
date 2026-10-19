module

/-
  Literal operational classes in arXiv:1907.11162v3, Definition 4, and
  Theorem 1's density-to-conditional-law bridge for linear payoff.
  Membership is witnessed by actual Gaussian, exponential and Pareto laws.
  Analytical classifications of additional laws are separate results.
-/
public import Stats.LayerCake
public import Stats.Probability.DensityIntegration
public import Stats.BinaryForecasts.Conflation
public import Stats.BinaryForecasts.GaussianLaw
public import Stats.BinaryForecasts.ExponentialLaw
public import Stats.BinaryForecasts.RegularVariationLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The literal operational limit in arXiv:1907.11162v3, Definition 4,
computed from the actual normalized conditional law. -/
def HasCharacteristicScale (ν : Measure ℝ) (scale : ℝ) : Prop :=
  Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂ν[|Ioi K]) / K) atTop (𝓝 scale)

/-- Definition 4's operational class D1. Analytical tail classifications
are separate implications, not built into this limit predicate. -/
def InThinTailClass (ν : Measure ℝ) : Prop := HasCharacteristicScale ν 1

/-- Definition 4's operational class D2, with a limit strictly above one. -/
def InFatTailClass (ν : Measure ℝ) : Prop :=
  ∃ scale : ℝ, 1 < scale ∧ HasCharacteristicScale ν scale

/-- Definition 4's borderline condition uses the actual conditional
mean minus the threshold, with a positive finite limiting excess. -/
def InBorderlineExponentialClass (ν : Measure ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂ν[|Ioi K]) - K) atTop (𝓝 m)

/-- A nonzero operational scale forces actual upper-tail normalization
and L1 eventually. The integral's totalized zero case cannot supply the
positive scales used by the paper's D1/D2 classes. -/
theorem HasCharacteristicScale.wellDefined (ν : Measure ℝ) [IsFiniteMeasure ν]
    {scale : ℝ} (h : HasCharacteristicScale ν scale) (hscale : scale ≠ 0) :
    ∀ᶠ K in atTop, IsProbabilityMeasure ν[|Ioi K] ∧
      Integrable (fun x : ℝ => x) ν[|Ioi K] ∧ IntegrableOn (fun x : ℝ => x) (Ioi K) ν := by
  unfold HasCharacteristicScale at h
  filter_upwards [h.eventually_ne hscale] with K hK
  have hm : (∫ x : ℝ, x ∂ν[|Ioi K]) ≠ 0 := by
    intro hz
    exact hK (by rw [hz, zero_div])
  have hn : ν (Ioi K) ≠ 0 := by
    intro hz
    exact hm (by rw [cond_eq_zero_of_meas_eq_zero hz, integral_zero_measure])
  have hf := measure_ne_top ν (Ioi K)
  have hi := Integrable.of_integral_ne_zero hm
  refine ⟨cond_isProbabilityMeasure_of_finite hn hf, hi, ?_⟩
  rw [ProbabilityTheory.cond] at hi
  exact (integrable_smul_measure (ENNReal.inv_ne_zero.mpr hf)
    (ENNReal.inv_ne_top.mpr hn)).mp hi

/-- The actual conditional-mean limit becomes the written density
I1/I2 limit for linear payoff, precisely the bridge in Theorem 1's proof. -/
theorem HasCharacteristicScale.densityRatio (ν : Measure ℝ) {scale : ℝ}
    (h : HasCharacteristicScale ν scale) {f : ℝ → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Tendsto (fun K : ℝ => I1 id f K / I2 id f K) atTop (𝓝 scale) := by
  have hi (K : ℝ) : (∫ x in Ioi K, x ∂ν) = I1 id f K := by
    rw [hν, realDensity_setIntegral f hm hn]
    rfl
  have hs (K : ℝ) : ν.real (Ioi K) = ∫ x in Ioi K, f x := by
    have he := realDensity_setIntegral f hm hn (fun _ => 1) (Ioi K)
    simp only [setIntegral_const, smul_eq_mul, mul_one, one_mul] at he
    simpa only [hν] using he
  unfold HasCharacteristicScale at h
  apply h.congr
  intro K
  rw [condMean_div_eq_tailMean_ratio, hi, hs]
  rfl

/-- Theorem 1's D1 implication under its literal Definition 4, for the
actual density and linear payoff. No analytical classification is assumed. -/
theorem thinTail_I1_div_I2_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : InThinTailClass ν) {f : ℝ → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    (∀ᶠ K in atTop, IsProbabilityMeasure ν[|Ioi K] ∧
      Integrable (fun x : ℝ => x) ν[|Ioi K] ∧ IntegrableOn (fun x : ℝ => x) (Ioi K) ν) ∧
      Tendsto (fun K : ℝ => I1 id f K / I2 id f K) atTop (𝓝 1) := by
  exact ⟨HasCharacteristicScale.wellDefined ν h one_ne_zero,
    HasCharacteristicScale.densityRatio ν h hm hn hν⟩

/-- Theorem 1's D2 implication with the actual Definition 4 limit and
identified density. Regular variation gives concrete members separately. -/
theorem fatTail_I1_div_I2_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : InFatTailClass ν) {f : ℝ → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ scale : ℝ, 1 < scale ∧
      (∀ᶠ K in atTop, IsProbabilityMeasure ν[|Ioi K] ∧
        Integrable (fun x : ℝ => x) ν[|Ioi K] ∧ IntegrableOn (fun x : ℝ => x) (Ioi K) ν) ∧
      Tendsto (fun K : ℝ => I1 id f K / I2 id f K) atTop (𝓝 scale) := by
  obtain ⟨scale, hscale, hs⟩ := h
  exact ⟨scale, hscale, HasCharacteristicScale.wellDefined ν hs (by linarith),
    HasCharacteristicScale.densityRatio ν hs hm hn hν⟩

/-- Actual standard Gaussian membership, from the proved Mills asymptotic. -/
theorem stdNormal_inThinTailClass : InThinTailClass (gaussianReal 0 1) :=
  stdNormal_condMean_ratio_tendsto

/-- Actual exponential membership in D1, from its proved conditional mean. -/
theorem expMeasure_inThinTailClass {r : ℝ} (hr : 0 < r) : InThinTailClass (expMeasure r) :=
  expMeasure_cond_characteristicScale_tendsto hr

/-- Actual strong Pareto membership in D2 for index greater than one. -/
theorem paretoMeasure_inFatTailClass {l α : ℝ} (hl : 0 < l) (hα : 1 < α) :
    InFatTailClass (paretoMeasure l α) :=
  ⟨α / (α - 1), characteristicScale_pareto_gt_one hα,
    paretoMeasure_cond_characteristicScale_tendsto hl hα⟩

/-- The actual exponential law meets Definition 4's separate positive
mean-excess limit, with reciprocal rate as that limit. -/
theorem expMeasure_inBorderlineExponentialClass {r : ℝ} (hr : 0 < r) :
    InBorderlineExponentialClass (expMeasure r) := by
  refine ⟨1 / r, one_div_pos.mpr hr, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK
  rw [expMeasure_cond_mean hr hK]
  ring

private instance expTwo_class_probability : IsProbabilityMeasure (expMeasure 2) :=
  isProbabilityMeasure_expMeasure (by norm_num)

private instance paretoTwoThree_class_probability : IsProbabilityMeasure (paretoMeasure 2 3) :=
  instIsProbabilityMeasureParetoMeasure 2 3 (by norm_num) (by norm_num)

example : InThinTailClass (expMeasure 2) := expMeasure_inThinTailClass (by norm_num)

example : InFatTailClass (paretoMeasure 2 3) :=
  paretoMeasure_inFatTailClass (by norm_num) (by norm_num)

example : InBorderlineExponentialClass (expMeasure 2) :=
  expMeasure_inBorderlineExponentialClass (by norm_num)

example : ∀ᶠ K : ℝ in atTop, IsProbabilityMeasure ((expMeasure 2)[|Ioi K]) ∧
    Integrable (fun x : ℝ => x) ((expMeasure 2)[|Ioi K]) ∧
    IntegrableOn (fun x : ℝ => x) (Ioi K) (expMeasure 2) :=
  HasCharacteristicScale.wellDefined _ (expMeasure_inThinTailClass (by norm_num)) one_ne_zero

example : Tendsto (fun K : ℝ => I1 id (exponentialPDFReal 2) K /
    I2 id (exponentialPDFReal 2) K) atTop (𝓝 1) :=
  HasCharacteristicScale.densityRatio _ (expMeasure_inThinTailClass (by norm_num))
    (measurable_exponentialPDFReal 2) (exponentialPDFReal_nonneg (by norm_num)) rfl

example : (∀ᶠ K : ℝ in atTop, IsProbabilityMeasure ((expMeasure 2)[|Ioi K]) ∧
    Integrable (fun x : ℝ => x) ((expMeasure 2)[|Ioi K]) ∧
    IntegrableOn (fun x : ℝ => x) (Ioi K) (expMeasure 2)) ∧
    Tendsto (fun K : ℝ => I1 id (exponentialPDFReal 2) K /
      I2 id (exponentialPDFReal 2) K) atTop (𝓝 1) :=
  thinTail_I1_div_I2_tendsto _ (expMeasure_inThinTailClass (by norm_num))
    (measurable_exponentialPDFReal 2) (exponentialPDFReal_nonneg (by norm_num)) rfl

example : ∃ scale : ℝ, 1 < scale ∧
    (∀ᶠ K : ℝ in atTop, IsProbabilityMeasure ((paretoMeasure 2 3)[|Ioi K]) ∧
      Integrable (fun x : ℝ => x) ((paretoMeasure 2 3)[|Ioi K]) ∧
      IntegrableOn (fun x : ℝ => x) (Ioi K) (paretoMeasure 2 3)) ∧
    Tendsto (fun K : ℝ =>
      I1 id (fun x => if 2 < x then paretoDensity 2 3 x else 0) K /
      I2 id (fun x => if 2 < x then paretoDensity 2 3 x else 0) K) atTop (𝓝 scale) := by
  let f : ℝ → ℝ := fun x => if 2 < x then paretoDensity 2 3 x else 0
  have hm : Measurable f := (paretoDensity_measurable 2 3).ite
    (measurableSet_lt measurable_const measurable_id) measurable_const
  have hn : ∀ x, 0 ≤ f x := by
    intro x
    dsimp only [f]
    split_ifs with h
    · have hx : 0 < x := by linarith
      unfold paretoDensity
      positivity
    · norm_num
  have hν : paretoMeasure 2 3 = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    unfold paretoMeasure
    congr 1
    funext x
    dsimp only [f]
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  exact fatTail_I1_div_I2_tendsto _
    (paretoMeasure_inFatTailClass (by norm_num) (by norm_num)) hm hn hν

#print axioms HasCharacteristicScale.wellDefined
#print axioms thinTail_I1_div_I2_tendsto
#print axioms fatTail_I1_div_I2_tendsto
#print axioms expMeasure_inBorderlineExponentialClass

end TailOptionPricing
