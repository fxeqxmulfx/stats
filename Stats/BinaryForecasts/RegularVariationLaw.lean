module

/-
  arXiv:1907.11162v3, Definition 4 and Theorem 1, RV branch.
  The hypotheses concern the actual law's survival function itself.
  Its slowly varying factor, upper-tail L1 and normalized conditional
  means are derived, including for laws with an uncontrolled lower tail.
-/
public import Stats.BinaryForecasts.RegularVariation
public import Stats.RegularVariation.Closure
public import Stats.BinaryForecasts.Conflation
public import Stats.Probability.DensityIntegration

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual survival is eventually positive under regular variation;
nonempty tails need not be assumed separately (paper Theorem 1, RV branch). -/
theorem regularlyVarying_survival_eventually_pos (ν : Measure ℝ) {α : ℝ}
    (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    ∀ᶠ s in atTop, 0 < ν.real (Ioi s) := by
  have hlim := hRV 1 zero_lt_one
  simp only [mul_one, Real.one_rpow] at hlim
  filter_upwards [hlim.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with s hs
  by_contra hp
  have hz : ν.real (Ioi s) = 0 := le_antisymm (not_lt.mp hp) measureReal_nonneg
  exact hs (by rw [hz, zero_div])

/-- The slowly varying factor is recovered from the actual survival law,
not postulated as an unrelated function. -/
private theorem survival_slowlyVarying_factor (ν : Measure ℝ) [IsFiniteMeasure ν]
    {α : ℝ} (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    ∃ L : ℝ → ℝ, Measurable L ∧ IsSlowlyVarying L ∧
      (∀ᶠ s in atTop, 0 < L s) ∧ (∀ᶠ s in atTop, ν.real (Ioi s) = survivalSV L α s) := by
  have hp := regularlyVarying_survival_eventually_pos ν hRV
  have ha : Antitone (fun s : ℝ => ν.real (Ioi s)) := by
    intro a b hab
    exact measureReal_mono (Ioi_subset_Ioi hab)
  refine ⟨(fun s : ℝ => ν.real (Ioi s) / s ^ (-α)),
    ha.measurable.div (measurable_id.pow_const (-α)), hRV.div_rpow_isSlowlyVarying hp, ?_, ?_⟩
  · filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with s hs hsp
    exact div_pos hs (Real.rpow_pos_of_pos hsp _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    change ν.real (Ioi s) = (ν.real (Ioi s) / s ^ (-α)) * s ^ (-α)
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hs _).ne']

/-- General regularly varying actual-survival form of Theorem 1 for
`g(x)=x` and alpha greater than one; upper-tail positivity is derived. -/
theorem regularlyVarying_survival_tailMean_ratio_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    {α : ℝ} (hα : 1 < α)
    (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    Tendsto (fun K : ℝ => (∫ x in Ioi K, x ∂ν) / (K * ν.real (Ioi K)))
      atTop (𝓝 (α / (α - 1))) := by
  obtain ⟨L, hLm, hL, hLp, hS⟩ := survival_slowlyVarying_factor ν hRV
  exact regularVariation_tailMean_ratio_tendsto ν hα hLm hL hLp hS

/-- The actual upper-tail conditional laws are eventually normalized and
L1 under the distributional hypotheses of the paper's RV branch. -/
theorem regularlyVarying_survival_cond_probability_integrable (ν : Measure ℝ)
    [IsFiniteMeasure ν] {α : ℝ} (hα : 1 < α)
    (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    ∀ᶠ K in atTop, IsProbabilityMeasure ν[|Ioi K] ∧
      Integrable (fun x : ℝ => x) ν[|Ioi K] := by
  obtain ⟨L, hLm, hL, hLp, hS⟩ := survival_slowlyVarying_factor ν hRV
  exact regularVariation_cond_probability_integrable ν hα hLm hL hLp hS

/-- Definition 4's actual conditional-mean ratio for every actual law
with the specified regularly varying survival; its limit exceeds one. -/
theorem regularlyVarying_survival_condMean_ratio_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    {α : ℝ} (hα : 1 < α)
    (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂ν[|Ioi K]) / K)
      atTop (𝓝 (α / (α - 1))) := by
  obtain ⟨L, hLm, hL, hLp, hS⟩ := survival_slowlyVarying_factor ν hRV
  exact regularVariation_condMean_ratio_tendsto ν hα hLm hL hLp hS

/-- The printed `I1/I2` limit for a nonnegative measurable density of
an actual finite law, with a regularly varying actual survival (Theorem 1).
The law's tail L1 and conditional normalization are proved above. -/
theorem regularlyVarying_density_I1_div_I2_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    {f : ℝ → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {α : ℝ} (hα : 1 < α)
    (hRV : IsRegularlyVarying (fun s : ℝ => ν.real (Ioi s)) (-α)) :
    Tendsto (fun K : ℝ => I1 id f K / I2 id f K) atTop (𝓝 (α / (α - 1))) := by
  have hi (K : ℝ) : (∫ x in Ioi K, x ∂ν) = I1 id f K := by
    rw [hν, realDensity_setIntegral f hm hn]
    rfl
  have hs (K : ℝ) : ν.real (Ioi K) = ∫ x in Ioi K, f x := by
    have h := realDensity_setIntegral f hm hn (fun _ => 1) (Ioi K)
    simp only [setIntegral_const, smul_eq_mul, mul_one, one_mul] at h
    simpa only [hν] using h
  apply (regularlyVarying_survival_tailMean_ratio_tendsto ν hα hRV).congr
  intro K
  rw [hi, hs]
  rfl

private theorem paretoTwoThree_actual_survival_RV :
    IsRegularlyVarying (fun s : ℝ => (paretoMeasure 2 3).real (Ioi s)) (-3) := by
  intro x hx
  have hlim := survival_isRegularlyVarying (l := 2) (α := 3) (by norm_num) x hx
  apply hlim.congr'
  have hm : Tendsto (fun t : ℝ => t * x) atTop atTop := tendsto_id.atTop_mul_const hx
  filter_upwards [eventually_ge_atTop (2 : ℝ), hm.eventually (eventually_ge_atTop (2 : ℝ))]
    with t ht htx
  rw [paretoMeasure_real_Ioi_eq_survival (by norm_num) (by norm_num) ht,
    paretoMeasure_real_Ioi_eq_survival (by norm_num) (by norm_num) htx]
  rfl

example : ∀ᶠ s : ℝ in atTop, 0 < (paretoMeasure 2 3).real (Ioi s) :=
  regularlyVarying_survival_eventually_pos _ paretoTwoThree_actual_survival_RV

private instance paretoTwoThree_actual_probability : IsProbabilityMeasure (paretoMeasure 2 3) :=
  instIsProbabilityMeasureParetoMeasure 2 3 (by norm_num) (by norm_num)

example : Tendsto (fun K : ℝ => (∫ x in Ioi K, x ∂paretoMeasure 2 3) /
    (K * (paretoMeasure 2 3).real (Ioi K))) atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := regularlyVarying_survival_tailMean_ratio_tendsto _ (by norm_num)
    paretoTwoThree_actual_survival_RV
  norm_num at h
  exact h

example : ∀ᶠ K : ℝ in atTop, IsProbabilityMeasure ((paretoMeasure 2 3)[|Ioi K]) ∧
    Integrable (fun x : ℝ => x) ((paretoMeasure 2 3)[|Ioi K]) :=
  regularlyVarying_survival_cond_probability_integrable _ (by norm_num)
    paretoTwoThree_actual_survival_RV

example : Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(paretoMeasure 2 3)[|Ioi K]) / K)
    atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := regularlyVarying_survival_condMean_ratio_tendsto _ (by norm_num)
    paretoTwoThree_actual_survival_RV
  norm_num at h
  exact h

private noncomputable def paretoTwoThreePDF (x : ℝ) : ℝ :=
  if 2 < x then paretoDensity 2 3 x else 0

private theorem paretoTwoThreePDF_measurable : Measurable paretoTwoThreePDF :=
  (paretoDensity_measurable 2 3).ite
    (measurableSet_lt measurable_const measurable_id) measurable_const

private theorem paretoTwoThreePDF_nonneg (x : ℝ) : 0 ≤ paretoTwoThreePDF x := by
  unfold paretoTwoThreePDF
  split_ifs with h
  · have hx : 0 < x := by linarith
    unfold paretoDensity
    positivity
  · norm_num

private theorem paretoTwoThreePDF_law :
    paretoMeasure 2 3 = volume.withDensity (fun x => ENNReal.ofReal (paretoTwoThreePDF x)) := by
  unfold paretoMeasure paretoTwoThreePDF
  congr 1
  funext x
  split_ifs <;> simp only [ENNReal.ofReal_zero]

example : Tendsto (fun K : ℝ => I1 id paretoTwoThreePDF K / I2 id paretoTwoThreePDF K)
    atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := regularlyVarying_density_I1_div_I2_tendsto _ paretoTwoThreePDF_measurable
    paretoTwoThreePDF_nonneg paretoTwoThreePDF_law (by norm_num)
    paretoTwoThree_actual_survival_RV
  norm_num at h
  exact h

#print axioms regularlyVarying_survival_eventually_pos
#print axioms regularlyVarying_survival_tailMean_ratio_tendsto
#print axioms regularlyVarying_survival_cond_probability_integrable
#print axioms regularlyVarying_survival_condMean_ratio_tendsto

#print axioms regularlyVarying_density_I1_div_I2_tendsto

end TailOptionPricing
