module

/-
  Actual-law form of arXiv:1907.11162v3, Definition 4 and Theorem 1's
  regularly varying, linear-payoff branch. Measurable slowly varying
  tails with index greater than one give proved L1 and normalized laws.
-/
public import Stats.LayerCake
public import Stats.RegularVariation.Abelian.FullSV
public import Stats.RegularVariation.Examples
public import Stats.BinaryForecasts.CharacteristicScale

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual upper-tail observations are eventually L1 under the source's
measurable, eventually positive regularly varying survival representation.
No finite mean or conditional-mean formula is assumed. -/
theorem regularVariation_tail_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {L : ℝ → ℝ} {α : ℝ} (hα : 1 < α) (hLm : Measurable L)
    (hL : IsSlowlyVarying L) (hLp : ∀ᶠ s in atTop, 0 < L s)
    (hS : ∀ᶠ s in atTop, ν.real (Ioi s) = survivalSV L α s) :
    ∀ᶠ K in atTop, IntegrableOn (fun x : ℝ => x) (Ioi K) ν := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hS
  have hne := (callPriceSV_asymptotic hα hLm hL hLp).eventually_ne
    (by positivity : (1 : ℝ) / (α - 1) ≠ 0)
  filter_upwards [hne, eventually_ge_atTop T] with K hne hK
  have hi : IntegrableOn (survivalSV L α) (Ioi K) := by
    apply Integrable.of_integral_ne_zero
    intro hz
    apply hne
    change (∫ s in Ioi K, survivalSV L α s) / (L K * K ^ (1 - α)) = 0
    rw [hz, zero_div]
  apply integrableOn_id_of_integrableOn_survival ν K
  apply hi.congr_fun _ measurableSet_Ioi
  intro s hs
  exact (hT s (hK.trans hs.le)).symm

/-- Theorem 1's general RV linear-payoff ratio, for the actual survival
law with alpha greater than one. The first tail moment is genuine and L1. -/
theorem regularVariation_tailMean_ratio_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    {L : ℝ → ℝ} {α : ℝ} (hα : 1 < α) (hLm : Measurable L)
    (hL : IsSlowlyVarying L) (hLp : ∀ᶠ s in atTop, 0 < L s)
    (hS : ∀ᶠ s in atTop, ν.real (Ioi s) = survivalSV L α s) :
    Tendsto (fun K : ℝ => (∫ x in Ioi K, x ∂ν) / (K * ν.real (Ioi K)))
      atTop (𝓝 (α / (α - 1))) := by
  have hc : (1 : ℝ) + 1 / (α - 1) = α / (α - 1) := by
    have ha : α - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add (callPriceSV_asymptotic hα hLm hL hLp)
  rw [hc] at hlim
  obtain ⟨T, hT⟩ := eventually_atTop.mp hS
  apply hlim.congr'
  filter_upwards [regularVariation_tail_integrable ν hα hLm hL hLp hS,
    hS, hLp, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop T] with K hi hSK hLK hK hKT
  rw [tailMean_eq_threshold_survival_add_integral ν K hi]
  have hcall : (∫ s in Ioi K, ν.real (Ioi s)) = callPriceSV L α K := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact hT s (hKT.trans hs.le)
  rw [hcall, hSK]
  have hd : K * survivalSV L α K = L K * K ^ (1 - α) := by
    rw [show (1 - α : ℝ) = 1 + (-α) from by ring, Real.rpow_add hK, Real.rpow_one]
    unfold survivalSV
    ring
  rw [hd]
  have hn : L K * K ^ (1 - α) ≠ 0 :=
    mul_ne_zero hLK.ne' (Real.rpow_pos_of_pos hK _).ne'
  field_simp

/-- Actual normalized upper-tail laws are eventually probability laws
with integrable observations, making Definition 4's expectations meaningful. -/
theorem regularVariation_cond_probability_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {L : ℝ → ℝ} {α : ℝ} (hα : 1 < α) (hLm : Measurable L)
    (hL : IsSlowlyVarying L) (hLp : ∀ᶠ s in atTop, 0 < L s)
    (hS : ∀ᶠ s in atTop, ν.real (Ioi s) = survivalSV L α s) :
    ∀ᶠ K in atTop, IsProbabilityMeasure ν[|Ioi K] ∧
      Integrable (fun x : ℝ => x) ν[|Ioi K] := by
  filter_upwards [regularVariation_tail_integrable ν hα hLm hL hLp hS,
    hS, hLp, eventually_gt_atTop (0 : ℝ)] with K hi hSK hLK hK
  have hp : 0 < ν.real (Ioi K) := by
    rw [hSK, survivalSV]
    exact mul_pos hLK (Real.rpow_pos_of_pos hK _)
  have hn := (ENNReal.toReal_pos_iff.mp hp).1.ne'
  refine ⟨cond_isProbabilityMeasure_of_finite hn (measure_ne_top ν _), ?_⟩
  rw [ProbabilityTheory.cond]
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr hn)

/-- Definition 4's actual conditional-mean ratio and Theorem 1's
linear-payoff limit follow for all the specified regularly varying tails. -/
theorem regularVariation_condMean_ratio_tendsto (ν : Measure ℝ) [IsFiniteMeasure ν]
    {L : ℝ → ℝ} {α : ℝ} (hα : 1 < α) (hLm : Measurable L)
    (hL : IsSlowlyVarying L) (hLp : ∀ᶠ s in atTop, 0 < L s)
    (hS : ∀ᶠ s in atTop, ν.real (Ioi s) = survivalSV L α s) :
    Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂ν[|Ioi K]) / K)
      atTop (𝓝 (α / (α - 1))) := by
  simpa only [condMean_div_eq_tailMean_ratio] using
    regularVariation_tailMean_ratio_tendsto ν hα hLm hL hLp hS

private theorem paretoTwoThree_survivalSV :
    ∀ᶠ s : ℝ in atTop, (paretoMeasure 2 3).real (Ioi s) = survivalSV (fun _ => 8) 3 s := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  rw [paretoMeasure_real_Ioi_eq_survival (by norm_num) (by norm_num) hs,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ s), survivalSV,
    Real.rpow_neg (by linarith : 0 ≤ s)]
  norm_num [Real.rpow_ofNat, div_eq_mul_inv]

private theorem paretoTwoThree_slowlyVarying : IsSlowlyVarying (fun _ : ℝ => (8 : ℝ)) :=
  isSlowlyVarying_const (by norm_num)

private theorem paretoTwoThree_slowlyVarying_pos : ∀ᶠ s : ℝ in atTop, (0 : ℝ) < (fun _ => 8) s :=
  Filter.Eventually.of_forall (by norm_num)

private instance paretoTwoThree_probability : IsProbabilityMeasure (paretoMeasure 2 3) :=
  instIsProbabilityMeasureParetoMeasure 2 3 (by norm_num) (by norm_num)

example : ∀ᶠ K : ℝ in atTop, IntegrableOn (fun x : ℝ => x) (Ioi K) (paretoMeasure 2 3) :=
  regularVariation_tail_integrable _ (by norm_num) measurable_const
    paretoTwoThree_slowlyVarying paretoTwoThree_slowlyVarying_pos paretoTwoThree_survivalSV

example : Tendsto (fun K : ℝ => (∫ x in Ioi K, x ∂paretoMeasure 2 3) /
    (K * (paretoMeasure 2 3).real (Ioi K))) atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := regularVariation_tailMean_ratio_tendsto _ (by norm_num) measurable_const
    paretoTwoThree_slowlyVarying paretoTwoThree_slowlyVarying_pos paretoTwoThree_survivalSV
  norm_num at h
  exact h

example : ∀ᶠ K : ℝ in atTop, IsProbabilityMeasure ((paretoMeasure 2 3)[|Ioi K]) ∧
    Integrable (fun x : ℝ => x) ((paretoMeasure 2 3)[|Ioi K]) :=
  regularVariation_cond_probability_integrable _ (by norm_num) measurable_const
    paretoTwoThree_slowlyVarying paretoTwoThree_slowlyVarying_pos paretoTwoThree_survivalSV

example : Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(paretoMeasure 2 3)[|Ioi K]) / K)
    atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := regularVariation_condMean_ratio_tendsto _ (by norm_num) measurable_const
    paretoTwoThree_slowlyVarying paretoTwoThree_slowlyVarying_pos paretoTwoThree_survivalSV
  norm_num at h
  exact h

#print axioms regularVariation_tail_integrable
#print axioms regularVariation_tailMean_ratio_tendsto
#print axioms regularVariation_cond_probability_integrable
#print axioms regularVariation_condMean_ratio_tendsto

end TailOptionPricing
