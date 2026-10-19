module

/-
  Actual Pareto conditional means and characteristic-scale limits for
  arXiv:1907.11162v3, Definition 4 and the linear-payoff Pareto case.
  The ratio classification is separate from finite second moments.
-/
public import Stats.Pareto.TailRisk
public import Stats.Pareto.Moments
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The strong-Pareto tail-integral ratio in Definition 4 is constant
above the support boundary; actual conditional laws are computed below. -/
theorem characteristicScale_pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / (K * survival l α K) = α / (α - 1) := by
  have hK_pos : 0 < K := hl.trans_le hK
  have hK_ne : K ≠ 0 := hK_pos.ne'
  have h := paretoTailExpectation_div_survival hα hl hK
  -- paretoTailExpectation/survival = α·K/(α-1)
  have h_surv_pos : 0 < survival l α K := by
    unfold survival; positivity
  have h_surv_ne : survival l α K ≠ 0 := h_surv_pos.ne'
  -- LHS = (paretoTailExpectation/survival) / K = (α·K/(α-1)) / K = α/(α-1).
  rw [show paretoTailExpectation l α K / (K * survival l α K)
        = (paretoTailExpectation l α K / survival l α K) / K from by
      field_simp]
  rw [h]
  field_simp

/-- The Pareto factor is greater than one for index greater than one. -/
theorem characteristicScale_pareto_gt_one {α : ℝ} (hα : 1 < α) :
    1 < α / (α - 1) := by
  have hα1_pos : 0 < α - 1 := by linarith
  rw [lt_div_iff₀ hα1_pos, one_mul]
  linarith

/-- Actual Pareto upper tails have positive probability at every finite
threshold, supplying normalization in arXiv:1907.11162v3, Definition 4. -/
theorem paretoMeasure_real_Ioi_pos {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (K : ℝ) :
    0 < (paretoMeasure l α).real (Ioi K) := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  have hp : 0 < (paretoMeasure l α).real (Ioi (max l K)) := by
    rw [paretoMeasure_real_Ioi_eq_survival hl hα (le_max_left _ _)]
    exact Real.rpow_pos_of_pos (div_pos hl (hl.trans_le (le_max_left _ _))) _
  exact hp.trans_le (measureReal_mono (Ioi_subset_Ioi (le_max_right _ _)))

/-- The actual normalized Pareto upper-tail restriction is a probability
measure at every finite threshold (paper Definition 4). -/
theorem paretoMeasure_cond_probability {l α : ℝ} (hl : 0 < l) (hα : 0 < α) (K : ℝ) :
    IsProbabilityMeasure ((paretoMeasure l α)[|Ioi K]) := by
  have h := ENNReal.toReal_pos_iff.mp (paretoMeasure_real_Ioi_pos hl hα K)
  exact cond_isProbabilityMeasure_of_finite h.1.ne' h.2.ne

/-- For index greater than one the actual conditional observation is L1;
the mean is not supplied as a hypothesis (paper Definition 4). -/
theorem paretoMeasure_cond_integrable_id {l α : ℝ} (hl : 0 < l) (hα : 1 < α) (K : ℝ) :
    Integrable (fun x : ℝ => x) ((paretoMeasure l α)[|Ioi K]) := by
  have hα0 : 0 < α := by linarith
  rw [ProbabilityTheory.cond]
  apply ((paretoMeasure_integrable_id_iff hl hα0).mpr hα).integrableOn.smul_measure
  exact ENNReal.inv_ne_top.mpr
    (ENNReal.toReal_pos_iff.mp (paretoMeasure_real_Ioi_pos hl hα0 K)).1.ne'

/-- Actual conditional mean under the normalized Pareto tail law,
matching the strong-Pareto calculation following the paper's Theorem 1. -/
theorem paretoMeasure_cond_mean {l α K : ℝ} (hl : 0 < l) (hα : 1 < α) (hK : l ≤ K) :
    (∫ x : ℝ, x ∂(paretoMeasure l α)[|Ioi K]) = α * K / (α - 1) := by
  have hα0 : 0 < α := by linarith
  have htail : (∫ x in Ioi K, x ∂paretoMeasure l α) = paretoTailExpectation l α K := by
    simpa only [paretoTailMoment, Real.rpow_one, paretoDensity, paretoTailExpectation] using
      paretoMeasure_tailMoment hl hα0 1 hK
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  change ((paretoMeasure l α).real (Ioi K))⁻¹ * (∫ x in Ioi K, x ∂paretoMeasure l α) = _
  rw [htail, paretoMeasure_real_Ioi_eq_survival hl hα0 hK]
  simpa only [survival, div_eq_mul_inv, mul_comm] using
    paretoTailExpectation_div_survival hα hl hK

/-- Actual Pareto mean excess grows linearly with the threshold,
under the L1 and normalization conditions of paper Definition 4. -/
theorem paretoMeasure_cond_mean_excess {l α K : ℝ}
    (hl : 0 < l) (hα : 1 < α) (hK : l ≤ K) :
    (∫ x : ℝ, x - K ∂(paretoMeasure l α)[|Ioi K]) = K / (α - 1) := by
  let : IsProbabilityMeasure ((paretoMeasure l α)[|Ioi K]) :=
    paretoMeasure_cond_probability hl (by linarith) K
  rw [integral_sub (paretoMeasure_cond_integrable_id hl hα K) (integrable_const K),
    paretoMeasure_cond_mean hl hα hK, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have ha : α - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The actual conditional-mean ratio equals the source's Pareto factor
at every threshold above the support (Definition 4, linear-payoff case). -/
theorem paretoMeasure_cond_characteristicScale {l α K : ℝ}
    (hl : 0 < l) (hα : 1 < α) (hK : l ≤ K) :
    (∫ x : ℝ, x ∂(paretoMeasure l α)[|Ioi K]) / K = α / (α - 1) := by
  rw [paretoMeasure_cond_mean hl hα hK]
  have hKn : K ≠ 0 := (hl.trans_le hK).ne'
  field_simp

/-- The actual Pareto conditional-mean ratio converges to `α/(α-1)>1`.
This proves Definition 4's operational limit, without identifying all RV laws. -/
theorem paretoMeasure_cond_characteristicScale_tendsto {l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) :
    Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(paretoMeasure l α)[|Ioi K]) / K)
      atTop (𝓝 (α / (α - 1))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop l] with K hK
  exact (paretoMeasure_cond_characteristicScale hl hα hK).symm

-- A genuine Pareto(2,3) law above four: conditional mean six, excess two.
example : 0 < (paretoMeasure 2 3).real (Ioi (-1)) :=
  paretoMeasure_real_Ioi_pos (by norm_num) (by norm_num) _

example : IsProbabilityMeasure ((paretoMeasure 2 3)[|Ioi (4 : ℝ)]) :=
  paretoMeasure_cond_probability (by norm_num) (by norm_num) _

example : ∀ᵐ x ∂(paretoMeasure 2 3)[|Ioi (4 : ℝ)], 4 < x := ae_cond_mem measurableSet_Ioi

example : Integrable (fun x : ℝ => x) ((paretoMeasure 2 3)[|Ioi 4]) :=
  paretoMeasure_cond_integrable_id (by norm_num) (by norm_num) _

example : (∫ x : ℝ, x ∂(paretoMeasure 2 3)[|Ioi 4]) = 6 := by
  rw [paretoMeasure_cond_mean (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : (∫ x : ℝ, x - 4 ∂(paretoMeasure 2 3)[|Ioi 4]) = 2 := by
  rw [paretoMeasure_cond_mean_excess (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : (∫ x : ℝ, x ∂(paretoMeasure 2 3)[|Ioi 4]) / 4 = 3 / 2 := by
  have h := paretoMeasure_cond_characteristicScale (l := 2) (α := 3) (K := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : Tendsto (fun K : ℝ => (∫ x : ℝ, x ∂(paretoMeasure 2 3)[|Ioi K]) / K)
    atTop (𝓝 (3 / 2 : ℝ)) := by
  have h := paretoMeasure_cond_characteristicScale_tendsto (l := 2) (α := 3)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : paretoTailExpectation 2 3 4 / (4 * survival 2 3 4) = 3 / 2 := by
  have h := characteristicScale_pareto (l := 2) (α := 3) (K := 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : 1 < (3 : ℝ) / (3 - 1) := characteristicScale_pareto_gt_one (by norm_num)

-- This ratio greater than one coexists with a finite actual second moment.
example : Integrable (fun x : ℝ => x ^ (2 : ℝ)) (paretoMeasure 2 3) :=
  (paretoMeasure_integrable_rpow_iff (by norm_num) (by norm_num)).mpr (by norm_num)

example : (∫ x : ℝ, x ^ (2 : ℝ) ∂paretoMeasure 2 3) = 12 := by
  rw [paretoMeasure_integral_rpow (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Real.rpow_ofNat]

#print axioms paretoMeasure_real_Ioi_pos
#print axioms paretoMeasure_cond_integrable_id
#print axioms paretoMeasure_cond_mean
#print axioms paretoMeasure_cond_mean_excess
#print axioms paretoMeasure_cond_characteristicScale_tendsto

end TailOptionPricing
