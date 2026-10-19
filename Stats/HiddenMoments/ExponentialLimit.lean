module

/-
  Corrected exponential asymptotic for the actual hidden probability mass.
  Source: arXiv:2004.05894v1, Remark 1. The unscaled exact exponential law
  is false; (n+1)*H_(n+1) converges weakly to the actual Exp(1) measure.
-/
public import Stats.HiddenMoments.ScaledLaw
public import Stats.Probability.WeakCDF
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual scaled hidden-mass CDFs converge at every real threshold to
the actual Exp(1) CDF (arXiv:2004.05894v1, Remark 1 correction). -/
theorem scaledHiddenMassLaw_cdf_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) (t : ℝ) :
    Tendsto (fun n : ℕ => cdf (scaledHiddenMassLaw ν n : Measure ℝ) t) atTop
      (𝓝 (cdf (unitExponentialLaw : Measure ℝ) t)) := by
  have he : cdf (unitExponentialLaw : Measure ℝ) t =
      if 0 ≤ t then 1 - Real.exp (-t) else 0 := by
    change cdf (expMeasure 1) t = _
    rw [cdf_expMeasure_eq (by norm_num)]
    norm_num
  rw [he]
  by_cases ht : t ≤ 0
  · have hzero (n : ℕ) : cdf (scaledHiddenMassLaw ν n : Measure ℝ) t = 0 := by
      rw [scaledHiddenMassLaw_cdf ν hc, betaMeasure_one_nat_cdf (Nat.succ_pos n),
        ite_eq_left (div_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg _))]
    simp_rw [hzero]
    split_ifs with ht0
    · have ht' : t = 0 := le_antisymm ht ht0
      rw [ht']
      norm_num
    · exact tendsto_const_nhds
  · have ht0 : 0 < t := lt_of_not_ge ht
    rw [ite_eq_left ht0.le]
    have hlim : Tendsto (fun n : ℕ => 1 - (1 + -t / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
        atTop (𝓝 (1 - Real.exp (-t))) := tendsto_const_nhds.sub
      ((Real.tendsto_one_add_div_pow_exp (-t)).comp (tendsto_add_atTop_nat 1))
    apply hlim.congr'
    have hlarge : ∀ᶠ n : ℕ in atTop, t < ((n + 1 : ℕ) : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
        (eventually_gt_atTop t)
    filter_upwards [hlarge] with n hn
    have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    rw [scaledHiddenMassLaw_cdf ν hc, betaMeasure_one_nat_cdf (Nat.succ_pos n),
      ite_eq_right (not_le_of_gt (div_pos ht0 hn0)),
      ite_eq_right (not_le_of_gt ((div_lt_one hn0).mpr hn))]
    unfold paretoSampleSurvivalRatioCDF
    congr 2
    ring

/-- Full weak convergence of the actual scaled hidden-mass laws to Exp(1)
for any continuous-CDF population, extending arXiv:2004.05894v1, Remark 1. -/
theorem scaledHiddenMassLaw_tendsto (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hc : Continuous (cdf ν : ℝ → ℝ)) :
    Tendsto (scaledHiddenMassLaw ν) atTop (𝓝 unitExponentialLaw) := by
  exact probabilityMeasure_tendsto_of_cdf (scaledHiddenMassLaw_cdf_tendsto ν hc)

/-- The actual strong-Pareto CDF is continuous for all positive scale
and tail index, including laws with infinite mean (arXiv:2004.05894v1, section 1). -/
theorem continuous_paretoMeasure_cdf {l a : ℝ} (hl : 0 < l) (ha : 0 < a) :
    Continuous (cdf (paretoMeasure l a) : ℝ → ℝ) := by
  let : IsProbabilityMeasure (paretoMeasure l a) := instIsProbabilityMeasureParetoMeasure l a hl ha
  have he : (cdf (paretoMeasure l a) : ℝ → ℝ) =
      fun x : ℝ => 1 - (l / max l x) ^ a := by
    funext x
    rw [cdf_eq_real, paretoMeasure_real_Iic hl ha]
    by_cases hx : x < l
    · rw [ite_eq_left hx, max_eq_left hx.le, div_self hl.ne', Real.one_rpow, sub_self]
    · rw [ite_eq_right hx, max_eq_right (le_of_not_gt hx)]
  rw [he]
  exact continuous_const.sub ((continuous_const.div (continuous_const.max continuous_id)
    (fun x => (hl.trans_le (le_max_left l x)).ne')).rpow_const (fun _ => Or.inr ha.le))

/-- The corrected weak exponential asymptotic for every positive
strong-Pareto scale and tail index (arXiv:2004.05894v1, Remark 1).
No population moment condition is required. -/
theorem paretoScaledHiddenMassLaw_tendsto {l a : ℝ} (hl : 0 < l) (ha : 0 < a) :
    letI : IsProbabilityMeasure (paretoMeasure l a) :=
      instIsProbabilityMeasureParetoMeasure l a hl ha
    Tendsto (scaledHiddenMassLaw (paretoMeasure l a)) atTop (𝓝 unitExponentialLaw) := by
  let : IsProbabilityMeasure (paretoMeasure l a) := instIsProbabilityMeasureParetoMeasure l a hl ha
  exact scaledHiddenMassLaw_tendsto _ (continuous_paretoMeasure_cdf hl ha)

end TailOptionPricing
