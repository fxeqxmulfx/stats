module

/-
  Inverting a supported Pareto tail for the finite-sample correction
  to arXiv:2004.05894v1, Remark 1. These are real-power identities;
  their use with actual observations is in SurvivalMass.lean.
-/
public import Stats.HiddenMoments.SurvivalKernel

@[expose] public section

open Real

namespace TailOptionPricing

/-- Threshold at which the Pareto survival equals `y`. -/
noncomputable def paretoSurvivalThreshold (l α y : ℝ) : ℝ :=
  l * y ^ (-(1 : ℝ) / α)

theorem paretoSurvivalThreshold_pos {l α y : ℝ} (hl : 0 < l) (hy : 0 < y) :
    0 < paretoSurvivalThreshold l α y :=
  mul_pos hl (Real.rpow_pos_of_pos hy _)

theorem paretoSurvivalThreshold_survival {l α y : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) :
    (l / paretoSurvivalThreshold l α y) ^ α = y := by
  have h := paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF (n := 1) hl hα hy
  simp only [paretoSampleSurvivalRatioCDF, paretoSampleMaxCDF, pow_one] at h
  unfold paretoSurvivalThreshold
  linarith

theorem paretoSurvivalThreshold_ge {l α y : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) (hy1 : y ≤ 1) :
    l ≤ paretoSurvivalThreshold l α y := by
  have hq := paretoSurvivalThreshold_pos (α := α) hl hy
  apply (div_le_one hq).mp
  apply (Real.rpow_le_rpow_iff (div_nonneg hl.le hq.le) zero_le_one hα).mp
  rw [paretoSurvivalThreshold_survival hl hα hy, Real.one_rpow]
  exact hy1

theorem paretoSurvival_ge_iff_le_threshold {l α y k : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) (hk : 0 < k) :
    y ≤ (l / k) ^ α ↔ k ≤ paretoSurvivalThreshold l α y := by
  have hq := paretoSurvivalThreshold_pos (α := α) hl hy
  conv_lhs => rw [← paretoSurvivalThreshold_survival hl hα hy]
  rw [Real.rpow_le_rpow_iff (div_nonneg hl.le hq.le) (div_nonneg hl.le hk.le) hα,
    div_le_div_iff₀ hq hk]
  constructor <;> intro h <;> nlinarith

theorem paretoSurvival_gt_iff_lt_threshold {l α y k : ℝ}
    (hl : 0 < l) (hα : 0 < α) (hy : 0 < y) (hk : 0 < k) :
    y < (l / k) ^ α ↔ k < paretoSurvivalThreshold l α y := by
  have hq := paretoSurvivalThreshold_pos (α := α) hl hy
  conv_lhs => rw [← paretoSurvivalThreshold_survival hl hα hy]
  rw [Real.rpow_lt_rpow_iff (div_nonneg hl.le hq.le) (div_nonneg hl.le hk.le) hα,
    div_lt_div_iff₀ hq hk]
  constructor <;> intro h <;> nlinarith

example : (1 / paretoSurvivalThreshold 1 2 (1 / 4)) ^ (2 : ℝ) = 1 / 4 :=
  paretoSurvivalThreshold_survival (by norm_num) (by norm_num) (by norm_num)

end TailOptionPricing
