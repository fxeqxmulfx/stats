module

/-
  Actual supported exponential-law survival used in the exponential
  comparison of arXiv:1907.11162v3, Definition 4, and the growth-law
  transformation of arXiv:2007.16096v1, "Uncertainty goes one way".
-/
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Tactic.Linarith

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual exponential-law survival, including the support boundary.
The raw kernel integral over negative thresholds is a different quantity. -/
theorem expMeasure_real_Ioi {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (expMeasure r).real (Ioi c) = if 0 ≤ c then Real.exp (-(r * c)) else 1 := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h := measureReal_add_measureReal_compl (μ := expMeasure r)
    (s := Iic c) measurableSet_Iic
  rw [compl_Iic, probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hr] at h
  split_ifs with hc <;> split_ifs at h <;> linarith

example : (expMeasure 1).real (Ioi (-1)) = 1 := by
  rw [expMeasure_real_Ioi (by norm_num)]
  norm_num

end TailOptionPricing
