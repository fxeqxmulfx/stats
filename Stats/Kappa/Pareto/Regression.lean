module

/-
  Regression certificates for the finite-Beta correction of Taleb's
  Pareto row, arXiv:1802.05495v3, Table I. The exact bound at alpha = 2
  excludes both the former zero ratio and its constant kappa value two.
  These are analytic certificates, not a replacement for a probability-law
  theorem identifying the expression with an actual iid-sum MAD.
-/
public import Stats.Kappa.Pareto.LowerBounds
public import Stats.Kappa.Pareto.RationalIntegral

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

/-- An exact rational bound for the corrected Table I ratio at `α = 2`.
The lower bound is derived by integration, not numerical quadrature. -/
theorem paretoRatio_two_lower_bound : (207 / 160 : ℝ) ≤ paretoRatio 2 := by
  have hi := paretoIntegrand_intervalIntegrable (by norm_num : (1 : ℝ) < 2)
  norm_num at hi
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    (pareto_two_rational_intervalIntegrable.const_mul 216) hi
    (fun y hy => paretoIntegrand_two_lower_bound hy.1 hy.2)
  rw [intervalIntegral.integral_const_mul, pareto_two_rational_integral] at h
  have hR : paretoRatio 2 = 2 * ∫ y in (0 : ℝ)..2, paretoIntegrand 2 y := by
    unfold paretoRatio
    norm_num
  calc
    (207 / 160 : ℝ) = 2 * (216 * (23 / 7680)) := by norm_num
    _ ≤ 2 * ∫ y in (0 : ℝ)..2, paretoIntegrand 2 y :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = paretoRatio 2 := hR.symm

/-- The corrected ratio is strictly above one at `α = 2`, so its
logarithmic denominator is in the ordinary positive domain. -/
theorem paretoRatio_two_gt_one : 1 < paretoRatio 2 := by
  linarith [paretoRatio_two_lower_bound]

/-- The corrected κ expression is strictly below two at `α = 2`.
This rules out the old divergent-integral degeneration. -/
theorem paretoKappa_two_lt_two : paretoKappa 2 < 2 := by
  apply sub_lt_self
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos paretoRatio_two_gt_one)

#print axioms paretoRatio_two_lower_bound
#print axioms paretoKappa_two_lt_two

end TailOptionPricing
