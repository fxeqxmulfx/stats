module

/-
  The supported exponential-law interpretation of the raw tail integral
  in arXiv:1907.11162v3, Definition 4. Nonnegative thresholds are essential
  for identifying the globally defined kernel with a probability tail.
-/
public import Stats.BinaryForecasts.Exponential
public import Stats.Probability.Exponential

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The raw tail integral equals the actual exponential-law survival
only on the nonnegative support domain (arXiv:1907.11162v3, Definition 4). -/
theorem exp_survival_eq_measure {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    (∫ x in Ioi K, expDensity lam x) = (expMeasure lam).real (Ioi K) := by
  rw [exp_survival_eq hlam, expMeasure_real_Ioi hlam, ite_eq_left hK]

example : (∫ x in Ioi (1 : ℝ), expDensity 1 x) = (expMeasure 1).real (Ioi 1) :=
  exp_survival_eq_measure (by norm_num) (by norm_num)

-- The omitted support case cannot be given a probability interpretation.
example : (expMeasure 1).real (Ioi (-1)) < ∫ x in Ioi (-1 : ℝ), expDensity 1 x := by
  rw [exp_survival_eq (by norm_num), expMeasure_real_Ioi (by norm_num)]
  norm_num

end TailOptionPricing
