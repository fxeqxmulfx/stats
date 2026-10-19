module

/-
  Regression model for the former unconditional lognormal PDF-tail formula.
  arXiv:1908.02347v3, Arbitrage Boundaries, uses positive strikes and positive
  volatility. Extending its logarithmic density formula outside that domain
  produced an incorrect global survival and incorrect degenerate call price.
-/
public import Stats.BlackScholes.StdNormal
public import Stats.BlackScholes.CallPrice.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatsReview

/-- The historical raw PDF tail, without support or zero-variance cases. -/
noncomputable def legacySurvivalLN (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) : ℝ :=
  ∫ x in Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x

/-- The historical call integral of that raw PDF tail. -/
noncomputable def legacyCallPriceBS (S₀ μ : ℝ) (v : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ s in Ioi K, legacySurvivalLN S₀ μ v s

/-- The old formula returned one half at threshold zero, although the
actual exponential Gaussian is strictly positive almost surely. -/
theorem legacySurvivalLN_zero_threshold : legacySurvivalLN 1 0 1 0 = 1 / 2 := by
  have hhalf : TailOptionPricing.stdNormalCdf 0 = 1 / 2 := by
    have h := TailOptionPricing.stdNormalCdf_neg 0
    norm_num at h
    linarith
  have htail := TailOptionPricing.one_sub_stdNormalCdf 0
  have hint : (gaussianReal 0 1).real (Ioi 0) =
      ∫ x in Ioi (0 : ℝ), gaussianPDFReal 0 1 x := by
    show ((gaussianReal 0 1) (Ioi 0)).toReal = _
    rw [gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ioi (fun x _ => gaussianPDFReal_nonneg 0 1 x))]
  norm_num [hhalf, hint] at htail
  simpa [legacySurvivalLN] using htail.symm

/-- The former PDF integral lost every zero-variance Gaussian atom. -/
theorem legacySurvivalLN_zero_var (S₀ μ s : ℝ) : legacySurvivalLN S₀ μ 0 s = 0 := by
  simp [legacySurvivalLN, gaussianPDFReal_zero_var]

/-- Consequently the former call price vanished at zero variance, even
for an in-the-money deterministic call. -/
theorem legacyCallPriceBS_zero_var (S₀ μ K : ℝ) : legacyCallPriceBS S₀ μ 0 K = 0 := by
  simp [legacyCallPriceBS, legacySurvivalLN_zero_var]

example : TailOptionPricing.survivalLN 1 0 1 0 ≠ legacySurvivalLN 1 0 1 0 := by
  rw [TailOptionPricing.survivalLN_of_nonpos (by norm_num) le_rfl,
    legacySurvivalLN_zero_threshold]
  norm_num

example : TailOptionPricing.callPriceBS 2 0 0 1 ≠ legacyCallPriceBS 2 0 0 1 := by
  rw [TailOptionPricing.callPriceBS_zero_var, legacyCallPriceBS_zero_var]
  norm_num

#print axioms legacySurvivalLN_zero_threshold
#print axioms legacyCallPriceBS_zero_var

end StatsReview
