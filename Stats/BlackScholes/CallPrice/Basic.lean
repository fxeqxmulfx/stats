module

/-
  The call integral for the actual lognormal law in arXiv:1908.02347v3,
  Arbitrage Boundaries. Layer cake identifies it with an integrable payoff
  for every strike and variance. Zero variance gives the intrinsic payoff.
-/
public import Stats.BlackScholes.Survival
public import Stats.LayerCake

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TailOptionPricing

/-- The lognormal call payoff at zero interest rates, written as an
integral of its actual survival. The choice `μ = -v/2` is risk-neutral. -/
noncomputable def callPriceBS (S₀ μ : ℝ) (v : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ s in Ioi K, survivalLN S₀ μ v s

/-- The call integral is the expectation of an integrable payoff under the
actual terminal-value law, including nonpositive strikes and zero variance. -/
theorem callPriceBS_eq_law_expectation (S₀ μ K : ℝ) (v : ℝ≥0) :
    callPriceBS S₀ μ v K = ∫ x, max (x - K) 0 ∂lognormalLaw S₀ μ v :=
  (expectation_max_eq_integral_survival (lognormalLaw S₀ μ v) K
    (integrable_lognormal_payoff S₀ μ K v)).symm

/-- Gaussian-driver form of the same genuine expectation. The earlier
positive-spot, positive-strike and nonzero-variance restrictions are
unnecessary after correcting the global survival function. -/
theorem callPriceBS_eq_expectation {S₀ μ K : ℝ} {v : ℝ≥0} :
    callPriceBS S₀ μ v K =
      ∫ x, max (S₀ * Real.exp x - K) 0 ∂gaussianReal μ v := by
  rw [callPriceBS_eq_law_expectation, lognormal_payoff_eq_gaussian]

/-- At zero variance the actual call price is the deterministic intrinsic
value. In particular, it need not be zero. -/
theorem callPriceBS_zero_var (S₀ μ K : ℝ) :
    callPriceBS S₀ μ 0 K = max (S₀ * Real.exp μ - K) 0 := by
  rw [callPriceBS_eq_law_expectation, lognormalLaw_zero_var]
  simp

/-- Nonnegativity of the actual call price for all model parameters. -/
theorem callPriceBS_nonneg (S₀ μ K : ℝ) (v : ℝ≥0) :
    0 ≤ callPriceBS S₀ μ v K := by
  rw [callPriceBS_eq_law_expectation]
  exact integral_nonneg (fun x => le_max_right (x - K) 0)

end TailOptionPricing
