module

/-
  The actual law of S₀ exp(X), X ~ N(μ,v), used in the Black–Scholes
  comparison of arXiv:1908.02347v3, Arbitrage Boundaries. For positive spot
  this law has positive support. Zero variance is the Gaussian Dirac case,
  not a zero density. Risk neutrality additionally requires μ = -v/2.
-/
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TailOptionPricing

/-- Gaussian pushforward by `x ↦ S₀ exp x`. For `S₀ > 0` this is the
lognormal law; the definition also covers zero variance and any real scale. -/
noncomputable def lognormalLaw (S₀ μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal μ v).map (fun x => S₀ * Real.exp x)

instance (S₀ μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (lognormalLaw S₀ μ v) := by
  unfold lognormalLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- The zero-variance Gaussian gives the deterministic terminal value,
including its atom. No density formula is used in this case. -/
theorem lognormalLaw_zero_var (S₀ μ : ℝ) :
    lognormalLaw S₀ μ 0 = Measure.dirac (S₀ * Real.exp μ) := by
  simp [lognormalLaw]

/-- Positive spot gives survival one at every nonpositive threshold,
including threshold zero, for every Gaussian variance. -/
theorem lognormalLaw_real_Ioi_of_nonpos {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hs : s ≤ 0) : (lognormalLaw S₀ μ v).real (Ioi s) = 1 := by
  have hpre : (fun x => S₀ * Real.exp x) ⁻¹' Ioi s = univ := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
    exact hs.trans_lt (mul_pos hS₀ (Real.exp_pos _))
  change ((gaussianReal μ v).map (fun x => S₀ * Real.exp x) (Ioi s)).toReal = 1
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
  simp

example : (lognormalLaw 1 0 1).real (Ioi 0) = 1 :=
  lognormalLaw_real_Ioi_of_nonpos (by norm_num) le_rfl

/-- The logarithmic Gaussian-tail transformation requires both a positive
spot and a positive threshold. It also holds for the degenerate Gaussian. -/
theorem lognormalLaw_real_Ioi_of_pos {S₀ μ s : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hs : 0 < s) :
    (lognormalLaw S₀ μ v).real (Ioi s) =
      (gaussianReal μ v).real (Ioi (Real.log (s / S₀))) := by
  have hpre : (fun x => S₀ * Real.exp x) ⁻¹' Ioi s = Ioi (Real.log (s / S₀)) := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    rw [Real.log_lt_iff_lt_exp (div_pos hs hS₀), div_lt_iff₀ hS₀]
    rw [mul_comm S₀]
  change ((gaussianReal μ v).map (fun x => S₀ * Real.exp x) (Ioi s)).toReal = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
  rfl

example : (lognormalLaw 1 0 1).real (Ioi 2) =
    (gaussianReal 0 1).real (Ioi (Real.log 2)) := by
  simpa using lognormalLaw_real_Ioi_of_pos (μ := 0) (v := 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)

/-- The actual call payoff is integrable for every strike, scale, Gaussian
mean and variance. This establishes a genuine expectation, not merely a
total Bochner integral with an unspecified integrability condition. -/
theorem integrable_lognormal_payoff (S₀ μ K : ℝ) (v : ℝ≥0) :
    Integrable (fun x => max (x - K) 0) (lognormalLaw S₀ μ v) := by
  have he : Integrable Real.exp (gaussianReal μ v) := by
    simpa using (integrable_exp_mul_gaussianReal (μ := μ) (v := v) 1)
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    (((he.const_mul S₀).sub (integrable_const K)).pos_part)

/-- Change of variables from the terminal-value law back to its Gaussian
driver. Together with integrability, this is the call-price law bridge. -/
theorem lognormal_payoff_eq_gaussian (S₀ μ K : ℝ) (v : ℝ≥0) :
    (∫ x, max (x - K) 0 ∂lognormalLaw S₀ μ v) =
      ∫ x, max (S₀ * Real.exp x - K) 0 ∂gaussianReal μ v := by
  exact integral_map (by fun_prop) (by fun_prop)

end TailOptionPricing
