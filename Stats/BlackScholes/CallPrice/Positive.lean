module

/-
  Strict positivity of genuine lognormal tails and calls for positive
  variance, as used in the Black–Scholes comparison of arXiv:1908.02347v3.
-/
public import Stats.BlackScholes.CallPrice.ClosedForm

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace TailOptionPricing

/-- A nondegenerate positive lognormal law has positive survival at every
finite threshold; outside its positive support that survival is one. -/
theorem survivalLN_pos {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (s : ℝ) : 0 < survivalLN S₀ μ v s := by
  by_cases hs : 0 < s
  · rw [survivalLN_eq_one_sub_stdNormalCdf hS₀ hv hs]
    exact sub_pos.mpr (stdNormalCdf_lt_one _)
  · rw [survivalLN_of_nonpos hS₀ (le_of_not_gt hs)]
    norm_num

example : 0 < survivalLN 1 0 1 2 := survivalLN_pos (by norm_num) (by norm_num) 2

/-- Every finite positive-strike lognormal call has strictly positive
value when the spot and variance are positive. -/
theorem callPriceBS_pos {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) : 0 < callPriceBS S₀ μ v K := by
  have hp := survivalLN_pos (μ := μ) hS₀ hv
  have hsupp : Function.support (survivalLN S₀ μ v) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp x).ne'
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun x => (hp x).le)) (integrableOn_survivalLN hS₀ hK)).mpr
  rw [hsupp, univ_inter, Real.volume_Ioi]
  simp

example : 0 < callPriceBS 1 0 1 2 :=
  callPriceBS_pos (by norm_num) (by norm_num) (by norm_num)

end TailOptionPricing
