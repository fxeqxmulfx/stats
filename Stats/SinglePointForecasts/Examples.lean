module

/-
  Concrete supported laws witness the hypotheses of the empirical-survival
  repair for arXiv:2007.16096v1, line 235. The two-observation examples use
  a nondegenerate independent product, rather than assumed moment formulas.
-/
public import Stats.SinglePointForecasts.FairCoin

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

example : variance ((Ioi (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ))) fairCoinLaw =
    1 / 4 := by
  rw [indicator_one_variance measurableSet_Ioi, fairCoinLaw_survival]
  norm_num

example : Measurable (empiricalEventAverage (fun _ : Fin 2 => Ioi (1 / 2 : ℝ))) :=
  measurable_empiricalEventAverage (fun _ => measurableSet_Ioi)

example : MemLp (empiricalEventAverage (fun _ : Fin 2 => Ioi (1 / 2 : ℝ))) 2
    fairCoinLaw := empiricalEventAverage_memLp (fun _ => measurableSet_Ioi)

-- Equal event probabilities give the mean even for identical observations.
example : (∫ ω, empiricalEventAverage (fun _ : Fin 2 => Ioi (1 / 2 : ℝ)) ω
    ∂fairCoinLaw) = 1 / 2 :=
  empiricalEventAverage_integral (by norm_num) (fun _ => measurableSet_Ioi)
    (fun _ => fairCoinLaw_survival)

example : variance (empiricalEventAverage (fun _ : Fin 1 => Ioi (1 / 2 : ℝ)))
    fairCoinLaw = 1 / 4 := by
  have h := empiricalEventAverage_variance (μ := fairCoinLaw) (n := 1)
    (A := fun _ => Ioi (1 / 2 : ℝ)) (p := 1 / 2) (by norm_num)
    (fun _ => measurableSet_Ioi)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (fun _ => fairCoinLaw_survival)
  norm_num at h
  exact h

example : (∫ ω, empiricalSurvival (fun i (ω : Fin 2 → ℝ) => ω i) (1 / 2) ω
    ∂fairCoinSampleLaw 2) = 1 / 2 := by
  have h := empiricalSurvival_integral (ν := fairCoinLaw) (1 / 2)
    (by norm_num : 0 < 2) (fun i => measurable_pi_apply i) (fairCoinSample_map 2)
  rw [fairCoinLaw_survival] at h
  exact h

example : variance (empiricalSurvival (fun i (ω : Fin 2 → ℝ) => ω i) (1 / 2))
    (fairCoinSampleLaw 2) = 1 / 8 := by
  have h := fairCoin_empiricalSurvival_variance 2 (by norm_num)
  norm_num at h
  exact h

example : Integrable (fun ω : Fin 2 → ℝ =>
    (empiricalSurvival (fun i ω => ω i) (1 / 2) ω - 1 / 2)^2) (fairCoinSampleLaw 2) :=
  integrable_empiricalSurvival_sq_error (1 / 2) (1 / 2) (fun i => measurable_pi_apply i)

example : fairCoinMSE 2 = 1 / 8 := by
  have h := fairCoinMSE_eq 2 (by norm_num)
  norm_num at h
  exact h

example : variance (empiricalSurvival (fun i (ω : Fin 2 → ℝ) => ω i) (1 / 2))
    (fairCoinSampleLaw 2) ≤ 1 / (4 * 2) :=
  empiricalSurvival_variance_bound (ν := fairCoinLaw) (1 / 2) (by norm_num)
    (fun i => measurable_pi_apply i)
    (fun _ _ hij => (fairCoinSample_indep 2).indepFun hij) (fairCoinSample_map 2)

example : Real.sqrt (fairCoinMSE 2) ≤ 1 / (2 * Real.sqrt 2) := by
  have h := empiricalSurvival_rmse_bound (ν := fairCoinLaw) (1 / 2)
    (by norm_num : 0 < 2) (fun i => measurable_pi_apply i)
    (fun _ _ hij => (fairCoinSample_indep 2).indepFun hij) (fairCoinSample_map 2)
  rw [fairCoinLaw_survival] at h
  exact h

example : (1 / 2 : ℝ) * (1 - 1 / 2) ≤ 1 / 4 := bernoulli_variance_bound

example : (1 / 2 : ℝ) * (1 - 1 / 2) / 4 ≤ 1 / (4 * 4) :=
  empirical_survival_variance_bound (by norm_num)

example : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2) / 4) ≤ 1 / (2 * Real.sqrt 4) :=
  empirical_survival_std_bound (by norm_num)

example : (1 : ℝ) / (1 * 2) * (1 / 2) ^ (1 / 1 : ℝ) =
    paretoDensity 1 (1 / 1) 2 :=
  exp_growth_density_eq_pareto (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ((1 : ℝ) / 1) * 1 * Real.sqrt (1 / 1^2) = 1 :=
  exp_growth_tail_index_variance_relation (by norm_num) (by norm_num)

example : ¬IntegrableOn (paretoMomentIntegrand 1 1 1) (Ioi 1) volume :=
  paretoMean_not_integrable_when_alpha_le_one (by norm_num) le_rfl (by norm_num)

example : ¬IntegrableOn (paretoMomentIntegrand 1 1 1) (Ioi 1) volume :=
  paretoMean_not_integrable_at_alpha_one (by norm_num)

#print axioms empiricalSurvival_variance
#print axioms empiricalSurvival_mse
#print axioms fairCoinMSE_not_littleO
#print axioms fairCoinRMSE_not_littleO

end TailOptionPricing
