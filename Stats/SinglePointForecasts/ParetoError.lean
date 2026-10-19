module

/-
  The printed o(1/n) survival-error claim (arXiv:2007.16096v1, line 235)
  also fails within the source's nonnegative regularly varying setting.
  The actual unit-Pareto law is constructed from an exponential rate;
  independent samples at threshold two give MSE exactly 1/(4n).
-/
public import Stats.SinglePointForecasts.ExponentialLaw
public import Stats.SinglePointForecasts.FairCoin
public import Stats.Theorem1

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- An actual scale-one, index-one Pareto law, obtained from `exp(R)`
with an exponentially distributed rate `R` of parameter one. -/
noncomputable def unitParetoLaw : Measure ℝ := exponentialGrowthLaw 1 1 1

instance : IsProbabilityMeasure unitParetoLaw :=
  exponentialGrowthLaw_probability 1 1 (by norm_num)

/-- The actual Pareto tail above its support boundary. -/
theorem unitParetoLaw_survival {s : ℝ} (hs : 1 ≤ s) :
    unitParetoLaw.real (Ioi s) = 1 / s := by
  have h := exponentialGrowthLaw_survival_of_ge (t := 1) (lam := 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num) hs
  simpa [unitParetoLaw] using h

/-- This example satisfies the paper's actual regular-variation
definition, not merely a description of its tail as fat. -/
theorem unitParetoLaw_regularlyVarying :
    IsRegularlyVarying (fun s => unitParetoLaw.real (Ioi s)) (-1) := by
  intro x hx
  have h := survival_isRegularlyVarying (l := 1) (α := 1) (by norm_num) x hx
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop (max 1 (1 / x))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htx : 1 ≤ t * x := (div_le_iff₀ hx).mp ((le_max_right _ _).trans ht)
  rw [unitParetoLaw_survival ht1, unitParetoLaw_survival htx]
  simp [survival]

/-- The actual joint law of independent heavy-tailed observations. -/
noncomputable def unitParetoSampleLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => unitParetoLaw)

instance (n : ℕ) : IsProbabilityMeasure (unitParetoSampleLaw n) := by
  unfold unitParetoSampleLaw
  infer_instance

/-- Independence is proved from the product law. -/
theorem unitParetoSample_indep (n : ℕ) :
    iIndepFun (fun i (ω : Fin n → ℝ) => ω i) (unitParetoSampleLaw n) :=
  iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
    (fun _ => measurable_id.aemeasurable)

/-- Each coordinate has the actual unit-Pareto marginal. -/
theorem unitParetoSample_map (n : ℕ) (i : Fin n) :
    (unitParetoSampleLaw n).map (fun ω => ω i) = unitParetoLaw :=
  (measurePreserving_eval (fun _ : Fin n => unitParetoLaw) i).map_eq

/-- Actual mean-square error of estimating the Pareto survival at two. -/
noncomputable def unitParetoMSE (n : ℕ) : ℝ :=
  ∫ ω : Fin n → ℝ,
    (empiricalSurvival (fun i ω => ω i) 2 ω - 1 / 2)^2 ∂unitParetoSampleLaw n

/-- The same exact nonzero rate holds in the source's heavy-tailed model. -/
theorem unitParetoMSE_eq (n : ℕ) (hn : 0 < n) : unitParetoMSE n = 1 / (4 * n) := by
  have h := empiricalSurvival_mse (ν := unitParetoLaw) 2 hn
    (fun i => measurable_pi_apply i)
    (fun _ _ hij => (unitParetoSample_indep n).indepFun hij) (unitParetoSample_map n)
  rw [unitParetoLaw_survival (by norm_num : (1 : ℝ) ≤ 2)] at h
  change unitParetoMSE n = _ at h
  rw [h]
  ring

/-- The printed rate is false for MSE even for an actual nonnegative
regularly varying Pareto sample. -/
theorem unitParetoMSE_not_littleO :
    ¬ (fun n : ℕ => unitParetoMSE (n + 1)) =o[atTop]
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  apply fairCoinMSE_not_littleO
  convert h using 1
  funext n
  rw [unitParetoMSE_eq (n + 1) (Nat.succ_pos n),
    fairCoinMSE_eq (n + 1) (Nat.succ_pos n)]

/-- The printed rate is also false for RMSE in the same heavy-tailed model. -/
theorem unitParetoRMSE_not_littleO :
    ¬ (fun n : ℕ => Real.sqrt (unitParetoMSE (n + 1))) =o[atTop]
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  apply fairCoinRMSE_not_littleO
  convert h using 1
  funext n
  rw [unitParetoMSE_eq (n + 1) (Nat.succ_pos n),
    fairCoinMSE_eq (n + 1) (Nat.succ_pos n)]

example : unitParetoLaw.real (Ioi 2) = 1 / 2 := unitParetoLaw_survival (by norm_num)

example : unitParetoMSE 2 = 1 / 8 := by
  have h := unitParetoMSE_eq 2 (by norm_num)
  norm_num at h
  exact h

#print axioms unitParetoLaw_regularlyVarying
#print axioms unitParetoMSE_not_littleO
#print axioms unitParetoRMSE_not_littleO

end TailOptionPricing
