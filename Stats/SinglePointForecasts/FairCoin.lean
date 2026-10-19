module

/-
  A nondegenerate iid counterexample to the survival-estimation error
  o(1/n) claim in arXiv:2007.16096v1, discussion at line 235. The error
  is specified explicitly as actual mean-square or root-mean-square
  error under a finite product of Bernoulli probability laws.
-/
public import Stats.SinglePointForecasts.EmpiricalSurvival
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

namespace TailOptionPricing

/-- A genuine Bernoulli law with equal masses at zero and one. -/
noncomputable def fairCoinLaw : Measure ℝ :=
  bernoulliMeasure 1 0 ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure fairCoinLaw := by unfold fairCoinLaw; infer_instance

/-- The actual joint law of `n` independent fair Bernoulli observations. -/
noncomputable def fairCoinSampleLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => fairCoinLaw)

instance (n : ℕ) : IsProbabilityMeasure (fairCoinSampleLaw n) := by
  unfold fairCoinSampleLaw
  infer_instance

/-- Product-space observations are mutually independent. -/
theorem fairCoinSample_indep (n : ℕ) :
    iIndepFun (fun i (ω : Fin n → ℝ) => ω i) (fairCoinSampleLaw n) :=
  iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
    (fun _ => measurable_id.aemeasurable)

/-- Every observation has the same nondegenerate marginal law. -/
theorem fairCoinSample_map (n : ℕ) (i : Fin n) :
    (fairCoinSampleLaw n).map (fun ω => ω i) = fairCoinLaw :=
  (measurePreserving_eval (fun _ : Fin n => fairCoinLaw) i).map_eq

/-- At threshold one half the true survival probability is one half. -/
theorem fairCoinLaw_survival : fairCoinLaw.real (Ioi (1 / 2)) = 1 / 2 :=
  bernoulliMeasure_real_apply_of_mem_of_notMem _ measurableSet_Ioi
    (by norm_num) (by norm_num)

/-- The genuine estimator has variance exactly `1/(4n)`, not merely an
upper bound on a scalar expression (arXiv:2007.16096v1, line 235). -/
theorem fairCoin_empiricalSurvival_variance (n : ℕ) (hn : 0 < n) :
    variance (empiricalSurvival (fun i (ω : Fin n → ℝ) => ω i) (1 / 2))
      (fairCoinSampleLaw n) = 1 / (4 * n) := by
  have h := empiricalSurvival_variance (ν := fairCoinLaw) (1 / 2) hn
    (fun i => measurable_pi_apply i)
    (fun _ _ hij => (fairCoinSample_indep n).indepFun hij) (fairCoinSample_map n)
  rw [fairCoinLaw_survival] at h
  rw [h]
  ring

/-- Actual mean-square estimation error, integrated under the iid product
law. It is defined by observed squared errors, not by a desired rate. -/
noncomputable def fairCoinMSE (n : ℕ) : ℝ :=
  ∫ ω : Fin n → ℝ,
    (empiricalSurvival (fun i ω => ω i) (1 / 2) ω - 1 / 2)^2 ∂fairCoinSampleLaw n

/-- Exact MSE of the genuine fair-coin estimator. -/
theorem fairCoinMSE_eq (n : ℕ) (hn : 0 < n) : fairCoinMSE n = 1 / (4 * n) := by
  have h := empiricalSurvival_mse (ν := fairCoinLaw) (1 / 2) hn
    (fun i => measurable_pi_apply i)
    (fun _ _ hij => (fairCoinSample_indep n).indepFun hij) (fairCoinSample_map n)
  rw [fairCoinLaw_survival] at h
  change fairCoinMSE n = _ at h
  rw [h]
  ring

/-- Counterexample to the printed `o(1/n)` rate under mean-square error:
the ratio to `1/n` is the nonzero constant one quarter. Shifting the index
by one keeps every sample nonempty and does not change the asymptotic rate. -/
theorem fairCoinMSE_not_littleO :
    ¬ (fun n : ℕ => fairCoinMSE (n + 1)) =o[Filter.atTop]
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  have ht := h.tendsto_div_nhds_zero
  have heq : (fun n : ℕ => fairCoinMSE (n + 1) / (1 / ((n + 1 : ℕ) : ℝ))) =
      (fun _ : ℕ => (1 / 4 : ℝ)) := by
    funext n
    rw [fairCoinMSE_eq (n + 1) (Nat.succ_pos n)]
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq] at ht
  have he := tendsto_nhds_unique ht (tendsto_const_nhds (x := (1 / 4 : ℝ)))
  norm_num at he

/-- The same printed claim also fails for actual root-mean-square error. -/
theorem fairCoinRMSE_not_littleO :
    ¬ (fun n : ℕ => Real.sqrt (fairCoinMSE (n + 1))) =o[Filter.atTop]
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro h
  apply fairCoinMSE_not_littleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  filter_upwards [h.bound hc] with n hn
  have hnonneg : 0 ≤ fairCoinMSE (n + 1) := by
    rw [fairCoinMSE_eq (n + 1) (Nat.succ_pos n)]
    positivity
  have hle : fairCoinMSE (n + 1) ≤ 1 := by
    rw [fairCoinMSE_eq (n + 1) (Nat.succ_pos n)]
    apply (div_le_one (by positivity : (0 : ℝ) < 4 * ((n + 1 : ℕ) : ℝ))).mpr
    norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm : ‖fairCoinMSE (n + 1)‖ ≤ ‖Real.sqrt (fairCoinMSE (n + 1))‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.le_sqrt_self_iff.mpr hle
  exact hnorm.trans hn

end TailOptionPricing
