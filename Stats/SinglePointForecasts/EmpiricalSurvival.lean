module

/-
  The actual finite-sample empirical survival for arXiv:2007.16096v1,
  discussion at line 235. Measurable independent samples with a common
  marginal law give an unbiased estimator and MSE p(1-p)/n, even when
  the sample values themselves have no finite moments.
-/
public import Stats.SinglePointForecasts.EventAverage
public import Stats.SinglePointForecasts.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace TailOptionPricing

/-- The observed proportion of sample values strictly exceeding `x`.
The strict-tail convention works for both continuous laws and atoms. -/
noncomputable def empiricalSurvival {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  empiricalEventAverage (fun i => X i ⁻¹' Ioi x)

/-- Squared estimation error is genuinely integrable without requiring
any moments of the underlying observations (arXiv:2007.16096v1, line 235). -/
theorem integrable_empiricalSurvival_sq_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (x p : ℝ) (hX : ∀ i, Measurable (X i)) :
    Integrable (fun ω => (empiricalSurvival X x ω - p)^2) μ :=
  ((empiricalEventAverage_memLp (fun i => measurableSet_Ioi.preimage (hX i))).sub
    (memLp_const p)).integrable_sq

/-- Unbiasedness at a fixed threshold for samples with a common marginal
law. Independence is not needed for this expectation identity. -/
theorem empiricalSurvival_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
    {n : ℕ} {X : Fin n → Ω → ℝ} (x : ℝ) (hn : 0 < n)
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν) :
    (∫ ω, empiricalSurvival X x ω ∂μ) = ν.real (Ioi x) := by
  apply empiricalEventAverage_integral hn (fun i => measurableSet_Ioi.preimage (hX i))
  intro i
  rw [← hlaw i]
  exact congrArg ENNReal.toReal (Measure.map_apply (hX i) measurableSet_Ioi).symm

/-- Exact actual-estimator variance, using pairwise independence and a
common law rather than taking the Bernoulli variance formula as input. -/
theorem empiricalSurvival_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
    {n : ℕ} {X : Fin n → Ω → ℝ} (x : ℝ) (hn : 0 < n)
    (hX : ∀ i, Measurable (X i))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, μ.map (X i) = ν) :
    variance (empiricalSurvival X x) μ = ν.real (Ioi x) * (1 - ν.real (Ioi x)) / n := by
  apply empiricalEventAverage_variance hn
    (fun i => measurableSet_Ioi.preimage (hX i))
  · intro i j hij
    have hm : Measurable ((Ioi x).indicator (fun _ : ℝ => (1 : ℝ))) :=
      measurable_const.indicator measurableSet_Ioi
    have hcomp := (hind hij).comp hm hm
    have heq (i : Fin n) : (Ioi x).indicator (fun _ : ℝ => (1 : ℝ)) ∘ X i =
        (X i ⁻¹' Ioi x).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      exact (Set.indicator_comp_right (X i)).symm
    rwa [heq i, heq j] at hcomp
  · intro i
    rw [← hlaw i]
    exact congrArg ENNReal.toReal (Measure.map_apply (hX i) measurableSet_Ioi).symm

/-- Correct fixed-threshold MSE in the setting of the source's line 235.
It is `p(1-p)/n`; no moment assumption is imposed on the sampled variable. -/
theorem empiricalSurvival_mse {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
    {n : ℕ} {X : Fin n → Ω → ℝ} (x : ℝ) (hn : 0 < n)
    (hX : ∀ i, Measurable (X i))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, μ.map (X i) = ν) :
    (∫ ω, (empiricalSurvival X x ω - ν.real (Ioi x))^2 ∂μ) =
      ν.real (Ioi x) * (1 - ν.real (Ioi x)) / n := by
  have hm : Measurable (empiricalSurvival X x) := by
    exact measurable_empiricalEventAverage (fun i => measurableSet_Ioi.preimage (hX i))
  have hv := empiricalSurvival_variance x hn hX hind hlaw
  rw [variance_eq_integral hm.aemeasurable, empiricalSurvival_integral x hn hX hlaw] at hv
  exact hv

/-- The actual independent-sample variance is at most `1/(4n)` at any
fixed threshold (corrected rate for arXiv:2007.16096v1, line 235). -/
theorem empiricalSurvival_variance_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
    {n : ℕ} {X : Fin n → Ω → ℝ} (x : ℝ) (hn : 0 < n)
    (hX : ∀ i, Measurable (X i))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, μ.map (X i) = ν) :
    variance (empiricalSurvival X x) μ ≤ 1 / (4 * n) := by
  rw [empiricalSurvival_variance x hn hX hind hlaw]
  exact empirical_survival_variance_bound hn

/-- The actual RMSE is at most `1/(2 sqrt n)` at a fixed threshold.
This is a corrected upper bound, not the source's printed `o(1/n)`. -/
theorem empiricalSurvival_rmse_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
    {n : ℕ} {X : Fin n → Ω → ℝ} (x : ℝ) (hn : 0 < n)
    (hX : ∀ i, Measurable (X i))
    (hind : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, μ.map (X i) = ν) :
    Real.sqrt (∫ ω, (empiricalSurvival X x ω - ν.real (Ioi x))^2 ∂μ) ≤
      1 / (2 * Real.sqrt n) := by
  rw [empiricalSurvival_mse x hn hX hind hlaw]
  exact empirical_survival_std_bound hn

end TailOptionPricing
