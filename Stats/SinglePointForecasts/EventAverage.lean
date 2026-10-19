module

/-
  Moments of actual finite indicator averages, used for the survival
  estimator in arXiv:2007.16096v1, discussion at line 235. Independence
  enters only the variance; equal event probabilities enter the mean.
-/
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace TailOptionPricing

/-- The variance of an actual measurable event indicator is `p(1-p)`.
This supplies the probability bridge behind the scalar Bernoulli formula. -/
theorem indicator_one_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    variance (A.indicator (fun _ => (1 : ℝ))) μ = μ.real A * (1 - μ.real A) := by
  have hLp : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet
  rw [variance_eq_sub hLp]
  have hsq : (A.indicator (fun _ => (1 : ℝ))) ^ 2 = A.indicator (fun _ => 1) := by
    classical
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  have hint : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real A := by
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
  rw [hsq, hint]
  ring

/-- A finite average of actual event outcomes on a common sample space. -/
noncomputable def empiricalEventAverage {Ω : Type*} {n : ℕ}
    (A : Fin n → Set Ω) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (A i).indicator (fun _ => 1) ω

/-- Measurable events give a measurable empirical average. -/
theorem measurable_empiricalEventAverage {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {A : Fin n → Set Ω} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (empiricalEventAverage A) := by
  unfold empiricalEventAverage
  exact measurable_const.mul (Finset.measurable_sum Finset.univ
    (fun i _ => measurable_const.indicator (hA i)))

/-- The actual average is square integrable even if any underlying sample
values have infinite variance. No independence hypothesis is needed. -/
theorem empiricalEventAverage_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {n : ℕ} {A : Fin n → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) : MemLp (empiricalEventAverage A) 2 μ :=
  (memLp_finsetSum Finset.univ (fun i _ =>
    (memLp_const (1 : ℝ)).indicator (hA i).nullMeasurableSet)).const_mul _

/-- Pairwise independent event indicators with common success probability
have the exact sample-mean variance. Full mutual independence is unnecessary. -/
theorem empiricalEventAverage_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {A : Fin n → Set Ω} {p : ℝ}
    (hn : 0 < n) (hA : ∀ i, MeasurableSet (A i))
    (hind : Pairwise fun i j => IndepFun ((A i).indicator (fun _ => (1 : ℝ)))
      ((A j).indicator (fun _ => (1 : ℝ))) μ)
    (hp : ∀ i, μ.real (A i) = p) :
    variance (empiricalEventAverage A) μ = p * (1 - p) / n := by
  have hsum := IndepFun.variance_sum (s := Finset.univ)
    (X := fun i => (A i).indicator (fun _ => (1 : ℝ)))
    (fun i _ => (memLp_const (1 : ℝ)).indicator (hA i).nullMeasurableSet)
    (by intro i _ j _ hij; exact hind hij)
  simp only [indicator_one_variance (hA _), hp, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold empiricalEventAverage
  rw [variance_const_mul]
  have heq : (fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) =
      ∑ i, (A i).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [heq]
  rw [hsum]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- Equal event probabilities give an unbiased empirical average,
regardless of dependence between the observations. -/
theorem empiricalEventAverage_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {A : Fin n → Set Ω} {p : ℝ}
    (hn : 0 < n) (hA : ∀ i, MeasurableSet (A i))
    (hp : ∀ i, μ.real (A i) = p) : ∫ ω, empiricalEventAverage A ω ∂μ = p := by
  unfold empiricalEventAverage
  rw [integral_const_mul, integral_finsetSum Finset.univ
    (fun i _ => (integrable_const (1 : ℝ)).indicator (hA i))]
  simp only [integral_indicator (hA _), setIntegral_const, smul_eq_mul, mul_one, hp,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

end TailOptionPricing
