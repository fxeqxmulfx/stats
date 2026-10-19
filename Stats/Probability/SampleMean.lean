module

/-
  Actual arithmetic sample means and finite-mean unbiasedness, used to
  assess arXiv:2004.05894v1, Applications and Conclusion, line 278.
  The observed average differs from a truncated population integral.
-/
public import Stats.Probability.SampleMaximum
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The observed arithmetic mean. At empty size its total expression is zero;
unbiasedness below requires a nonempty sample. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / (n : ℝ)

theorem sampleMean_one (x : Fin 1 → ℝ) : sampleMean x = x 0 := by
  simp only [sampleMean, Fin.sum_univ_one, Nat.cast_one, div_one]

theorem measurable_sampleMean {n : ℕ} : Measurable (sampleMean : (Fin n → ℝ) → ℝ) := by
  change Measurable (fun x : Fin n → ℝ => (∑ i, x i) / (n : ℝ))
  exact (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)).div_const _

theorem sampleMean_integrable {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp : Integrable (fun s : ℝ => s) ν) :
    Integrable (sampleMean : (Fin n → ℝ) → ℝ) (iidSampleLaw n ν) := by
  change Integrable (fun x : Fin n → ℝ => (∑ i, x i) / (n : ℝ)) (iidSampleLaw n ν)
  exact (integrable_finsetSum Finset.univ
    (fun i _ => (iidSample_identDistrib n ν i).integrable_iff.mpr hp)).div_const _

/-- A nonempty actual iid sample mean is unbiased when the population
first moment is integrable; no variance or higher moments are required. -/
theorem sampleMean_unbiased {n : ℕ} [NeZero n] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp : Integrable (fun s : ℝ => s) ν) :
    (∫ x : Fin n → ℝ, sampleMean x ∂iidSampleLaw n ν) = ∫ s : ℝ, s ∂ν := by
  change (∫ x : Fin n → ℝ, (∑ i, x i) / (n : ℝ) ∂iidSampleLaw n ν) = _
  rw [integral_div, integral_finsetSum Finset.univ
    (fun i _ => (iidSample_identDistrib n ν i).integrable_iff.mpr hp)]
  have he (i : Fin n) : (∫ x : Fin n → ℝ, x i ∂iidSampleLaw n ν) = ∫ s : ℝ, s ∂ν :=
    (iidSample_identDistrib n ν i).integral_eq
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem iidSample_ae_nonneg (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp : ∀ᵐ s ∂ν, 0 ≤ s) :
    ∀ᵐ x ∂iidSampleLaw n ν, ∀ i : Fin n, 0 ≤ x i := by
  apply ae_all_iff.mpr
  intro i
  exact (iidSample_identDistrib n ν i).symm.ae_snd measurableSet_Ici hp

end TailOptionPricing
