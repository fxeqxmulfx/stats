module

/-
  The arithmetic sample mean can exceed its true mean under a right-tailed
  Pareto law, for every positive finite sample size. This refutes the
  necessary-underestimation assertion in arXiv:2004.05894v1, conclusion,
  line 278. The valid population-truncation claim is in Decomposition.lean.
-/
public import Stats.Probability.SampleMean
public import Stats.Pareto.Moments
public import Stats.HiddenMoments.Maximum

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual finite iid Pareto sample mean is unbiased throughout the
finite-mean domain, including infinite-variance laws. -/
theorem paretoSampleMean_unbiased {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) :
    (∫ x : Fin n → ℝ, sampleMean x ∂iidSampleLaw n (paretoMeasure l α)) = α * l / (α - 1) := by
  have hα0 : 0 < α := by linarith
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα0
  rw [sampleMean_unbiased _ ((paretoMeasure_integrable_id_iff hl hα0).mpr hα),
    paretoMeasure_mean hl hα]

theorem paretoMeasure_ae_gt {l α : ℝ} (hl : 0 < l) (hα : 0 < α) :
    ∀ᵐ s ∂paretoMeasure l α, l < s := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα
  apply ae_iff.mpr
  rw [← measureReal_eq_zero_iff]
  simp only [not_lt]
  change (paretoMeasure l α).real (Iic l) = 0
  rw [paretoMeasure_real_Iic hl hα, ite_eq_right (lt_irrefl l), div_self hl.ne', Real.one_rpow]
  norm_num

/-- A single sufficiently large observation gives a positive lower bound
on the actual probability of a sample-mean overshoot, for every nonempty
finite sample. This supplies the counterexample to the necessary
underestimation claim in arXiv:2004.05894v1, conclusion, line 278. -/
theorem paretoSampleMean_upper_tail_lower {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) :
    (l / ((n : ℝ) * (α * l / (α - 1)))) ^ α ≤
      (iidSampleLaw n (paretoMeasure l α)).real {x | α * l / (α - 1) < sampleMean x} := by
  have hα0 : 0 < α := by linarith
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl hα0
  let m : ℝ := α * l / (α - 1)
  let k : ℝ := (n : ℝ) * m
  let i : Fin n := ⟨0, NeZero.pos n⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hm0 : 0 < m := div_pos (mul_pos hα0 hl) (sub_pos.mpr hα)
  have hlm : l ≤ m := by
    dsimp [m]
    rw [le_div_iff₀ (sub_pos.mpr hα)]
    nlinarith
  have hlk : l ≤ k := by dsimp [k]; nlinarith
  have hpop : ∀ᵐ s ∂paretoMeasure l α, 0 ≤ s := by
    filter_upwards [paretoMeasure_ae_gt hl hα0] with s hs using hl.le.trans hs.le
  have hnonneg := iidSample_ae_nonneg n (paretoMeasure l α) hpop
  have hmono : (iidSampleLaw n (paretoMeasure l α)) {x | k < x i} ≤
      (iidSampleLaw n (paretoMeasure l α)) {x | m < sampleMean x} := by
    apply measure_mono_ae
    filter_upwards [hnonneg] with x hx
    intro he
    have hsum := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
    change m < (∑ j, x j) / (n : ℝ)
    apply (lt_div_iff₀ hn0).mpr
    dsimp [k] at he
    nlinarith
  have hreal : (iidSampleLaw n (paretoMeasure l α)).real {x | k < x i} ≤
      (iidSampleLaw n (paretoMeasure l α)).real {x | m < sampleMean x} :=
    ENNReal.toReal_mono (by finiteness) hmono
  have he : (iidSampleLaw n (paretoMeasure l α)).real {x | k < x i} =
      (paretoMeasure l α).real (Ioi k) := by
    have h := (iidSample_identDistrib n (paretoMeasure l α) i).measure_mem_eq
      (s := Ioi k) measurableSet_Ioi
    exact congrArg ENNReal.toReal h
  rw [he, paretoMeasure_real_Ioi_eq_survival hl hα0 hlk] at hreal
  exact hreal

theorem paretoSampleMean_can_exceed_mean {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) :
    0 < (iidSampleLaw n (paretoMeasure l α)).real
      {x | (∫ s : ℝ, s ∂paretoMeasure l α) < sampleMean x} := by
  rw [paretoMeasure_mean hl hα]
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hden : 0 < (n : ℝ) * (α * l / (α - 1)) :=
    mul_pos hn (div_pos (mul_pos (by linarith : 0 < α) hl) (sub_pos.mpr hα))
  exact (Real.rpow_pos_of_pos (div_pos hl hden) α).trans_le
    (paretoSampleMean_upper_tail_lower hl hα)

/-- Formal refutation of the literal necessary-underestimation claim
for the arithmetic sample mean (arXiv:2004.05894v1, conclusion, line 278). -/
theorem paretoSampleMean_not_always_below_mean {n : ℕ} [NeZero n] {l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) :
    ¬ ∀ᵐ x ∂iidSampleLaw n (paretoMeasure l α),
      sampleMean x ≤ ∫ s : ℝ, s ∂paretoMeasure l α := by
  let : IsProbabilityMeasure (paretoMeasure l α) :=
    instIsProbabilityMeasureParetoMeasure l α hl (by linarith)
  intro he
  have hz : (iidSampleLaw n (paretoMeasure l α)).real
      {x | (∫ s : ℝ, s ∂paretoMeasure l α) < sampleMean x} = 0 := by
    rw [measureReal_eq_zero_iff]
    simpa only [not_le] using ae_iff.mp he
  exact (paretoSampleMean_can_exceed_mean (n := n) hl hα).ne' hz

end TailOptionPricing
