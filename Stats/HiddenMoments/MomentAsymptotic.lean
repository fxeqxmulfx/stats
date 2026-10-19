module

/-
  The printed general-p hidden-moment expectation is an asymptotic for
  the actual strong-Pareto sample, not its exact finite-sample expectation.
  Source: arXiv:2004.05894v1, section 1, display following Proposition 1.
-/
public import Stats.HiddenMoments.MomentMean
public import Stats.Probability.BetaAsymptotic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual finite-sample hidden-moment expectations converge after
power scaling. This proves the leading term printed after Proposition 1
in arXiv:2004.05894v1, section 1, without replacing the finite maximum by a Frechet law. -/
theorem paretoHiddenMoment_mean_scaled_tendsto {l a p : ℝ} (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ ((a - p) / a) *
      ∫ x : Fin (n + 1) → ℝ, sampleHiddenMoment (paretoMeasure l a) p x
        ∂iidSampleLaw (n + 1) (paretoMeasure l a)) atTop
      (𝓝 (l ^ p * Real.Gamma ((a - p) / a))) := by
  have hr : 0 < (a - p) / a := div_pos (sub_pos.mpr hp) ha
  have hlim := ((Real.GammaSeq_tendsto_Gamma ((a - p) / a)).comp
    (tendsto_add_atTop_nat 1)).const_mul (l ^ p)
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [realGammaSeq_eq_beta hr, paretoHiddenMoment_mean_gamma hl ha hp]
  unfold ProbabilityTheory.beta
  rw [show (a - p) / a + (((n + 1 : ℕ) : ℝ) + 1) =
    ((n + 1 : ℕ) : ℝ) + 1 + (a - p) / a by ring]
  ring

/-- The ratio of the genuine expected hidden moment to the source
expression tends to one. Here `(a-p)/a = 1-p/a`, so the denominator is
the expression following Proposition 1 of arXiv:2004.05894v1.
Indexing samples by `n+1` ensures a nonempty sample at every index. -/
theorem paretoHiddenMoment_mean_ratio_tendsto {l a p : ℝ} (hl : 0 < l) (ha : 0 < a) (hp : p < a) :
    Tendsto (fun n : ℕ =>
      (∫ x : Fin (n + 1) → ℝ, sampleHiddenMoment (paretoMeasure l a) p x
        ∂iidSampleLaw (n + 1) (paretoMeasure l a)) /
      (l ^ p * ((n + 1 : ℕ) : ℝ) ^ (-((a - p) / a)) *
        Real.Gamma ((a - p) / a))) atTop (𝓝 1) := by
  have hr : 0 < (a - p) / a := div_pos (sub_pos.mpr hp) ha
  have hc : l ^ p * Real.Gamma ((a - p) / a) ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos hl _) (Real.Gamma_pos_of_pos hr)).ne'
  have hlim := (paretoHiddenMoment_mean_scaled_tendsto hl ha hp).div_const (l ^ p * Real.Gamma ((a - p) / a))
  rw [div_self hc] at hlim
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [Real.rpow_neg (Nat.cast_nonneg (n + 1))]
  have hn : ((n + 1 : ℕ) : ℝ) ^ ((a - p) / a) ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) _).ne'
  field_simp

end TailOptionPricing
