module

/-
  Geometric divergence of actual finite-population moments in
  arXiv:1912.00277v2, Section III. Nonzero uncertainty and base scale
  are essential. These limits concern the sequence of finite laws;
  they neither construct an infinite-depth law nor identify a tail class.
-/
public import Stats.EpistemicUncertainty.BranchingKurtosis
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter

namespace TailOptionPricing

/-- Actual Pearson kurtosis is a geometric sequence (Section III).
The nonzero base scale gives a genuinely positive actual variance. -/
theorem epistemicBranchLawKurtosis_geometric (n : ℕ) (μ σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicBranchLawKurtosis n μ σ ε =
      3 * ((1 + 6 * ε ^ 2 + ε ^ 4) / (1 + ε ^ 2) ^ 2) ^ n := by
  rw [epistemicBranchLawKurtosis_closed _ _ _ _ hσ, div_pow, ← pow_mul]
  ring

/-- Actual variance diverges with depth for nonzero uncertainty and
nonzero base scale, as asserted in arXiv:1912.00277v2, Section III. -/
theorem epistemicBranchLaw_variance_tendsto_atTop (μ : ℝ) {σ ε : ℝ}
    (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    Tendsto (fun n => variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε)) atTop atTop := by
  have hr : 1 < 1 + ε ^ 2 := by nlinarith [sq_pos_of_ne_zero hε]
  simpa only [epistemicBranchLaw_variance] using
    Filter.Tendsto.const_mul_atTop (sq_pos_of_ne_zero hσ)
      (tendsto_pow_atTop_atTop_of_one_lt hr)

/-- The genuine fourth central moments also diverge (Section III).
Each finite population still has an independently proved finite L1 moment. -/
theorem epistemicBranchLaw_centralMoment_four_tendsto_atTop (μ : ℝ) {σ ε : ℝ}
    (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    Tendsto (fun n => centralMoment (fun x : ℝ => x) 4 (epistemicBranchLaw n μ σ ε))
      atTop atTop := by
  have hr : 1 < 1 + 6 * ε ^ 2 + ε ^ 4 := by
    nlinarith [sq_pos_of_ne_zero hε, sq_nonneg (ε ^ 2)]
  have hc : 0 < 3 * σ ^ 4 := by positivity
  simpa only [epistemicBranchLaw_centralMoment_four] using
    Filter.Tendsto.const_mul_atTop hc (tendsto_pow_atTop_atTop_of_one_lt hr)

/-- Actual Pearson kurtosis diverges geometrically with depth (Section
III). The ratio B/A² exceeds one exactly on the nonzero-error domain used here. -/
theorem epistemicBranchLawKurtosis_tendsto_atTop (μ : ℝ) {σ ε : ℝ}
    (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    Tendsto (fun n => epistemicBranchLawKurtosis n μ σ ε) atTop atTop := by
  have hd : 0 < (1 + ε ^ 2) ^ 2 := by positivity
  have hr : 1 < (1 + 6 * ε ^ 2 + ε ^ 4) / (1 + ε ^ 2) ^ 2 := by
    rw [lt_div_iff₀ hd, one_mul]
    exact epistemicMomentFactor_four_strict hε
  have he : (fun n => epistemicBranchLawKurtosis n μ σ ε) =
      fun n => 3 * ((1 + 6 * ε ^ 2 + ε ^ 4) / (1 + ε ^ 2) ^ 2) ^ n :=
    funext (fun n => epistemicBranchLawKurtosis_geometric n μ σ ε hσ)
  rw [he]
  exact Filter.Tendsto.const_mul_atTop (by norm_num) (tendsto_pow_atTop_atTop_of_one_lt hr)

/-- The source uses excess kurtosis; subtracting three from the actual
Pearson kurtosis preserves its divergence (Section III). -/
theorem epistemicBranchLaw_excessKurtosis_tendsto_atTop (μ : ℝ) {σ ε : ℝ}
    (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    Tendsto (fun n => epistemicBranchLawKurtosis n μ σ ε - 3) atTop atTop := by
  simpa only [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right atTop (-3 : ℝ)
      (epistemicBranchLawKurtosis_tendsto_atTop μ hσ hε)

/-- Zero uncertainty gives constant actual variance, so the source's
explosion requires an explicit nonzero-error hypothesis (Section III). -/
theorem epistemicBranchLaw_variance_zero_error (n : ℕ) (μ σ : ℝ) :
    variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ 0) = σ ^ 2 := by
  rw [epistemicBranchLaw_variance]
  simp

/-- At zero uncertainty, nondegenerate populations have actual Pearson
kurtosis three at every finite depth, rather than divergent kurtosis. -/
theorem epistemicBranchLawKurtosis_zero_error (n : ℕ) (μ σ : ℝ) (hσ : σ ≠ 0) :
    epistemicBranchLawKurtosis n μ σ 0 = 3 := by
  rw [epistemicBranchLawKurtosis_closed _ _ _ _ hσ]
  simp

example : Tendsto (fun n => variance (fun x : ℝ => x) (epistemicBranchLaw n 1 1 (1 / 2)))
    atTop atTop := epistemicBranchLaw_variance_tendsto_atTop _ (by norm_num) (by norm_num)

example : Tendsto (fun n => centralMoment (fun x : ℝ => x) 4
    (epistemicBranchLaw n 1 1 (1 / 2))) atTop atTop :=
  epistemicBranchLaw_centralMoment_four_tendsto_atTop _ (by norm_num) (by norm_num)

example : epistemicBranchLawKurtosis 2 1 1 (1 / 2) = 3 * (41 / 25 : ℝ) ^ 2 := by
  rw [epistemicBranchLawKurtosis_geometric _ _ _ _ (by norm_num)]
  norm_num

example : Tendsto (fun n => epistemicBranchLawKurtosis n 1 1 (1 / 2)) atTop atTop :=
  epistemicBranchLawKurtosis_tendsto_atTop _ (by norm_num) (by norm_num)

example : Tendsto (fun n => epistemicBranchLawKurtosis n 1 1 (1 / 2) - 3) atTop atTop :=
  epistemicBranchLaw_excessKurtosis_tendsto_atTop _ (by norm_num) (by norm_num)

example : epistemicBranchLawKurtosis 10 1 1 0 = 3 :=
  epistemicBranchLawKurtosis_zero_error _ _ _ (by norm_num)

#print axioms epistemicBranchLaw_variance_tendsto_atTop
#print axioms epistemicBranchLawKurtosis_tendsto_atTop
#print axioms epistemicBranchLaw_excessKurtosis_tendsto_atTop

end TailOptionPricing
