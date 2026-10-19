module

/-
  Actual variance, skewness and kurtosis for arXiv:1912.00277v2,
  Section III's finite recursive constant-error Gaussian population.
  The earlier scale-sum expressions are identified with actual central
  moments before transferring their closed forms and inequalities.
-/
public import Stats.EpistemicUncertainty.BranchingMoments
public import Stats.EpistemicUncertainty

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The earlier Section III scale-sum expression is the actual
outcome variance of the normalized recursive branching population. -/
theorem epistemicBranchLaw_variance_eq_scaleMoment (n : ℕ) (μ σ ε : ℝ) :
    variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) = epistemicSigmaMoment n 2 σ ε := by
  rw [epistemicBranchLaw_variance, epistemicVariance_eq]

/-- Three times the scale fourth moment is the actual fourth central
outcome moment; the corrected raw formula has already been proved. -/
theorem epistemicBranchLaw_centralMoment_four_eq_scaleMoment (n : ℕ) (μ σ ε : ℝ) :
    centralMoment (fun x : ℝ => x) 4 (epistemicBranchLaw n μ σ ε) =
      3 * epistemicSigmaMoment n 4 σ ε := by
  rw [epistemicBranchLaw_centralMoment_four, epistemicSigmaFourthMoment_eq]
  ring

/-- Nonzero base scale gives a genuinely positive actual variance at
each finite depth, so Section III's standardized ratios are well defined. -/
theorem epistemicBranchLaw_variance_pos (n : ℕ) (μ ε : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    0 < variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) := by
  rw [epistemicBranchLaw_variance]
  have hp : 0 < 1 + ε ^ 2 := by nlinarith [sq_nonneg ε]
  exact mul_pos (sq_pos_of_ne_zero hσ) (pow_pos hp n)

/-- Actual standardized third central moment is zero (Section III).
The positive-variance theorem above supplies its nondegenerate domain. -/
theorem epistemicBranchLaw_skewness_zero (n : ℕ) (μ σ ε : ℝ) :
    centralMoment (fun x : ℝ => x) 3 (epistemicBranchLaw n μ σ ε) /
      variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) ^ ((3 : ℝ) / 2) = 0 := by
  rw [epistemicBranchLaw_centralMoment_three, zero_div]

/-- Pearson kurtosis defined from actual central moments and actual
variance, as required to interpret Section III's closed formula. -/
noncomputable def epistemicBranchLawKurtosis (n : ℕ) (μ σ ε : ℝ) : ℝ :=
  centralMoment (fun x : ℝ => x) 4 (epistemicBranchLaw n μ σ ε) /
    variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) ^ 2

/-- The earlier algebraic candidate is now identified with actual
Pearson kurtosis for the recursively constructed population. -/
theorem epistemicBranchLawKurtosis_eq (n : ℕ) (μ σ ε : ℝ) :
    epistemicBranchLawKurtosis n μ σ ε = epistemicKurtosis n σ ε := by
  rw [epistemicBranchLawKurtosis, epistemicBranchLaw_centralMoment_four_eq_scaleMoment,
    epistemicBranchLaw_variance_eq_scaleMoment, epistemicKurtosis]

/-- Actual Pearson kurtosis's Section III closed form, with nonzero
base scale ensuring the genuine variance is positive. -/
theorem epistemicBranchLawKurtosis_closed (n : ℕ) (μ σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicBranchLawKurtosis n μ σ ε =
      3 * (1 + 6 * ε ^ 2 + ε ^ 4) ^ n / (1 + ε ^ 2) ^ (2 * n) := by
  rw [epistemicBranchLawKurtosis_eq]
  exact epistemicKurtosis_eq n σ ε hσ

/-- The source uses excess kurtosis: its actual value is Pearson
kurtosis minus three, identified here with the Section III expression. -/
theorem epistemicBranchLaw_excessKurtosis (n : ℕ) (μ σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicBranchLawKurtosis n μ σ ε - 3 =
      3 * ((1 + 6 * ε ^ 2 + ε ^ 4) ^ n / (1 + ε ^ 2) ^ (2 * n) - 1) := by
  rw [epistemicBranchLawKurtosis_eq]
  exact epistemicExcessKurtosis_eq n σ ε hσ

/-- Actual Pearson kurtosis is at least three (Section III). -/
theorem epistemicBranchLawKurtosis_ge_three (n : ℕ) (μ σ ε : ℝ) (hσ : σ ≠ 0) :
    3 ≤ epistemicBranchLawKurtosis n μ σ ε := by
  rw [epistemicBranchLawKurtosis_eq]
  exact epistemicKurtosis_ge_three n σ ε hσ

/-- Genuine higher kurtosis for positive depth and nonzero uncertainty
(Section III). This asserts no power-law tail or infinite-depth law. -/
theorem epistemicBranchLawKurtosis_gt_three {n : ℕ} {σ ε : ℝ} (μ : ℝ)
    (hn : 1 ≤ n) (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    3 < epistemicBranchLawKurtosis n μ σ ε := by
  rw [epistemicBranchLawKurtosis_eq]
  exact epistemicKurtosis_gt_three hn hσ hε

example : 0 < variance (fun x : ℝ => x) (epistemicBranchLaw 1 1 1 (1 / 2)) :=
  epistemicBranchLaw_variance_pos _ _ _ (by norm_num)

example : epistemicBranchLawKurtosis 1 1 1 (1 / 2) = 123 / 25 := by
  rw [epistemicBranchLawKurtosis_closed _ _ _ _ (by norm_num)]
  norm_num

example : epistemicBranchLawKurtosis 1 1 1 (1 / 2) - 3 = 48 / 25 := by
  rw [epistemicBranchLaw_excessKurtosis _ _ _ _ (by norm_num)]
  norm_num

example : 3 ≤ epistemicBranchLawKurtosis 1 1 1 (1 / 2) :=
  epistemicBranchLawKurtosis_ge_three _ _ _ _ (by norm_num)

example : 3 < epistemicBranchLawKurtosis 1 1 1 (1 / 2) :=
  epistemicBranchLawKurtosis_gt_three _ (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemicBranchLaw_variance_eq_scaleMoment
#print axioms epistemicBranchLawKurtosis_eq
#print axioms epistemicBranchLawKurtosis_gt_three

end TailOptionPricing
