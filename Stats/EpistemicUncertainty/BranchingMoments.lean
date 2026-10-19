module

/-
  Actual finite branching outcome moments, arXiv:1912.00277v2, Section III.
  The normalized recursive law is evaluated by genuine mixture integration.
  The source's leading 3*mu^4 in the fourth raw moment is corrected to mu^4.
-/
public import Stats.EpistemicUncertainty.BranchingLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual second moment about any center in Section III's finite
constant-error population, rather than a weighted scale proxy. -/
theorem epistemicBranchLaw_momentAbout_two (n : ℕ) (μ σ ε c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 2 ∂epistemicBranchLaw n μ σ ε) =
      (μ - c) ^ 2 + σ ^ 2 * (1 + ε ^ 2) ^ n := by
  induction n generalizing σ with
  | zero =>
    rw [epistemicBranchLaw, gaussianReal_momentAbout_two, NNReal.coe_mk]
    simp only [pow_zero, mul_one]
    ring
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_integral
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 2)
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 2), ih, ih,
      pow_succ (1 + ε ^ 2) n]
    ring

/-- Actual third moment about an arbitrary center (Section III). -/
theorem epistemicBranchLaw_momentAbout_three (n : ℕ) (μ σ ε c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 3 ∂epistemicBranchLaw n μ σ ε) =
      (μ - c) ^ 3 + 3 * (μ - c) * σ ^ 2 * (1 + ε ^ 2) ^ n := by
  induction n generalizing σ with
  | zero =>
    rw [epistemicBranchLaw, gaussianReal_momentAbout_three, NNReal.coe_mk]
    simp only [pow_zero, mul_one]
    ring
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_integral
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 3)
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 3), ih, ih,
      pow_succ (1 + ε ^ 2) n]
    ring

/-- Correct actual fourth moment about a center (Section III).
The printed raw formula has 3*mu^4; its leading coefficient must be 1.
Here c=0 gives that repair and c=mu gives the actual central moment. -/
theorem epistemicBranchLaw_momentAbout_four (n : ℕ) (μ σ ε c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 4 ∂epistemicBranchLaw n μ σ ε) =
      (μ - c) ^ 4 + 6 * (μ - c) ^ 2 * σ ^ 2 * (1 + ε ^ 2) ^ n +
        3 * σ ^ 4 * (1 + 6 * ε ^ 2 + ε ^ 4) ^ n := by
  induction n generalizing σ with
  | zero =>
    rw [epistemicBranchLaw, gaussianReal_momentAbout_four, NNReal.coe_mk]
    simp only [pow_zero, mul_one]
    ring
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_integral
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 4)
      (epistemicBranchLaw_integrable_sub_pow n μ _ ε c 4), ih, ih,
      pow_succ (1 + ε ^ 2) n, pow_succ (1 + 6 * ε ^ 2 + ε ^ 4) n]
    ring

/-- Actual second raw outcome moment as printed in Section III. -/
theorem epistemicBranchLaw_moment_two (n : ℕ) (μ σ ε : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂epistemicBranchLaw n μ σ ε) = μ ^ 2 + σ ^ 2 * (1 + ε ^ 2) ^ n := by
  simpa only [sub_zero] using epistemicBranchLaw_momentAbout_two n μ σ ε 0

/-- Actual third raw outcome moment as printed in Section III. -/
theorem epistemicBranchLaw_moment_three (n : ℕ) (μ σ ε : ℝ) :
    (∫ x : ℝ, x ^ 3 ∂epistemicBranchLaw n μ σ ε) =
      μ ^ 3 + 3 * μ * σ ^ 2 * (1 + ε ^ 2) ^ n := by
  simpa only [sub_zero] using epistemicBranchLaw_momentAbout_three n μ σ ε 0

/-- Corrected actual fourth raw outcome moment in Section III:
replace the source's leading 3*mu^4 by mu^4, retaining all other terms. -/
theorem epistemicBranchLaw_moment_four (n : ℕ) (μ σ ε : ℝ) :
    (∫ x : ℝ, x ^ 4 ∂epistemicBranchLaw n μ σ ε) =
      μ ^ 4 + 6 * μ ^ 2 * σ ^ 2 * (1 + ε ^ 2) ^ n +
        3 * σ ^ 4 * (1 + 6 * ε ^ 2 + ε ^ 4) ^ n := by
  simpa only [sub_zero] using epistemicBranchLaw_momentAbout_four n μ σ ε 0

/-- Actual variance of the Section III population, using its actual mean. -/
theorem epistemicBranchLaw_variance (n : ℕ) (μ σ ε : ℝ) :
    variance (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) = σ ^ 2 * (1 + ε ^ 2) ^ n := by
  have hm : AEMeasurable (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) :=
    measurable_id.aemeasurable
  rw [variance_eq_integral hm, epistemicBranchLaw_mean, epistemicBranchLaw_momentAbout_two]
  simp

/-- The actual third central moment vanishes (Section III). -/
theorem epistemicBranchLaw_centralMoment_three (n : ℕ) (μ σ ε : ℝ) :
    centralMoment (fun x : ℝ => x) 3 (epistemicBranchLaw n μ σ ε) = 0 := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, epistemicBranchLaw_mean]
  rw [epistemicBranchLaw_momentAbout_three]
  simp

/-- The actual fourth central moment of the finite branching population. -/
theorem epistemicBranchLaw_centralMoment_four (n : ℕ) (μ σ ε : ℝ) :
    centralMoment (fun x : ℝ => x) 4 (epistemicBranchLaw n μ σ ε) =
      3 * σ ^ 4 * (1 + 6 * ε ^ 2 + ε ^ 4) ^ n := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, epistemicBranchLaw_mean]
  rw [epistemicBranchLaw_momentAbout_four]
  simp

/-- Proper one-layer counterexample to Section III's printed fourth
raw moment: mu=1, sigma=1, epsilon=1/2, with both branch scales positive. -/
theorem epistemicBranchLaw_fourth_source_counterexample :
    (∫ x : ℝ, x ^ 4 ∂epistemicBranchLaw 1 1 1 (1 / 2)) ≠
      3 * (1 : ℝ) ^ 4 + 6 * 1 ^ 2 * 1 ^ 2 * (1 + (1 / 2 : ℝ) ^ 2) ^ 1 +
        3 * 1 ^ 4 * (1 + 6 * (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 4) ^ 1 := by
  rw [epistemicBranchLaw_moment_four]
  norm_num

example : (∫ x : ℝ, x ^ 2 ∂epistemicBranchLaw 1 1 1 (1 / 2)) = 9 / 4 := by
  rw [epistemicBranchLaw_moment_two]
  norm_num

example : (∫ x : ℝ, x ^ 3 ∂epistemicBranchLaw 1 1 1 (1 / 2)) = 19 / 4 := by
  rw [epistemicBranchLaw_moment_three]
  norm_num

example : (∫ x : ℝ, x ^ 4 ∂epistemicBranchLaw 1 1 1 (1 / 2)) = 259 / 16 := by
  rw [epistemicBranchLaw_moment_four]
  norm_num

example : variance (fun x : ℝ => x) (epistemicBranchLaw 1 1 1 (1 / 2)) = 5 / 4 := by
  rw [epistemicBranchLaw_variance]
  norm_num

example : centralMoment (fun x : ℝ => x) 3 (epistemicBranchLaw 1 1 1 (1 / 2)) = 0 :=
  epistemicBranchLaw_centralMoment_three _ _ _ _

example : centralMoment (fun x : ℝ => x) 4 (epistemicBranchLaw 1 1 1 (1 / 2)) = 123 / 16 := by
  rw [epistemicBranchLaw_centralMoment_four]
  norm_num

#print axioms epistemicBranchLaw_moment_four
#print axioms epistemicBranchLaw_variance
#print axioms epistemicBranchLaw_fourth_source_counterexample

end TailOptionPricing
