module

/-
  Actual finite constant-error branching population from
  arXiv:1912.00277v2, Sections II–III. Each step mixes two actual
  populations with equal probability and perturbs their base scales.
  The paper's standard-deviation domain is sigma>0 and 0<=epsilon<1.
  The measure remains defined for other real parameters through variance
  sigma squared; the proved moment identities extend to those laws too.
-/
public import Stats.Probability.EqualMixture
public import Stats.Probability.GaussianShiftedMoments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual recursive Gaussian population of Sections II–III. At each
layer the scale is multiplied by 1+epsilon or 1-epsilon, equally likely. -/
noncomputable def epistemicBranchLaw : ℕ → ℝ → ℝ → ℝ → Measure ℝ
  | 0, μ, σ, _ => gaussianReal μ (NNReal.mk (σ ^ 2) (sq_nonneg σ))
  | n + 1, μ, σ, ε => equalMixture (epistemicBranchLaw n μ (σ * (1 + ε)) ε)
      (epistemicBranchLaw n μ (σ * (1 - ε)) ε)

/-- Every finite branching depth defines an actual probability population. -/
instance epistemicBranchLaw_probability (n : ℕ) (μ σ ε : ℝ) :
    IsProbabilityMeasure (epistemicBranchLaw n μ σ ε) := by
  induction n generalizing σ with
  | zero => unfold epistemicBranchLaw; infer_instance
  | succ n ih =>
    let := ih (σ * (1 + ε))
    let := ih (σ * (1 - ε))
    unfold epistemicBranchLaw
    infer_instance

/-- All natural powers about every finite center are L1 at every finite
depth, independently of the moment evaluations in Section III. -/
theorem epistemicBranchLaw_integrable_sub_pow (n : ℕ) (μ σ ε c : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (x - c) ^ k) (epistemicBranchLaw n μ σ ε) := by
  induction n generalizing σ with
  | zero => exact gaussianReal_integrable_sub_pow _ _ _ _
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_integrable_iff]
    exact ⟨ih _, ih _⟩

/-- Actual first-moment integrability of the branching observation. -/
theorem epistemicBranchLaw_integrable_id (n : ℕ) (μ σ ε : ℝ) :
    Integrable (fun x : ℝ => x) (epistemicBranchLaw n μ σ ε) := by
  simpa only [sub_zero, pow_one] using epistemicBranchLaw_integrable_sub_pow n μ σ ε 0 1

/-- Actual mean preservation at every finite depth (Section III),
proved from actual component L1 and equal-mixture integration. -/
theorem epistemicBranchLaw_mean (n : ℕ) (μ σ ε : ℝ) :
    (∫ x : ℝ, x ∂epistemicBranchLaw n μ σ ε) = μ := by
  induction n generalizing σ with
  | zero => exact integral_id_gaussianReal
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_integral (epistemicBranchLaw_integrable_id _ _ _ _)
      (epistemicBranchLaw_integrable_id _ _ _ _), ih, ih]
    ring

/-- Actual distributional symmetry about the common mean (Section III).
Reflection preserves the whole law, rather than just an odd-moment proxy. -/
theorem epistemicBranchLaw_reflection (n : ℕ) (μ σ ε : ℝ) :
    (epistemicBranchLaw n μ σ ε).map (fun x : ℝ => 2 * μ - x) =
      epistemicBranchLaw n μ σ ε := by
  have hm : Measurable (fun x : ℝ => 2 * μ - x) := measurable_id.const_sub (2 * μ)
  induction n generalizing σ with
  | zero =>
    rw [epistemicBranchLaw, gaussianReal_map_const_sub]
    congr 1
    ring
  | succ n ih =>
    rw [epistemicBranchLaw, equalMixture_map _ _ hm, ih, ih]

example : IsProbabilityMeasure (epistemicBranchLaw 2 1 2 (1 / 2)) := inferInstance

example : Integrable (fun x : ℝ => (x - 1) ^ 4) (epistemicBranchLaw 2 1 2 (1 / 2)) :=
  epistemicBranchLaw_integrable_sub_pow _ _ _ _ _ _

example : (∫ x : ℝ, x ∂epistemicBranchLaw 2 1 2 (1 / 2)) = 1 :=
  epistemicBranchLaw_mean _ _ _ _

example : (epistemicBranchLaw 2 1 2 (1 / 2)).map (fun x : ℝ => 2 - x) =
    epistemicBranchLaw 2 1 2 (1 / 2) := by
  simpa only [mul_one] using epistemicBranchLaw_reflection 2 1 2 (1 / 2)

#print axioms epistemicBranchLaw_probability
#print axioms epistemicBranchLaw_integrable_sub_pow
#print axioms epistemicBranchLaw_mean
#print axioms epistemicBranchLaw_reflection

end TailOptionPricing
