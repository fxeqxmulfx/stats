module

/-
  Actual moments with varying errors, arXiv:1912.00277v2, Sections II–IV.
  Section IV's variance and fourth-central-moment products are derived
  by actual finite-mixture integration, including geometric decay.
  Zero-based error i is source epsilon_(i+1)=epsilon_1*kappa^i;
  the source's prose epsilon_n=kappa^n*epsilon_1 needs exponent n-1.
-/
public import Stats.EpistemicUncertainty.LayerLaw

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

/-- Actual dispersion moments under different fair error layers
(Sections II and IV). Every test power is independently L1. -/
theorem epistemicLayerScaleLaw_moment (n k : ℕ) (σ : ℝ) (ε : ℕ → ℝ) :
    (∫ s : ℝ, s ^ k ∂epistemicLayerScaleLaw n σ ε) =
      σ ^ k * ∏ i ∈ range n, epistemicMomentFactor k (ε i) := by
  induction n generalizing σ with
  | zero => simp [epistemicLayerScaleLaw]
  | succ n ih =>
    rw [epistemicLayerScaleLaw, equalMixture_integral
      (epistemicLayerScaleLaw_integrable n _ ε (fun s : ℝ => s ^ k))
      (epistemicLayerScaleLaw_integrable n _ ε (fun s : ℝ => s ^ k)), ih, ih,
      prod_range_succ]
    unfold epistemicMomentFactor
    simp only [mul_pow]
    ring

/-- Actual mean dispersion remains the base scale even with different
finite errors, as required by Section II's unbiased dispersion model. -/
theorem epistemicLayerScaleLaw_mean (n : ℕ) (σ : ℝ) (ε : ℕ → ℝ) :
    (∫ s : ℝ, s ∂epistemicLayerScaleLaw n σ ε) = σ := by
  have hf (e : ℝ) : epistemicMomentFactor 1 e = 1 := by unfold epistemicMomentFactor; ring
  simpa only [pow_one, hf, prod_const_one, mul_one] using epistemicLayerScaleLaw_moment n 1 σ ε

/-- Genuine second moment about an arbitrary center, Sections II–IV.
At the actual common mean it gives the source variance product. -/
theorem epistemicLayerBranchLaw_momentAbout_two (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) (c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 2 ∂epistemicLayerBranchLaw n μ σ ε) =
      (μ - c) ^ 2 + σ ^ 2 * ∏ i ∈ range n, (1 + (ε i) ^ 2) := by
  induction n generalizing σ with
  | zero =>
    rw [epistemicLayerBranchLaw, gaussianReal_momentAbout_two, NNReal.coe_mk]
    simp only [prod_range_zero, mul_one]
    ring
  | succ n ih =>
    rw [epistemicLayerBranchLaw, equalMixture_integral
      (epistemicLayerBranchLaw_integrable_sub_pow n μ _ ε c 2)
      (epistemicLayerBranchLaw_integrable_sub_pow n μ _ ε c 2), ih, ih, prod_range_succ]
    ring

/-- Genuine fourth moment about an arbitrary center, Sections II–IV.
The raw noncentered coefficient is one, as in the corrected Section III
statement; at the common mean this is the source's Section IV product. -/
theorem epistemicLayerBranchLaw_momentAbout_four (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) (c : ℝ) :
    (∫ x : ℝ, (x - c) ^ 4 ∂epistemicLayerBranchLaw n μ σ ε) =
      (μ - c) ^ 4 + 6 * (μ - c) ^ 2 * σ ^ 2 *
        (∏ i ∈ range n, (1 + (ε i) ^ 2)) +
      3 * σ ^ 4 * ∏ i ∈ range n, (1 + 6 * (ε i) ^ 2 + (ε i) ^ 4) := by
  induction n generalizing σ with
  | zero =>
    rw [epistemicLayerBranchLaw, gaussianReal_momentAbout_four, NNReal.coe_mk]
    simp only [prod_range_zero, mul_one]
    ring
  | succ n ih =>
    rw [epistemicLayerBranchLaw, equalMixture_integral
      (epistemicLayerBranchLaw_integrable_sub_pow n μ _ ε c 4)
      (epistemicLayerBranchLaw_integrable_sub_pow n μ _ ε c 4), ih, ih,
      prod_range_succ, prod_range_succ]
    ring

/-- Actual varying-error variance derived from the actual population's
mean and second central moment, Sections II and IV (Eq. var2). -/
theorem epistemicLayerBranchLaw_variance (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) :
    variance (fun x : ℝ => x) (epistemicLayerBranchLaw n μ σ ε) =
      σ ^ 2 * ∏ i ∈ range n, (1 + (ε i) ^ 2) := by
  have hm : AEMeasurable (fun x : ℝ => x) (epistemicLayerBranchLaw n μ σ ε) :=
    measurable_id.aemeasurable
  rw [variance_eq_integral hm, epistemicLayerBranchLaw_mean,
    epistemicLayerBranchLaw_momentAbout_two]
  simp

/-- Nonzero base scale gives positive actual variance at every finite
varying-error depth, including the source's positive-scale domain. -/
theorem epistemicLayerBranchLaw_variance_pos (n : ℕ) (μ : ℝ) {σ : ℝ} (ε : ℕ → ℝ)
    (hσ : σ ≠ 0) :
    0 < variance (fun x : ℝ => x) (epistemicLayerBranchLaw n μ σ ε) := by
  rw [epistemicLayerBranchLaw_variance]
  exact mul_pos (sq_pos_of_ne_zero hσ) (prod_pos (fun _ _ => by positivity))

/-- Actual fourth central outcome moment is the product printed in
Section IV, derived from genuine mixture integration and the true mean. -/
theorem epistemicLayerBranchLaw_centralMoment_four (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) :
    centralMoment (fun x : ℝ => x) 4 (epistemicLayerBranchLaw n μ σ ε) =
      3 * σ ^ 4 * ∏ i ∈ range n, (1 + 6 * (ε i) ^ 2 + (ε i) ^ 4) := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, epistemicLayerBranchLaw_mean]
  rw [epistemicLayerBranchLaw_momentAbout_four]
  simp

/-- The earlier Section IV Eq. var2 expression is now identified with
an actual geometrically decaying-error population variance. Index zero
is source epsilon_1, so layer i has error epsilon_1*kappa^i. -/
theorem epistemicLayerBranchLaw_variance_decaying (n : ℕ) (μ σ ε₁ κ : ℝ) :
    variance (fun x : ℝ => x)
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i)) =
      decayingErrorVariance n σ ε₁ κ := by
  rw [epistemicLayerBranchLaw_variance, decayingErrorVariance]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [mul_pow, ← pow_mul, Nat.mul_comm i 2]

/-- Section IV's actual decaying-error variance is at least the base
Gaussian variance; this transfers the proved finite-product inequality. -/
theorem epistemicLayerBranchLaw_variance_decaying_ge_base (n : ℕ) (μ σ ε₁ κ : ℝ) :
    σ ^ 2 ≤ variance (fun x : ℝ => x)
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i)) := by
  rw [epistemicLayerBranchLaw_variance_decaying]
  exact decayingErrorVariance_ge_base n σ ε₁ κ (sq_nonneg σ)

/-- The actual Section IV population variance increases with the
number of error layers, by the proved actual product identification. -/
theorem epistemicLayerBranchLaw_variance_decaying_monotone (μ σ ε₁ κ : ℝ) :
    Monotone (fun n => variance (fun x : ℝ => x)
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i))) := by
  intro n m hnm
  dsimp only
  rw [epistemicLayerBranchLaw_variance_decaying, epistemicLayerBranchLaw_variance_decaying]
  exact decayingErrorVariance_mono σ ε₁ κ hnm (sq_nonneg σ)

/-- Actual fourth central moment of the geometrically decaying-error
Gaussian population, as printed after Eq. var2 in Section IV. -/
theorem epistemicLayerBranchLaw_centralMoment_four_decaying (n : ℕ) (μ σ ε₁ κ : ℝ) :
    centralMoment (fun x : ℝ => x) 4
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i)) =
      3 * σ ^ 4 * ∏ i ∈ range n,
        (1 + 6 * ε₁ ^ 2 * κ ^ (2 * i) + ε₁ ^ 4 * κ ^ (4 * i)) := by
  rw [epistemicLayerBranchLaw_centralMoment_four]
  congr 1
  apply prod_congr rfl
  intro i hi
  have h₂ : (ε₁ * κ ^ i) ^ 2 = ε₁ ^ 2 * κ ^ (2 * i) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm i 2]
  have h₄ : (ε₁ * κ ^ i) ^ 4 = ε₁ ^ 4 * κ ^ (4 * i) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm i 4]
  rw [h₂, h₄]
  ring

/-- Section IV writes [-epsilon^2;kappa^2]_n but defines [a;q]_n
with a plus sign. Taken together these give the wrong variance.
The actual one-layer variance is 5/4, while that printed convention
gives 3/4. The usual minus-sign Pochhammer convention fixes the notation. -/
theorem epistemic_decaying_pochhammer_sign_counterexample :
    variance (fun x : ℝ => x) (epistemicLayerBranchLaw 1 0 1
      (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) ≠
      (1 : ℝ) ^ 2 * ∏ i ∈ range 1,
        (1 + (-((1 / 2 : ℝ) ^ 2)) * (1 / 2) ^ (2 * i)) := by
  rw [epistemicLayerBranchLaw_variance_decaying, decayingErrorVariance]
  norm_num [Finset.prod_range_succ]

example : (∫ s : ℝ, s ∂epistemicLayerScaleLaw 2 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) = 2 := epistemicLayerScaleLaw_mean _ _ _

example : 0 < variance (fun x : ℝ => x) (epistemicLayerBranchLaw 2 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) :=
  epistemicLayerBranchLaw_variance_pos _ _ _ (by norm_num)

example : variance (fun x : ℝ => x) (epistemicLayerBranchLaw 2 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) = 85 / 16 := by
  rw [epistemicLayerBranchLaw_variance_decaying, decayingErrorVariance]
  norm_num [Finset.prod_range_succ]

example : centralMoment (fun x : ℝ => x) 4 (epistemicLayerBranchLaw 2 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) = 43419 / 256 := by
  rw [epistemicLayerBranchLaw_centralMoment_four_decaying]
  norm_num [Finset.prod_range_succ]

#print axioms epistemicLayerScaleLaw_moment
#print axioms epistemicLayerBranchLaw_variance_decaying
#print axioms epistemicLayerBranchLaw_centralMoment_four_decaying
#print axioms epistemic_decaying_pochhammer_sign_counterexample

end TailOptionPricing
