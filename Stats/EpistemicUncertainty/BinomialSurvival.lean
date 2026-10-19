module

/-
  Actual constant-error exceedance probabilities, arXiv:1912.00277v2,
  Section III. The printed erfc formula omits centering by the common
  mean: K must be K-mu unless mu=0. Both the corrected formula and
  the printed zero-mean specialization are proved for actual laws.
-/
public import Stats.EpistemicUncertainty.BinomialDensity
public import Stats.BlackScholes.Erfc

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

/-- Actual positive-scale Gaussian exceedance, as used for every
component of Section III's mixture. The threshold is centered by mu. -/
theorem gaussianReal_real_Ici_affine_scale (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (K : ℝ) :
    (gaussianReal μ (NNReal.mk (σ ^ 2) (sq_nonneg σ))).real (Ici K) =
      1 - stdNormalCdf ((K - μ) / σ) := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← gaussianReal_map_affine_scale μ σ]
  unfold Measure.real
  rw [Measure.map_apply ((measurable_const_mul σ).const_add μ) measurableSet_Ici]
  have hp : (fun x : ℝ => μ + σ * x) ⁻¹' Ici K = Ici ((K - μ) / σ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, div_le_iff₀ hσ]
    constructor <;> intro h <;> nlinarith
  rw [hp, ← measure_congr (Ioi_ae_eq_Ici : Ioi ((K - μ) / σ) =ᵐ[gaussianReal 0 1]
    Ici ((K - μ) / σ))]
  exact (one_sub_stdNormalCdf _).symm

/-- Section III's actual exceedance probability is the binomial sum
of centered Gaussian tails. Finite measure weights are transported
through the proved whole-law Gaussian mixture identity. -/
theorem epistemicBranchLaw_real_Ici_binomial (n : ℕ) (μ K : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (epistemicBranchLaw n μ σ ε).real (Ici K) =
      ∑ j ∈ range (n + 1), ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) *
        (1 - stdNormalCdf ((K - μ) / (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)))) := by
  rw [epistemicBranchLaw_eq_binomial_mixture]
  unfold Measure.real
  rw [Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (by
    intro j hj
    change ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) *
      gaussianReal μ (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2)
        (sq_nonneg _)) (Ici K) ≠ ⊤
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply sum_congr rfl
  intro j hj
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  change ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) *
    (gaussianReal μ (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2)
      (sq_nonneg _))).real (Ici K) = _
  rw [gaussianReal_real_Ici_affine_scale μ (epistemicBinomialScale_pos n j hσ hε₀ hε₁) K]

/-- Corrected actual erfc exceedance formula of Section III. The source
prints K in the numerator; for its general common mean mu this must
be K-mu. The project's erfc has its proved source integral definition
in `erfc_eq_one_sub_integral`, beyond the CDF notation alone. -/
theorem epistemicBranchLaw_real_Ici_erfc (n : ℕ) (μ K : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (epistemicBranchLaw n μ σ ε).real (Ici K) =
      ∑ j ∈ range (n + 1), ((1 / 2 : ℝ) ^ (n + 1) * (n.choose j : ℝ)) *
        erfc ((K - μ) / (Real.sqrt 2 * (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)))) := by
  rw [epistemicBranchLaw_real_Ici_binomial n μ K hσ hε₀ hε₁]
  apply sum_congr rfl
  intro j hj
  rw [one_sub_stdNormalCdf_eq_half_erfc, div_div,
    mul_comm (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) (Real.sqrt 2), pow_succ]
  ring

/-- The formula literally printed in Section III is valid when the
calculation sets the common mean to zero. The density has no atoms,
so this is the actual non-strict exceedance probability in the source. -/
theorem epistemicBranchLaw_real_Ici_erfc_zero_mean (n : ℕ) (K : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (epistemicBranchLaw n 0 σ ε).real (Ici K) =
      ∑ j ∈ range (n + 1), ((1 / 2 : ℝ) ^ (n + 1) * (n.choose j : ℝ)) *
        erfc (K / (Real.sqrt 2 * (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)))) := by
  simpa only [sub_zero] using epistemicBranchLaw_real_Ici_erfc n 0 K hσ hε₀ hε₁

/-- Every finite positive-scale population exceeds its common mean
with probability one-half (Section III). The binomial weights are
normalized by an actual constant expectation of the dispersion law. -/
theorem epistemicBranchLaw_real_Ici_mean (n : ℕ) (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (epistemicBranchLaw n μ σ ε).real (Ici μ) = 1 / 2 := by
  have hw := epistemicScaleLaw_integral_binomial n σ ε (fun _ : ℝ => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hw
  rw [epistemicBranchLaw_real_Ici_binomial n μ μ hσ hε₀ hε₁]
  simp only [sub_self, zero_div, stdNormalCdf_zero]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← hw]
  norm_num

/-- Counterexample to Section III's uncentered exceedance formula for
general mu: the actual N(1,1) population exceeds its mean with
probability one-half, strictly above the printed uncentered tail. -/
theorem epistemic_uncentered_exceedance_counterexample :
    (epistemicBranchLaw 0 1 1 0).real (Ici 1) ≠ (1 / 2 : ℝ) * erfc (1 / Real.sqrt 2) := by
  have ha := epistemicBranchLaw_real_Ici_binomial 0 1 1 (σ := 1) (ε := 0)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, stdNormalCdf_zero] at ha
  rw [ha, ← one_sub_stdNormalCdf_eq_half_erfc]
  have h := stdNormalCdf_strictMono (by norm_num : (0 : ℝ) < 1)
  rw [stdNormalCdf_zero] at h
  linarith

example : (gaussianReal 1 (NNReal.mk ((2 : ℝ) ^ 2) (sq_nonneg _))).real (Ici 3) =
    1 - stdNormalCdf 1 := by
  simpa only [show ((3 - 1) / 2 : ℝ) = 1 by norm_num] using
    gaussianReal_real_Ici_affine_scale 1 (σ := 2) (by norm_num) 3

example : (epistemicBranchLaw 2 1 2 (1 / 2)).real (Ici 1) = 1 / 2 := by
  exact epistemicBranchLaw_real_Ici_mean _ _ (by norm_num) (by norm_num) (by norm_num)

example : (epistemicBranchLaw 2 1 2 (1 / 2)).real (Ici 3) =
    ∑ j ∈ range 3, ((1 / 2 : ℝ) ^ 2 * (Nat.choose 2 j : ℝ)) *
      (1 - stdNormalCdf ((3 - 1) /
        (2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)))) :=
  epistemicBranchLaw_real_Ici_binomial _ _ _ (by norm_num) (by norm_num) (by norm_num)

example : (epistemicBranchLaw 2 1 2 (1 / 2)).real (Ici 3) =
    ∑ j ∈ range 3, ((1 / 2 : ℝ) ^ 3 * (Nat.choose 2 j : ℝ)) *
      erfc ((3 - 1) / (Real.sqrt 2 *
        (2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)))) :=
  epistemicBranchLaw_real_Ici_erfc _ _ _ (by norm_num) (by norm_num) (by norm_num)

example : (epistemicBranchLaw 2 0 2 (1 / 2)).real (Ici 3) =
    ∑ j ∈ range 3, ((1 / 2 : ℝ) ^ 3 * (Nat.choose 2 j : ℝ)) *
      erfc (3 / (Real.sqrt 2 *
        (2 * (1 + (1 / 2 : ℝ)) ^ j * (1 - (1 / 2 : ℝ)) ^ (2 - j)))) :=
  epistemicBranchLaw_real_Ici_erfc_zero_mean _ _ (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemicBranchLaw_real_Ici_erfc
#print axioms epistemic_uncentered_exceedance_counterexample

end TailOptionPricing
