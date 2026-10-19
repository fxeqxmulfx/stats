module

/-
  Correct actual outcome-tail comparison, arXiv:1912.00277v2,
  Section VI. The source calls Gamma a lower bound for Lognormal
  precision and expects the Lognormal compound to generate more
  extreme outcomes. Right-tail order of precision does not transfer
  through inverse precision: the actual matched Gamma outcome has
  strictly heavier extreme tails than the Lognormal outcome.
  The source's centered model is used, with the exact matched prior
  parameters and arbitrary positive epistemic log variance.
-/
public import Stats.EpistemicUncertainty.GammaOutcomeTail
public import Stats.Probability.MomentTail

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Section VI's actual centered Normal--Lognormal outcome has both
tails negligible relative to every reciprocal real power. Its full
natural-moment L1 domain is proved from the independent Gaussian
generator and the actual lognormal precision inverse moments. -/
theorem epistemicNormalLognormalLaw_tail_rpow_tendsto_zero (m : ℝ) (v : NNReal) (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ p * (epistemicNormalLognormalLaw 0 m v).real (Ioi x))
      atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => x ^ p * (epistemicNormalLognormalLaw 0 m v).real (Iio (-x)))
      atTop (𝓝 0) := by
  have hi (k : ℕ) : Integrable (fun y : ℝ => y ^ k) (epistemicNormalLognormalLaw 0 m v) := by
    simpa only [sub_zero] using epistemicNormalLognormalLaw_integrable_sub_pow 0 m v k
  exact ⟨measureReal_right_tail_rpow_tendsto_zero hi p,
    measureReal_left_tail_rpow_tendsto_zero hi p⟩

/-- Actual Normal--Lognormal right-tail probability divided by its
exact moment-matched Gamma-compound counterpart tends to zero.
This reverses the proposed outcome lower-bound interpretation in
Section VI, for every positive epistemic variance. -/
theorem epistemicNormalLognormal_matchedGamma_rightTail_ratio_tendsto_zero
    {v : NNReal} (hv : 0 < (v : ℝ)) :
    Tendsto (fun x : ℝ => (epistemicNormalLognormalLaw 0 0 v).real (Ioi x) /
      (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x)) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x ^ epistemicGammaTailIndex v *
      (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x)) atTop
        (𝓝 (studentSurvivalTailConstant (epistemicGammaTailIndex v) (epistemicGammaMatchScale v))) := by
    rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure 0 hv]
    exact studentMeasure_survival_rpow_tendsto 0
      (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv)
  exact tendsto_ratio_zero_of_rpow_limits
    (epistemicNormalLognormalLaw_tail_rpow_tendsto_zero 0 v _).1 hg
    (studentSurvivalTailConstant_pos (epistemicGammaTailIndex_pos hv)
      (epistemicGammaMatchScale_pos hv)).ne'

/-- The same strict actual tail ratio holds on the left, at reflected
thresholds. The Gamma counterpart is the source's correctly scaled
Student law, whose actual tails have a positive power coefficient. -/
theorem epistemicNormalLognormal_matchedGamma_leftTail_ratio_tendsto_zero
    {v : NNReal} (hv : 0 < (v : ℝ)) :
    Tendsto (fun x : ℝ => (epistemicNormalLognormalLaw 0 0 v).real (Iio (-x)) /
      (epistemicMatchedGammaOutcomeLaw 0 v).real (Iio (-x))) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x ^ epistemicGammaTailIndex v *
      (epistemicMatchedGammaOutcomeLaw 0 v).real (Iio (-x))) atTop
        (𝓝 (studentSurvivalTailConstant (epistemicGammaTailIndex v) (epistemicGammaMatchScale v))) := by
    rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure 0 hv]
    have he (x : ℝ) :
        (studentMeasure 0 (epistemicGammaTailIndex v) (epistemicGammaMatchScale v)).real (Iio (-x)) =
          (studentMeasure 0 (epistemicGammaTailIndex v) (epistemicGammaMatchScale v)).real (Ioi x) := by
      simpa only [mul_zero, zero_sub] using studentMeasure_leftTail_eq_survival 0
        (epistemicGammaTailIndex v) (epistemicGammaMatchScale v) x
    simp_rw [he]
    exact studentMeasure_survival_rpow_tendsto 0
      (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv)
  exact tendsto_ratio_zero_of_rpow_limits
    (epistemicNormalLognormalLaw_tail_rpow_tendsto_zero 0 v _).2 hg
    (studentSurvivalTailConstant_pos (epistemicGammaTailIndex_pos hv)
      (epistemicGammaMatchScale_pos hv)).ne'

/-- Both actual extreme outcome tails are eventually strictly larger
under the moment-matched Gamma precision than under the lognormal
precision. This concerns probabilities, not isolated density values. -/
theorem eventually_epistemicNormalLognormal_tail_lt_matchedGamma
    {v : NNReal} (hv : 0 < (v : ℝ)) :
    ∀ᶠ x in atTop,
      (epistemicNormalLognormalLaw 0 0 v).real (Ioi x) <
        (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x) ∧
      (epistemicNormalLognormalLaw 0 0 v).real (Iio (-x)) <
        (epistemicMatchedGammaOutcomeLaw 0 v).real (Iio (-x)) := by
  have hr := (epistemicNormalLognormal_matchedGamma_rightTail_ratio_tendsto_zero hv).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hl := (epistemicNormalLognormal_matchedGamma_leftTail_ratio_tendsto_zero hv).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hr, hl] with x hx hy
  have hp : 0 < (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x) := by
    rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure 0 hv]
    exact studentMeasure_survival_pos 0
      (epistemicGammaTailIndex_pos hv) (epistemicGammaMatchScale_pos hv) x
  have he : (epistemicMatchedGammaOutcomeLaw 0 v).real (Iio (-x)) =
      (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x) := by
    rw [epistemicMatchedGammaOutcomeLaw_eq_studentMeasure 0 hv]
    simpa only [mul_zero, zero_sub] using studentMeasure_leftTail_eq_survival 0
      (epistemicGammaTailIndex v) (epistemicGammaMatchScale v) x
  exact ⟨(div_lt_one hp).mp hx, (div_lt_one (by rwa [he])).mp hy⟩

/-- Section VI's proposed Gamma lower bound cannot mean even eventual
right-tail domination by the Normal--Lognormal outcome. The opposite
strict inequality holds arbitrarily far into the actual tails. -/
theorem epistemicMatchedGamma_not_outcome_tail_lower_bound {v : NNReal} (hv : 0 < (v : ℝ)) :
    ¬(∀ᶠ x in atTop, (epistemicMatchedGammaOutcomeLaw 0 v).real (Ioi x) ≤
      (epistemicNormalLognormalLaw 0 0 v).real (Ioi x)) := by
  intro h
  obtain ⟨x, hx, hy⟩ := ((eventually_epistemicNormalLognormal_tail_lt_matchedGamma hv).and h).exists
  exact (not_le_of_gt hx.1) hy

/-- A proper pair at the source's exact variance-one moment match
refutes the outcome tail lower bound. Both populations are normalized. -/
theorem epistemicMatchedGamma_outcome_lower_bound_counterexample :
    IsProbabilityMeasure (epistemicNormalLognormalLaw 0 0 1) ∧
      IsProbabilityMeasure (epistemicMatchedGammaOutcomeLaw 0 1) ∧
        ¬(∀ᶠ x in atTop, (epistemicMatchedGammaOutcomeLaw 0 1).real (Ioi x) ≤
          (epistemicNormalLognormalLaw 0 0 1).real (Ioi x)) := by
  refine ⟨inferInstance, epistemicMatchedGammaOutcomeLaw_probability 0 (by norm_num), ?_⟩
  simpa only [NNReal.coe_one] using
    epistemicMatchedGamma_not_outcome_tail_lower_bound (v := 1) (by norm_num)

example : Tendsto (fun x : ℝ => (epistemicNormalLognormalLaw 0 0 1).real (Ioi x) /
    (epistemicMatchedGammaOutcomeLaw 0 1).real (Ioi x)) atTop (𝓝 0) := by
  simpa only [NNReal.coe_one] using
    epistemicNormalLognormal_matchedGamma_rightTail_ratio_tendsto_zero (v := 1) (by norm_num)

example : Tendsto (fun x : ℝ => (epistemicNormalLognormalLaw 0 0 1).real (Iio (-x)) /
    (epistemicMatchedGammaOutcomeLaw 0 1).real (Iio (-x))) atTop (𝓝 0) := by
  simpa only [NNReal.coe_one] using
    epistemicNormalLognormal_matchedGamma_leftTail_ratio_tendsto_zero (v := 1) (by norm_num)

example : ∀ᶠ x in atTop,
    (epistemicNormalLognormalLaw 0 0 1).real (Ioi x) < (epistemicMatchedGammaOutcomeLaw 0 1).real (Ioi x) ∧
    (epistemicNormalLognormalLaw 0 0 1).real (Iio (-x)) < (epistemicMatchedGammaOutcomeLaw 0 1).real (Iio (-x)) := by
  simpa only [NNReal.coe_one] using
    eventually_epistemicNormalLognormal_tail_lt_matchedGamma (v := 1) (by norm_num)

example : ¬(∀ᶠ x in atTop, (epistemicMatchedGammaOutcomeLaw 0 1).real (Ioi x) ≤
    (epistemicNormalLognormalLaw 0 0 1).real (Ioi x)) := by
  simpa only [NNReal.coe_one] using
    epistemicMatchedGamma_not_outcome_tail_lower_bound (v := 1) (by norm_num)

#print axioms epistemicNormalLognormalLaw_tail_rpow_tendsto_zero
#print axioms epistemicNormalLognormal_matchedGamma_rightTail_ratio_tendsto_zero
#print axioms epistemicNormalLognormal_matchedGamma_leftTail_ratio_tendsto_zero
#print axioms eventually_epistemicNormalLognormal_tail_lt_matchedGamma
#print axioms epistemicMatchedGamma_not_outcome_tail_lower_bound
#print axioms epistemicMatchedGamma_outcome_lower_bound_counterexample

end TailOptionPricing
