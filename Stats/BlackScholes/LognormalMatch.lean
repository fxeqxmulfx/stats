module

/-
  Genuine matching models for arXiv:1908.02347v3, Arbitrage Boundaries.
  The positive-variance hypotheses in the density-based comparison are
  satisfied by a risk-neutral Gaussian law and an actual Pareto call.
-/
public import Stats.BlackScholes.Erfc
public import Stats.BlackScholes.StrictButterfly

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

/-- Matching and the local mixed butterfly hold simultaneously for actual
lognormal and Pareto call integrals, without assuming either condition. -/
theorem exists_lognormal_pareto_match :
    ∃ l α : ℝ, 1 < α ∧ 0 < l ∧ l < 1 ∧
      callPriceBS 1 (-(1 / 2)) 1 1 = callPrice l α 1 ∧
      (∀ᶠ d in 𝓝[>] (0 : ℝ),
        callPrice l α (1 + d) + callPriceBS 1 (-(1 / 2)) 1 (1 - d) ≥
          2 * callPrice l α 1) := by
  let C : ℝ := callPriceBS 1 (-(1 / 2)) 1 1
  let D : ℝ := survivalLN 1 (-(1 / 2)) 1 1
  have hC : 0 < C := callPriceBS_pos (by norm_num) (by norm_num) (by norm_num)
  have hD : 0 < D := survivalLN_pos (by norm_num) (by norm_num) 1
  have hD1 : D ≤ 1 := survivalLN_le_one 1
  let q : ℝ := D / 2
  have hq : 0 < q := div_pos hD (by norm_num)
  have hq1 : q < 1 := by dsimp [q]; linarith
  let α : ℝ := 1 + q / C
  have hα : 1 < α := by dsimp [α]; linarith [div_pos hq hC]
  have hαpos : 0 < α := by linarith
  let l : ℝ := q ^ (1 / α)
  have hl : 0 < l := Real.rpow_pos_of_pos hq _
  have hl1 : l < 1 := Real.rpow_lt_one hq.le hq1 (one_div_pos.mpr hαpos)
  have hlpow : l ^ α = q := by
    dsimp [l]
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hαpos.ne', Real.rpow_one]
  have hm : callPriceBS 1 (-(1 / 2)) 1 1 = callPrice l α 1 := by
    rw [callPrice_eq hα hl hl1.le, Real.one_rpow, mul_one, hlpow]
    change C = q / (α - 1)
    dsimp [α]
    field_simp [hC.ne', hq.ne']
    ring
  have hf : HasDerivAt (callPrice l α) (-q) 1 := by
    simpa only [div_one, hlpow] using callPrice_hasDerivAt hα hl hl1
  have hg : HasDerivAt (callPriceBS 1 (-(1 / 2)) 1) (-D) 1 :=
    callPriceBS_hasDerivAt (by norm_num) (by norm_num) (by norm_num)
  have hlt : -D < -q := by dsimp [q]; linarith
  exact ⟨l, α, hα, hl, hl1, hm,
    matched_butterfly_of_deriv_lt hf hg hm.symm hlt⟩

example : ∃ l α : ℝ, 1 < α ∧ 0 < l ∧ l < 1 ∧
    (l / 1) ^ α ≤ survivalLN 1 (-(1 / 2)) 1 1 := by
  obtain ⟨l, α, hα, hl, hl1, hm, hb⟩ := exists_lognormal_pareto_match
  exact ⟨l, α, hα, hl, hl1,
    BSC_lognormal_tail_dominates_at_match (a := 1 / 2)
      hα hl hl1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm hb⟩

example : ∃ l α : ℝ, 1 < α ∧ 0 < l ∧ l < 1 ∧
    Real.log ((1 / 2) * erfc ((1 / 2) / Real.sqrt 2)) / Real.log l ≤ α := by
  obtain ⟨l, α, hα, hl, hl1, hm, hb⟩ := exists_lognormal_pareto_match
  have h := alpha_lower_bound_erfc (a := 1 / 2)
    hα hl hl1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hm hb
  refine ⟨l, α, hα, hl, hl1, ?_⟩
  norm_num at h
  exact h

end TailOptionPricing
