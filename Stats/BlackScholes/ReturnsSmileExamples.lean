module

/-
  Satisfiability certificates for the corrected final bound in
  arXiv:1908.02347v3, "Arbitrage Boundaries". We construct a genuine
  matching Pareto call and a nonconstant smile. The annual volatility is
  `(3 - K) / 2` near K = 2 and time to expiry is 4, so both the strike
  derivative and the square-root time factor are exercised.
-/
public import Stats.BlackScholes.ReturnsSmile
public import Stats.BlackScholes.StrictButterfly

@[expose] public section

open Real Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TailOptionPricing

private noncomputable def sampleBSCall : ℝ := callPriceBS_σ 1 1 2
private noncomputable def sampleBSDigital : ℝ := stdNormalCdf (Real.log (1 / 2) - 1 / 2)

private theorem sampleBSCall_pos : 0 < sampleBSCall := by
  have hlink := callPriceBS_σ_eq_callPriceBS_riskNeutral
    (S₀ := 1) (K := 2) (v := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hlink
  rw [sampleBSCall, hlink, callPriceBS]
  have hp : ∀ x : ℝ, 0 < survivalLN 1 (-(1 / 2)) 1 x := by
    intro x
    have heq := survivalLN_riskNeutral_eq_stdNormalCdf
      (S₀ := 1) (K := x) (v := 1) (by norm_num)
    norm_num at heq
    rw [heq]
    exact stdNormalCdf_pos _
  have hsupp : Function.support (survivalLN 1 (-(1 / 2)) 1) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp x).ne'
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (hp x).le))
    (integrableOn_survivalLN (by norm_num) (by norm_num))).mpr
  norm_num at hsupp
  rw [hsupp, Set.univ_inter, Real.volume_Ioi]
  simp

/-- A nonempty set of parameters satisfies all the matching and butterfly
hypotheses of the paper's final bound. No no-arbitrage inequality is
assumed in this construction. The strict derivative conclusion refutes
the printed `BSC' ≥ C'` direction immediately after `arbitrage` in
arXiv:1908.02347v3 while preserving the stated butterfly hypothesis. -/
theorem exists_returns_smile_parameters :
    ∃ l α : ℝ, 1 < α ∧ 0 < l ∧ 1 * (1 + l) < 2 ∧
      callPriceBS_σ 1 1 2 = callPriceReturns l α 1 2 ∧
      (∀ᶠ d in 𝓝[>] (0 : ℝ),
        callPriceReturns l α 1 (2 + d) + callPriceBS_σ 1 (3 - (2 - d)) (2 - d) ≥
        2 * callPriceReturns l α 1 2) ∧
      deriv (fun x => callPriceBS_σ 1 (3 - x) x) 2 < deriv (callPriceReturns l α 1) 2 := by
  let q : ℝ := sampleBSDigital / 2
  have hD : 0 < sampleBSDigital := stdNormalCdf_pos _
  have hD1 : sampleBSDigital < 1 := stdNormalCdf_lt_one _
  have hq : 0 < q := div_pos hD (by norm_num)
  have hq1 : q < 1 := by dsimp [q]; linarith
  let α : ℝ := 1 + q / sampleBSCall
  have hα : 1 < α := by dsimp [α]; linarith [div_pos hq sampleBSCall_pos]
  have hαpos : 0 < α := by linarith
  let l : ℝ := q ^ (1 / α)
  have hl : 0 < l := Real.rpow_pos_of_pos hq _
  have hl1 : l < 1 := Real.rpow_lt_one hq.le hq1 (one_div_pos.mpr hαpos)
  have hlpow : l ^ α = q := by
    dsimp [l]
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hαpos.ne', Real.rpow_one]
  have hK : 1 * (1 + l) < (2 : ℝ) := by linarith
  have hmatch : callPriceBS_σ 1 1 2 = callPriceReturns l α 1 2 := by
    rw [callPriceReturns_eq hα hl (by norm_num) hK.le]
    simp only [mul_one, show (2 - 1 : ℝ) = 1 from by norm_num, Real.one_rpow, hlpow]
    change sampleBSCall = q / (α - 1)
    dsimp [α]
    field_simp [sampleBSCall_pos.ne', hq.ne']
    ring
  have hf : HasDerivAt (callPriceReturns l α 1) (-q) 2 := by
    simpa only [mul_one, show (2 - 1 : ℝ) = 1 from by norm_num, div_one, hlpow]
      using callPriceReturns_hasDerivAt hα hl (by norm_num) hK
  have hg := callPriceBS_σ_smile_hasDerivAt (S₀ := 1) (K₀ := 2)
    (σ := fun x => 3 - x) (σ' := -1)
    (by norm_num) (by norm_num) (by norm_num) ((hasDerivAt_id 2).const_sub 3)
  have hg' : HasDerivAt (fun x => callPriceBS_σ 1 (3 - x) x)
      (-sampleBSDigital - gaussianPDFReal 0 1 (Real.log (1 / 2) + 1 / 2)) 2 := by
    norm_num [sampleBSDigital] at hg ⊢
    simpa only [sub_eq_add_neg] using hg
  have hlt : -sampleBSDigital - gaussianPDFReal 0 1 (Real.log (1 / 2) + 1 / 2) < -q := by
    have hp := gaussianPDFReal_nonneg 0 1 (Real.log (1 / 2) + 1 / 2)
    dsimp [q]
    linarith
  exact ⟨l, α, hα, hl, hK, hmatch,
    matched_butterfly_of_deriv_lt hf hg'
      (by simpa only [show (3 - 2 : ℝ) = 1 from by norm_num] using hmatch.symm) hlt,
    by rw [hg'.deriv, hf.deriv]; exact hlt⟩

example : ∃ l α : ℝ, 1 < α ∧ 0 < l ∧ 1 * (1 + l) < 2 ∧
    (l * 1 / (2 - 1)) ^ α ≤ bsSmileDigital 1 4 (fun x => (3 - x) / 2) (-1 / 2) 2 ∧
    Real.log (bsSmileDigital 1 4 (fun x => (3 - x) / 2) (-1 / 2) 2) /
      Real.log (l * 1 / (2 - 1)) ≤ α := by
  obtain ⟨l, α, hα, hl, hK, hm, hb, _⟩ := exists_returns_smile_parameters
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
  have hv (x : ℝ) : (3 - x) / 2 * Real.sqrt 4 = 3 - x := by rw [hsqrt]; ring
  have hm' : callPriceBS_σ 1 (((3 - 2) / 2) * Real.sqrt 4) 2 =
      callPriceReturns l α 1 2 := by rw [hv]; norm_num; exact hm
  have hb' : ∀ᶠ d in 𝓝[>] (0 : ℝ),
      callPriceReturns l α 1 (2 + d) +
        callPriceBS_σ 1 (((3 - (2 - d)) / 2) * Real.sqrt 4) (2 - d) ≥
      2 * callPriceReturns l α 1 2 := by simpa only [hv] using hb
  have hσ : HasDerivAt (fun x : ℝ => (3 - x) / 2) (-1 / 2) 2 :=
    ((hasDerivAt_id 2).const_sub 3).div_const 2
  exact ⟨l, α, hα, hl, hK,
    returns_survival_le_bsSmileDigital hα hl (by norm_num) hK (by norm_num)
      (by norm_num) hσ hm' hb',
    (by
      rw [bsSmileDigital_eq_erfc (by norm_num : 0 ≤ (4 : ℝ))]
      exact alpha_lower_bound_returns_smile_erfc
        (σ := fun x => (3 - x) / 2) (σ' := -1 / 2) (t := 4)
        hα hl (by norm_num) hK (by norm_num)
        (by norm_num) hσ hm' hb')⟩

-- The older conditional price-tail helper also has satisfiable premises.
example : ∃ l : ℝ, 0 < l ∧ l < 2 ∧
    Real.log (stdNormalCdf (Real.log (1 / 2) - 1 / 2)) / Real.log (l / 2) ≤ 2 := by
  let q : ℝ := stdNormalCdf (Real.log (1 / 2) - 1 / 2)
  have hq : 0 < q := stdNormalCdf_pos _
  have hq1 : q < 1 := stdNormalCdf_lt_one _
  have hq2 : q < 2 := by linarith
  have heq : q = (1 / 2) * erfc ((Real.log 2 + 1 / 2) / Real.sqrt 2) := by
    simpa [q, bsSmileDigital] using
      (bsSmileDigital_eq_erfc (S₀ := 1) (K := 2) (σ := fun _ => 1) (σ' := 0)
        (by norm_num : 0 ≤ (1 : ℝ)))
  have hpow : (q / 2) ^ (2 : ℝ) ≤ q := by
    rw [Real.rpow_two]
    nlinarith [sq_nonneg q, mul_pos hq (sub_pos.mpr hq1)]
  norm_num at heq
  refine ⟨q, hq, hq2, ?_⟩
  have h := alpha_lower_bound_smile_erfc (l := q) (α := 2) (S₀ := 1) (K₁ := 2)
    (σ := fun _ => 1) (σ' := 0) hq hq2 (by
      norm_num
      rw [← heq]
      simpa only [Real.rpow_two] using hpow)
  change Real.log q / Real.log (q / 2) ≤ 2
  norm_num at h
  rw [← heq] at h
  exact h

end TailOptionPricing
