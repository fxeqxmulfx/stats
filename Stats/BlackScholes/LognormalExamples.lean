module

/-
  Support and variance regression certificates for the actual lognormal
  law in arXiv:1908.02347v3, Arbitrage Boundaries. Concrete examples also
  witness the corrected domains of the density, CDF and derivative APIs.
-/
public import Stats.BlackScholes.Erfc
public import Stats.BlackScholes.PutCall

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

example : survivalLN 1 0 1 0 = 1 := survivalLN_of_nonpos (by norm_num) le_rfl

example : survivalLN 2 0 0 1 = 1 := by norm_num [survivalLN_zero_var]

example : survivalLN 2 0 0 2 = 0 := by norm_num [survivalLN_zero_var]

example : callPriceBS 2 0 0 1 = 1 := by norm_num [callPriceBS_zero_var]

example : callPriceBS 2 0 0 (-1) = 3 := by norm_num [callPriceBS_zero_var]

example : ContinuousOn (callPriceBS 2 0 0) (Ioi 0) :=
  callPriceBS_continuousOn (by norm_num)

/-- Zero variance really is outside the global continuity claim: the
actual survival jumps at the deterministic terminal value. -/
theorem survivalLN_zero_var_not_continuousAt :
    ¬ContinuousAt (survivalLN 2 0 0) 2 := by
  intro h
  have hleft : Tendsto (survivalLN 2 0 0) (𝓝[<] 2) (𝓝 1) := by
    apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (1 : ℝ)) _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    symm
    rw [survivalLN_zero_var, Real.exp_zero, mul_one]
    exact ite_eq_left hs
  have hzero : Tendsto (survivalLN 2 0 0) (𝓝[<] 2) (𝓝 0) := by
    have ht := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 2))
    simpa [survivalLN_zero_var] using ht
  have hbad := tendsto_nhds_unique hleft hzero
  norm_num at hbad

example : survivalLN 1 0 1 2 =
    ∫ x in Ioi (Real.log 2), gaussianPDFReal 0 1 x := by
  simpa using survivalLN_eq_integral (μ := 0) (v := 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num : (0 : ℝ) < 2)

example : survivalLN 1 0 1 2 = 1 - stdNormalCdf (Real.log 2) := by
  simpa using survivalLN_eq_one_sub_stdNormalCdf (μ := 0) (v := 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num : (0 : ℝ) < 2)

example : survivalLN 1 (-(1 / 2)) 1 2 =
    stdNormalCdf (Real.log (1 / 2) - 1 / 2) := by
  simpa using survivalLN_riskNeutral_eq_stdNormalCdf (S₀ := 1) (K := 2) (v := 1)
    (by norm_num) (by norm_num) (by norm_num)

example : survivalLN 1 0 1 2 = (1 / 2) * erfc (Real.log 2 / Real.sqrt 2) := by
  simpa using survivalLN_eq_half_erfc (μ := 0) (v := 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num : (0 : ℝ) < 2)

example : ContinuousOn (survivalLN 1 0 1) (Ioi 0) :=
  survivalLN_continuousOn (by norm_num) (by norm_num)

example : HasDerivAt (callPriceBS 1 0 1) (-(survivalLN 1 0 1 2)) 2 :=
  callPriceBS_hasDerivAt (by norm_num) (by norm_num) (by norm_num)

example : HasDerivAt (survivalLN 1 0 1)
    (-gaussianPDFReal 0 1 (Real.log (2 / 1)) / 2) 2 :=
  survivalLN_hasDerivAt (by norm_num) (by norm_num) (by norm_num)

-- Put–call parity now includes the same genuine zero-variance law.
example : callPriceBS 2 0 0 1 - putPriceBS 2 0 0 1 = 1 := by
  have h := putCallParity_BS (S₀ := 2) (μ := 0) (v := 0) (K := 1)
  norm_num at h
  exact h

#print axioms callPriceBS_eq_law_expectation
#print axioms callPriceBS_zero_var
#print axioms survivalLN_zero_var_not_continuousAt

end TailOptionPricing
