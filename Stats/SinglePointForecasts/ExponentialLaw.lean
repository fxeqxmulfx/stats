module

/-
  The supported law transformation for arXiv:2007.16096v1, "Uncertainty
  goes one way", lines 250–260. An exponential rate with parameter λ,
  positive elapsed time t and positive initial value X₀ produces an actual
  Pareto law: survival one below X₀ and (X₀/s)^(λ/t) above X₀.
-/
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Actual exponential-law survival, including its support boundary. -/
theorem expMeasure_real_Ioi {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (expMeasure r).real (Ioi c) = if 0 ≤ c then Real.exp (-(r * c)) else 1 := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h := measureReal_add_measureReal_compl (μ := expMeasure r)
    (s := Iic c) measurableSet_Iic
  rw [compl_Iic, probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hr] at h
  split_ifs with hc <;> split_ifs at h <;> linarith

/-- Pushforward of the supported exponential rate law by the paper's
actual growth map. Here `t` is the positive elapsed time `t-t₀`. -/
noncomputable def exponentialGrowthLaw (X₀ t lam : ℝ) : Measure ℝ :=
  (expMeasure lam).map (fun r => X₀ * Real.exp (t * r))

/-- A positive exponential rate parameter gives a genuine probability
law under the growth transformation, for every scale and elapsed time. -/
theorem exponentialGrowthLaw_probability (X₀ t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    IsProbabilityMeasure (exponentialGrowthLaw X₀ t lam) := by
  let : IsProbabilityMeasure (expMeasure lam) := isProbabilityMeasure_expMeasure hlam
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- Above the support boundary, the actual transformed law has the
Pareto survival formula with tail index `λ/t`. -/
theorem exponentialGrowthLaw_survival_of_ge {X₀ t lam s : ℝ}
    (hX₀ : 0 < X₀) (ht : 0 < t) (hlam : 0 < lam) (hs : X₀ ≤ s) :
    (exponentialGrowthLaw X₀ t lam).real (Ioi s) = (X₀ / s) ^ (lam / t) := by
  have hspos : 0 < s := hX₀.trans_le hs
  have hpre : (fun r => X₀ * Real.exp (t * r)) ⁻¹' Ioi s =
      Ioi (Real.log (s / X₀) / t) := by
    ext r
    simp only [mem_preimage, mem_Ioi]
    rw [div_lt_iff₀ ht, Real.log_lt_iff_lt_exp (div_pos hspos hX₀),
      div_lt_iff₀ hX₀, mul_comm r t, mul_comm (Real.exp (t * r)) X₀]
  have hc : 0 ≤ Real.log (s / X₀) / t :=
    div_nonneg (Real.log_nonneg ((one_le_div hX₀).mpr hs)) ht.le
  change ((expMeasure lam).map (fun r => X₀ * Real.exp (t * r)) (Ioi s)).toReal = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
  change (expMeasure lam).real (Ioi (Real.log (s / X₀) / t)) = _
  rw [expMeasure_real_Ioi hlam, ite_eq_left hc, Real.rpow_def_of_pos (div_pos hX₀ hspos),
    Real.log_div hX₀.ne' hspos.ne', Real.log_div hspos.ne' hX₀.ne']
  congr 1
  ring

/-- The transformed exponential law has survival one below its positive
initial value, including at nonpositive thresholds. -/
theorem exponentialGrowthLaw_survival_of_lt {X₀ t lam s : ℝ}
    (hX₀ : 0 < X₀) (ht : 0 < t) (hlam : 0 < lam) (hs : s < X₀) :
    (exponentialGrowthLaw X₀ t lam).real (Ioi s) = 1 := by
  let : IsProbabilityMeasure (expMeasure lam) := isProbabilityMeasure_expMeasure hlam
  by_cases hspos : 0 < s
  · have hpre : (fun r => X₀ * Real.exp (t * r)) ⁻¹' Ioi s =
        Ioi (Real.log (s / X₀) / t) := by
      ext r
      simp only [mem_preimage, mem_Ioi]
      rw [div_lt_iff₀ ht, Real.log_lt_iff_lt_exp (div_pos hspos hX₀),
        div_lt_iff₀ hX₀, mul_comm r t, mul_comm (Real.exp (t * r)) X₀]
    have hc : Real.log (s / X₀) / t < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg (div_pos hspos hX₀)
        ((div_lt_one hX₀).mpr hs)) ht
    change ((expMeasure lam).map (fun r => X₀ * Real.exp (t * r)) (Ioi s)).toReal = _
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
    change (expMeasure lam).real (Ioi (Real.log (s / X₀) / t)) = _
    rw [expMeasure_real_Ioi hlam, ite_eq_right (not_le.mpr hc)]
  · have hpre : (fun r => X₀ * Real.exp (t * r)) ⁻¹' Ioi s = univ := by
      ext r
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact (le_of_not_gt hspos).trans_lt (mul_pos hX₀ (Real.exp_pos _))
    change ((expMeasure lam).map (fun r => X₀ * Real.exp (t * r)) (Ioi s)).toReal = _
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
    simp

/-- Full supported Pareto survival, derived from the actual exponential
rate law. This proves the distributional claim in the source's lines
250–260 rather than merely matching two candidate density expressions. -/
theorem exponentialGrowthLaw_survival {X₀ t lam : ℝ}
    (hX₀ : 0 < X₀) (ht : 0 < t) (hlam : 0 < lam) (s : ℝ) :
    (exponentialGrowthLaw X₀ t lam).real (Ioi s) =
      if s < X₀ then 1 else (X₀ / s) ^ (lam / t) := by
  by_cases hs : s < X₀
  · rw [ite_eq_left hs]
    exact exponentialGrowthLaw_survival_of_lt hX₀ ht hlam hs
  · rw [ite_eq_right hs]
    exact exponentialGrowthLaw_survival_of_ge hX₀ ht hlam (le_of_not_gt hs)

example : (expMeasure 1).real (Ioi 0) = 1 := by
  have h := expMeasure_real_Ioi (by norm_num : (0 : ℝ) < 1) 0
  norm_num at h
  exact h

example : IsProbabilityMeasure (exponentialGrowthLaw 1 2 1) :=
  exponentialGrowthLaw_probability 1 2 (by norm_num)

example : (exponentialGrowthLaw 1 2 1).real (Ioi 4) = (1 / 4) ^ (1 / 2 : ℝ) :=
  exponentialGrowthLaw_survival_of_ge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example : (exponentialGrowthLaw 1 2 1).real (Ioi (1 / 2)) = 1 :=
  exponentialGrowthLaw_survival_of_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example : (exponentialGrowthLaw 1 2 1).real (Ioi (-1)) = 1 :=
  exponentialGrowthLaw_survival_of_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example (s : ℝ) : (exponentialGrowthLaw 1 2 1).real (Ioi s) =
    if s < 1 then 1 else (1 / s) ^ (1 / 2 : ℝ) :=
  exponentialGrowthLaw_survival (by norm_num) (by norm_num) (by norm_num) s

end TailOptionPricing
