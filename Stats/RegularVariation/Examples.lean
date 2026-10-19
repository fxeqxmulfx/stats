module

/-
  Karamata's theory of regular variation — basic examples.

  Constant functions, `Real.log`, iterated logarithms.
-/
public import Stats.RegularVariation.Defs
public import Stats.RegularVariation.Closure

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- A nonzero constant function is slowly varying. -/
theorem isSlowlyVarying_const {c : ℝ} (hc : c ≠ 0) :
    IsSlowlyVarying (fun _ => c) := by
  intro _ _
  simp [div_self hc]

/-- `Real.log` is slowly varying:
    `log(t·x)/log(t) = 1 + log x / log t → 1` as `t → ∞`. -/
theorem isSlowlyVarying_log : IsSlowlyVarying Real.log := by
  intro x hx
  have h_ratio_eq : ∀ᶠ t in atTop,
      Real.log (t * x) / Real.log t = 1 + Real.log x / Real.log t := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht_pos : 0 < t := lt_trans zero_lt_one ht
    have h_log_pos : 0 < Real.log t := Real.log_pos ht
    rw [Real.log_mul ht_pos.ne' hx.ne']
    field_simp
  have h_to_zero : Tendsto (fun t : ℝ => Real.log x / Real.log t) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop (Real.log x)
  have h_to_one : Tendsto (fun t : ℝ => 1 + Real.log x / Real.log t)
      atTop (𝓝 1) := by
    have h_const : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have := h_const.add h_to_zero
    simpa using this
  exact h_to_one.congr' (h_ratio_eq.mono (fun _ h => h.symm))

/-- Iterated logarithms are slowly varying: `(log s)^k` for any real `k`.
    Direct corollary of `isSlowlyVarying_log` and the `rpow` closure. -/
theorem isSlowlyVarying_log_rpow (k : ℝ) :
    IsSlowlyVarying (fun s => (Real.log s) ^ k) :=
  isSlowlyVarying_log.rpow (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact Real.log_pos ht) k

end TailOptionPricing
