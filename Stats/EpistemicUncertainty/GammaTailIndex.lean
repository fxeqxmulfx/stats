module

/-
  Matched Gamma/Student tail parameters, arXiv:1912.00277v2,
  Section VI. Positive epistemic log variance v gives Student df
  2/(exp(v)-1) and conventional scale exp(-v/4), using the source's
  Gamma RATE convention. The tail index decreases strictly in v.
  At zero the literal Gamma formulas are singular: the correct
  parameter limits are infinite df and unit scale, not df zero.
-/
public import Stats.EpistemicUncertainty.GammaMatch
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

open Real Set Filter Topology

namespace TailOptionPricing

/-- The Student tail exponent corresponding to the source's matched
Gamma shape, for positive log variance v (Section VI). -/
noncomputable def epistemicGammaTailIndex (v : ℝ) : ℝ := 2 * epistemicGammaMatchShape v

/-- The conventional Student scale from the matched Gamma RATE and
shape. It is not the source's beta itself (Section VI correction). -/
noncomputable def epistemicGammaMatchScale (v : ℝ) : ℝ :=
  √(epistemicGammaMatchRate v / epistemicGammaMatchShape v)

theorem epistemicGammaTailIndex_pos {v : ℝ} (hv : 0 < v) : 0 < epistemicGammaTailIndex v :=
  mul_pos (by norm_num) (epistemicGammaMatchShape_pos hv)

/-- The source's matched Gamma shape decreases strictly with positive
epistemic log variance, before interpreting it as a tail parameter. -/
theorem epistemicGammaMatchShape_strictAnti {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    epistemicGammaMatchShape w < epistemicGammaMatchShape v := by
  exact one_div_lt_one_div_of_lt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv))
    (sub_lt_sub_right (Real.exp_lt_exp.mpr hvw) 1)

/-- Section VI's Student tail exponent decreases strictly with
epistemic log variance. The actual tail meaning is proved separately. -/
theorem epistemicGammaTailIndex_strictAnti {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    epistemicGammaTailIndex w < epistemicGammaTailIndex v :=
  mul_lt_mul_of_pos_left (epistemicGammaMatchShape_strictAnti hv hvw) (by norm_num)

theorem epistemicGammaMatchRate_div_shape {v : ℝ} (hv : 0 < v) :
    epistemicGammaMatchRate v / epistemicGammaMatchShape v = Real.exp (-v / 2) := by
  have hd : Real.exp v - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)).ne'
  unfold epistemicGammaMatchRate epistemicGammaMatchShape
  field_simp

/-- Correct conventional Student scale for the source's matched Gamma
rate is exp(-v/4), rather than the printed Gamma rate beta. -/
theorem epistemicGammaMatchScale_eq {v : ℝ} (hv : 0 < v) :
    epistemicGammaMatchScale v = Real.exp (-v / 4) := by
  rw [epistemicGammaMatchScale, epistemicGammaMatchRate_div_shape hv, ← Real.exp_half]
  congr 1
  ring

theorem epistemicGammaMatchScale_pos {v : ℝ} (hv : 0 < v) : 0 < epistemicGammaMatchScale v := by
  rw [epistemicGammaMatchScale_eq hv]
  exact Real.exp_pos _

/-- The source's singular zero-variance formula has infinite Student
df as v tends to zero from above. Literal real division at zero does
not give a proper finite-df boundary model (Section VI). -/
theorem epistemicGammaTailIndex_tendsto_zero_right :
    Tendsto epistemicGammaTailIndex (𝓝[>] (0 : ℝ)) atTop := by
  change Tendsto (fun v : ℝ => 2 * (1 / (Real.exp v - 1))) (𝓝[>] 0) atTop
  have hd₀ : Tendsto (fun v : ℝ => Real.exp v - 1) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.exp_zero, sub_self] using
      ((Real.continuous_exp.tendsto 0).sub_const 1).mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun v : ℝ => Real.exp v - 1) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd₀, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)
  have h := (tendsto_inv_nhdsGT_zero.comp hd).atTop_mul_const (show (0 : ℝ) < 2 by norm_num)
  simpa only [epistemicGammaTailIndex, epistemicGammaMatchShape, one_div, Function.comp_def, mul_comm] using h

/-- At very large epistemic variance the matched Student tail index
tends to zero through positive values, without assigning df zero a
proper Student law (Section VI). -/
theorem epistemicGammaTailIndex_tendsto_atTop : Tendsto epistemicGammaTailIndex atTop (𝓝 0) := by
  change Tendsto (fun v : ℝ => 2 * (1 / (Real.exp v - 1))) atTop (𝓝 0)
  have hd : Tendsto (fun v : ℝ => Real.exp v - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) Real.tendsto_exp_atTop
  have h := (tendsto_inv_atTop_zero.comp hd).const_mul (2 : ℝ)
  simpa only [epistemicGammaTailIndex, epistemicGammaMatchShape, one_div,
    Function.comp_def, mul_zero] using h

/-- Unit conventional scale is the right limit at zero epistemic
variance; combine with the infinite-df limit, not the singular value. -/
theorem epistemicGammaMatchScale_tendsto_zero_right :
    Tendsto epistemicGammaMatchScale (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : Continuous (fun v : ℝ => Real.exp (-v / 4)) := by fun_prop
  have h : Tendsto (fun v : ℝ => Real.exp (-v / 4)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [neg_zero, zero_div, Real.exp_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (epistemicGammaMatchScale_eq hv).symm

/-- The conventional scale also decreases, while the actual tail
comparison must account for the simultaneously decreasing df. -/
theorem epistemicGammaMatchScale_strictAnti {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
    epistemicGammaMatchScale w < epistemicGammaMatchScale v := by
  rw [epistemicGammaMatchScale_eq (hv.trans hvw), epistemicGammaMatchScale_eq hv]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem epistemicGammaMatchScale_tendsto_atTop : Tendsto epistemicGammaMatchScale atTop (𝓝 0) := by
  have hlin : Tendsto (fun v : ℝ => v / 4) atTop atTop := by
    simpa only [id_eq] using tendsto_id.atTop_div_const (show (0 : ℝ) < 4 by norm_num)
  apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
  simp only [Function.comp_def]
  rw [epistemicGammaMatchScale_eq hv]
  congr 1
  ring

/-- Literal real-division values at zero are singular formula
artifacts, different from the right limits above. They do not specify
the source's zero-uncertainty Gaussian population. -/
theorem epistemicGammaMatch_zero_parameters :
    epistemicGammaTailIndex 0 = 0 ∧ epistemicGammaMatchScale 0 = 0 := by
  simp [epistemicGammaTailIndex, epistemicGammaMatchScale, epistemicGammaMatchShape,
    epistemicGammaMatchRate]

example : 0 < epistemicGammaTailIndex 1 := epistemicGammaTailIndex_pos (by norm_num)

example : epistemicGammaMatchShape 2 < epistemicGammaMatchShape 1 :=
  epistemicGammaMatchShape_strictAnti (by norm_num) (by norm_num)

example : epistemicGammaTailIndex 2 < epistemicGammaTailIndex 1 :=
  epistemicGammaTailIndex_strictAnti (by norm_num) (by norm_num)

example : epistemicGammaMatchRate 1 / epistemicGammaMatchShape 1 = Real.exp (-1 / 2) :=
  epistemicGammaMatchRate_div_shape (by norm_num)

example : epistemicGammaMatchScale 1 = Real.exp (-1 / 4) := epistemicGammaMatchScale_eq (by norm_num)

example : 0 < epistemicGammaMatchScale 1 := epistemicGammaMatchScale_pos (by norm_num)

example : epistemicGammaMatchScale 2 < epistemicGammaMatchScale 1 :=
  epistemicGammaMatchScale_strictAnti (by norm_num) (by norm_num)

#print axioms epistemicGammaMatchShape_strictAnti
#print axioms epistemicGammaTailIndex_strictAnti
#print axioms epistemicGammaMatchScale_eq
#print axioms epistemicGammaTailIndex_tendsto_zero_right
#print axioms epistemicGammaTailIndex_tendsto_atTop
#print axioms epistemicGammaMatchScale_tendsto_zero_right
#print axioms epistemicGammaMatchScale_strictAnti
#print axioms epistemicGammaMatchScale_tendsto_atTop

end TailOptionPricing
