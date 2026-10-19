module

/-
  Actual Gamma/Lognormal moment match, arXiv:1912.00277v2,
  Section VI. The source's alpha and beta formulas match actual
  means, variances and coefficients of variation. Beta is a RATE.
  This identity does not assert a distributional approximation bound.
-/
public import Stats.Probability.GammaMoments
public import Stats.Probability.Lognormal

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace TailOptionPricing

open LognormalMeasure

/-- Section VI's Gamma shape; v represents the lognormal log variance
S squared. Positive v is required for a proper Gamma parameter. -/
noncomputable def epistemicGammaMatchShape (v : ℝ) : ℝ := 1 / (Real.exp v - 1)

/-- Section VI's Gamma RATE beta, not its scale. -/
noncomputable def epistemicGammaMatchRate (v : ℝ) : ℝ :=
  Real.exp (-v / 2) / (Real.exp v - 1)

theorem epistemicGammaMatchShape_pos {v : ℝ} (hv : 0 < v) :
    0 < epistemicGammaMatchShape v :=
  div_pos zero_lt_one (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv))

theorem epistemicGammaMatchRate_pos {v : ℝ} (hv : 0 < v) :
    0 < epistemicGammaMatchRate v :=
  div_pos (Real.exp_pos _) (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv))

theorem epistemicGammaMatchRate_eq (v : ℝ) :
    epistemicGammaMatchRate v = (Real.exp (v / 2))⁻¹ / (Real.exp v - 1) := by
  unfold epistemicGammaMatchRate
  rw [show -v / 2 = -(v / 2) by ring, Real.exp_neg]

/-- The source's matched shape and rate specify an actual normalized
Gamma precision population, before evaluating any moment (Section VI). -/
theorem epistemicGammaMatch_probability {v : ℝ} (hv : 0 < v) :
    IsProbabilityMeasure (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) :=
  isProbabilityMeasure_gammaMeasure (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv)

/-- The source's Gamma parameters match the actual lognormal precision
mean, using independently proved actual moments of both laws. -/
theorem epistemicGammaMatch_mean {v : NNReal} (hv : 0 < (v : ℝ)) :
    (∫ l : ℝ, l ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
      ∫ l : ℝ, l ∂lognormalReal 0 v := by
  rw [gammaMeasure_mean (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv),
    lognormalReal_mean, epistemicGammaMatchShape, epistemicGammaMatchRate_eq]
  simp only [zero_add]
  have hd : Real.exp (v : ℝ) - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)).ne'
  field_simp

/-- The actual Gamma and lognormal precision variances also match,
so this is a genuine two-moment match (Section VI). -/
theorem epistemicGammaMatch_variance {v : NNReal} (hv : 0 < (v : ℝ)) :
    variance (fun l : ℝ => l)
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
        variance (fun l : ℝ => l) (lognormalReal 0 v) := by
  rw [gammaMeasure_variance (epistemicGammaMatchShape_pos hv) (epistemicGammaMatchRate_pos hv),
    lognormalReal_variance, epistemicGammaMatchShape, epistemicGammaMatchRate_eq]
  simp only [mul_zero, zero_add]
  have hd : Real.exp (v : ℝ) - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hv)).ne'
  have he : Real.exp ((v : ℝ) / 2) ^ 2 = Real.exp (v : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  field_simp
  exact he

/-- The actual coefficients of variation coincide as a consequence
of matching actual means and variances, not of naming the parameters
“matched” (Section VI). -/
theorem epistemicGammaMatch_cv {v : NNReal} (hv : 0 < (v : ℝ)) :
    √(variance (fun l : ℝ => l)
      (gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v))) /
        (∫ l : ℝ, l ∂gammaMeasure (epistemicGammaMatchShape v) (epistemicGammaMatchRate v)) =
      √(variance (fun l : ℝ => l) (lognormalReal 0 v)) / (∫ l : ℝ, l ∂lognormalReal 0 v) := by
  rw [epistemicGammaMatch_variance hv, epistemicGammaMatch_mean hv]

example : 0 < epistemicGammaMatchShape 1 := epistemicGammaMatchShape_pos (by norm_num)

example : 0 < epistemicGammaMatchRate 1 := epistemicGammaMatchRate_pos (by norm_num)

example : IsProbabilityMeasure (gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) :=
  epistemicGammaMatch_probability (by norm_num)

example : (∫ l : ℝ, l ∂gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) =
    ∫ l : ℝ, l ∂lognormalReal 0 1 := by
  simpa only [NNReal.coe_one] using epistemicGammaMatch_mean (v := 1) (by norm_num)

example : variance (fun l : ℝ => l)
    (gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) =
      variance (fun l : ℝ => l) (lognormalReal 0 1) := by
  simpa only [NNReal.coe_one] using epistemicGammaMatch_variance (v := 1) (by norm_num)

example : √(variance (fun l : ℝ => l)
    (gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1))) /
      (∫ l : ℝ, l ∂gammaMeasure (epistemicGammaMatchShape 1) (epistemicGammaMatchRate 1)) =
        √(variance (fun l : ℝ => l) (lognormalReal 0 1)) / (∫ l : ℝ, l ∂lognormalReal 0 1) :=
  by simpa only [NNReal.coe_one] using epistemicGammaMatch_cv (v := 1) (by norm_num)

#print axioms epistemicGammaMatch_probability
#print axioms epistemicGammaMatch_mean
#print axioms epistemicGammaMatch_variance
#print axioms epistemicGammaMatch_cv

end TailOptionPricing
