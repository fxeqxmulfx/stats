module

/-
  Supported and normalized Beta(1,n) density and CDF for the correction
  to arXiv:2004.05894v1, Remark 1. The polynomial alone is not a global CDF.
-/
public import Stats.HiddenMoments.SurvivalKernel
public import Stats.Probability.BetaMoments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The Beta(1,n) normalizing constant for a positive finite sample. -/
theorem beta_one_nat (n : ℕ) (hn : 0 < n) : ProbabilityTheory.beta 1 n = 1 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hg : Real.Gamma (n : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne'
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_one, one_mul, add_comm (1 : ℝ), Real.Gamma_add_one hn0]
  field_simp

/-- The normalized supported density for the finite-sample correction
to arXiv:2004.05894v1, Remark 1. -/
theorem betaPDFReal_one_nat_eq (n : ℕ) (hn : 0 < n) (x : ℝ) :
    betaPDFReal 1 n x = (Ioo (0 : ℝ) 1).indicator
      (fun x => paretoSampleSurvivalRatioPDF n x) x := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.ne'
  have he : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  unfold betaPDFReal paretoSampleSurvivalRatioPDF
  rw [beta_one_nat n hn]
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp only [mem_Ioo] at hx
    rw [ite_eq_left hx, indicator_of_mem (s := Ioo (0 : ℝ) 1) hx]
    rw [sub_self, Real.rpow_zero, mul_one, one_div_one_div, he, Real.rpow_natCast]
  · simp only [mem_Ioo] at hx
    rw [ite_eq_right hx, indicator_of_notMem (s := Ioo (0 : ℝ) 1) hx]

/-- The candidate polynomial integrates to its candidate CDF between zero
and a nonnegative endpoint (arXiv:2004.05894v1, Remark 1 correction). -/
theorem paretoSampleSurvivalRatioPDF_integral {n : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    ∫ x in Ioc (0 : ℝ) y, paretoSampleSurvivalRatioPDF n x =
      paretoSampleSurvivalRatioCDF n y := by
  rw [← intervalIntegral.integral_of_le hy]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => paretoSampleSurvivalRatioPDF_eq_deriv n x)
    (Continuous.intervalIntegrable (by
      unfold paretoSampleSurvivalRatioPDF
      fun_prop) _ _)]
  simp [paretoSampleSurvivalRatioCDF]

/-- Full CDF of the actual Beta(1,n) measure, including both support
branches. This is the finite-sample correction to arXiv:2004.05894v1, Remark 1. -/
theorem betaMeasure_one_nat_cdf {n : ℕ} (hn : 0 < n) (y : ℝ) :
    (betaMeasure 1 n).real (Iic y) =
      if y ≤ 0 then 0 else if 1 ≤ y then 1
      else paretoSampleSurvivalRatioCDF n y := by
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm : Measurable (betaPDF 1 n) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal 1 n)
  rw [betaMeasure, withDensity_real_apply_eq_integral
    hm.aemeasurable
    (Filter.Eventually.of_forall (fun x _ => ENNReal.ofReal_lt_top))
    measurableSet_Iic.nullMeasurableSet]
  simp_rw [betaPDF, ENNReal.toReal_ofReal
    (betaPDFReal_nonneg (a := 1) (b := (n : ℝ)) (by norm_num) hpos _),
    betaPDFReal_one_nat_eq n hn]
  rw [setIntegral_indicator measurableSet_Ioo]
  split_ifs with hy0 hy1
  · have he : Iic y ∩ Ioo (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false,
        not_and]
      intro hx hx0
      linarith
    simp [he]
  · have he : Iic y ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
      exact inter_eq_right.mpr (fun x hx => hx.2.le.trans hy1)
    rw [he, ← integral_Ioc_eq_integral_Ioo, paretoSampleSurvivalRatioPDF_integral (by norm_num)]
    simp only [paretoSampleSurvivalRatioCDF, sub_self,
      zero_pow hn.ne', sub_zero]
  · have he : Iic y ∩ Ioo (0 : ℝ) 1 = Ioc (0 : ℝ) y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · intro hx
        exact ⟨hx.2.1, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1, hx.2.trans_lt (lt_of_not_ge hy1)⟩
    rw [he, paretoSampleSurvivalRatioPDF_integral (le_of_not_ge hy0)]

end TailOptionPricing
