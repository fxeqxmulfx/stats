module

/-
  Actual Beta-law power moments used in the finite-sample correction to
  arXiv:2004.05894v1, Proposition 1 and its following mean formula.
  The shifted Beta density proves the integral, with positive shape parameters.
-/
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Nonnegativity of the supported Beta density at every real argument. -/
theorem betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp only [mem_Ioo] at hx
    rw [betaPDFReal, ite_eq_right hx]

/-- The real supported Beta density integrates to one for positive shapes. -/
theorem integral_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ, betaPDFReal a b x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (betaPDFReal_nonneg ha hb))
    (measurable_betaPDFReal a b).aestronglyMeasurable]
  change (∫⁻ x : ℝ, betaPDF a b x).toReal = 1
  rw [lintegral_betaPDF_eq_one ha hb, ENNReal.toReal_one]

/-- Multiplication by a power shifts the first Beta shape, with the exact
normalizing-constant ratio. This identity includes the support branches. -/
theorem betaPDFReal_mul_rpow {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (har : 0 < a + r)
    (x : ℝ) :
    betaPDFReal a b x * x ^ r =
      (ProbabilityTheory.beta (a + r) b / ProbabilityTheory.beta a b) *
        betaPDFReal (a + r) b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, ite_eq_left hx]
    rw [show a + r - 1 = (a - 1) + r by ring, Real.rpow_add hx.1]
    have h1 := (beta_pos ha hb).ne'
    have h2 := (beta_pos har hb).ne'
    field_simp
  · simp only [betaPDFReal, ite_eq_right hx, zero_mul, mul_zero]

/-- Actual Beta-law power moment, with its integrability range `a+r>0`.
Used for the finite-sample correction of arXiv:2004.05894v1, Proposition 1. -/
theorem betaMeasure_integral_rpow {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (har : 0 < a + r) :
    ∫ x : ℝ, x ^ r ∂betaMeasure a b =
      ProbabilityTheory.beta (a + r) b / ProbabilityTheory.beta a b := by
  have hm : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [smul_eq_mul, betaPDF,
    ENNReal.toReal_ofReal (betaPDFReal_nonneg ha hb _), betaPDFReal_mul_rpow ha hb har]
  rw [integral_const_mul, integral_betaPDFReal har hb, mul_one]

/-- Integrability of the actual Beta-law power throughout `a+r>0`.
The density-weighted integrand is a multiple of a normalized shifted density. -/
theorem betaMeasure_integrable_rpow {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (har : 0 < a + r) : Integrable (fun x : ℝ => x ^ r) (betaMeasure a b) := by
  have hm : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [betaMeasure, integrable_withDensity_iff hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun x : ℝ => x ^ r * (betaPDF a b x).toReal) =
      fun x => (ProbabilityTheory.beta (a + r) b / ProbabilityTheory.beta a b) *
        betaPDFReal (a + r) b x := by
    funext x
    rw [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg ha hb x), mul_comm,
      betaPDFReal_mul_rpow ha hb har]
  rw [he]
  exact (integrable_of_integral_eq_one (integral_betaPDFReal har hb)).const_mul _

end TailOptionPricing
