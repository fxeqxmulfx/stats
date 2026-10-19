module

/-
  The actual lognormal Lebesgue density, arXiv:1912.00277v2,
  Section V, Eq. compound. The one-dimensional change of variables
  x = exp(z) identifies the density of the independently constructed
  Gaussian pushforward. Normalization is a consequence, not an input.
-/
public import Stats.Probability.Lognormal
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing.LognormalMeasure

/-- Section V's lognormal precision density, zero on nonpositive
precision. Its Jacobian is 1/x on the strictly positive domain. -/
noncomputable def lognormalPDF (m : ℝ) (v : NNReal) : ℝ → ENNReal :=
  (Ioi 0).indicator (fun x => gaussianPDF m v (Real.log x) * ENNReal.ofReal x⁻¹)

theorem lognormalPDF_measurable (m : ℝ) (v : NNReal) : Measurable (lognormalPDF m v) := by
  unfold lognormalPDF
  apply Measurable.indicator _ measurableSet_Ioi
  unfold gaussianPDF gaussianPDFReal
  fun_prop

/-- At positive precision, the actual density is the Gaussian log
density divided by precision, as in Section V's compound integrand. -/
theorem lognormalPDF_of_pos (m : ℝ) (v : NNReal) {x : ℝ} (hx : 0 < x) :
    lognormalPDF m v x = ENNReal.ofReal (gaussianPDFReal m v (Real.log x) / x) := by
  simp only [lognormalPDF, indicator_of_mem (show x ∈ Ioi 0 from hx), gaussianPDF,
    div_eq_mul_inv, ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]

/-- Change of variables for the literal lognormal density. The
Jacobian cancellation is proved pointwise before applying the result
to probability laws or moment integrals (Section V, Eq. compound). -/
theorem lognormalPDF_lintegral_mul (m : ℝ) (v : NNReal) (g : ℝ → ENNReal) :
    (∫⁻ x : ℝ, g x * lognormalPDF m v x) =
      ∫⁻ z : ℝ, g (Real.exp z) * gaussianPDF m v z := by
  have he : (fun x => g x * lognormalPDF m v x) =
      (Ioi 0).indicator (fun x => g x * (gaussianPDF m v (Real.log x) * ENNReal.ofReal x⁻¹)) := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ) <;> simp [lognormalPDF, hx]
  rw [he, lintegral_indicator measurableSet_Ioi]
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ)
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun x => g x * (gaussianPDF m v (Real.log x) * ENNReal.ofReal x⁻¹))
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at hj
  rw [hj]
  apply lintegral_congr
  intro z
  rw [Real.log_exp, abs_of_pos (Real.exp_pos z)]
  have hc : ENNReal.ofReal (Real.exp z) * ENNReal.ofReal (Real.exp z)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos z).le, mul_inv_cancel₀ (Real.exp_ne_zero z)]
    norm_num
  calc
    _ = (g (Real.exp z) * gaussianPDF m v z) *
        (ENNReal.ofReal (Real.exp z) * ENNReal.ofReal (Real.exp z)⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

/-- The actual Gaussian-exponential pushforward has the literal
lognormal density. Nonzero log variance is necessary: variance zero
is a point mass and has no Lebesgue density (Section V). -/
theorem lognormalReal_eq_withDensity (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    lognormalReal m v = volume.withDensity (lognormalPDF m v) := by
  ext A hA
  rw [lognormalReal, Measure.map_apply Real.measurable_exp hA,
    gaussianReal_apply m hv, withDensity_apply _ hA]
  have h := lognormalPDF_lintegral_mul m v (A.indicator (fun _ => 1))
  have he (x : ℝ) : A.indicator (fun _ => (1 : ENNReal)) x * lognormalPDF m v x =
      A.indicator (lognormalPDF m v) x := by by_cases hx : x ∈ A <;> simp [hx]
  have he' (z : ℝ) : A.indicator (fun _ => (1 : ENNReal)) (Real.exp z) * gaussianPDF m v z =
      (Real.exp ⁻¹' A).indicator (gaussianPDF m v) z := by
    by_cases hz : Real.exp z ∈ A <;> simp [hz]
  simp_rw [he, he'] at h
  rw [lintegral_indicator hA, lintegral_indicator (Real.measurable_exp hA)] at h
  exact h.symm

/-- The prior's literal density has total mass one, derived from the
actual independently normalized probability law (Section V). -/
theorem lognormalPDF_lintegral (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (∫⁻ x : ℝ, lognormalPDF m v x) = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (lognormalReal_eq_withDensity m hv)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    using h.symm

theorem lognormalPDF_ae_lt_top (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ x : ℝ, lognormalPDF m v x < ⊤ := by
  apply ae_lt_top (lognormalPDF_measurable m v)
  rw [lognormalPDF_lintegral m hv]
  norm_num

example : lognormalPDF 0 1 1 = ENNReal.ofReal (gaussianPDFReal 0 1 0 / 1) := by
  simpa using lognormalPDF_of_pos 0 1 (show (0 : ℝ) < 1 by norm_num)

example : lognormalReal 0 1 = volume.withDensity (lognormalPDF 0 1) :=
  lognormalReal_eq_withDensity _ (by norm_num)

example : (∫⁻ x : ℝ, lognormalPDF 0 1 x) = 1 := lognormalPDF_lintegral _ (by norm_num)

example : ∀ᵐ x : ℝ, lognormalPDF 0 1 x < ⊤ := lognormalPDF_ae_lt_top _ (by norm_num)

#print axioms lognormalPDF_lintegral_mul
#print axioms lognormalReal_eq_withDensity
#print axioms lognormalPDF_lintegral

end TailOptionPricing.LognormalMeasure
