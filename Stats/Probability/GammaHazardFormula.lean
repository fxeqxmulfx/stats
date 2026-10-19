module

/-
  Actual Gamma survival and the incomplete-Gamma hazard display in
  arXiv:1912.00277v2, Section VI. The preceding density uses RATE r;
  the displayed hazard instead uses SCALE b. We prove both formulas
  for the same actual probability measure, with b=1/r explicitly.
  The existing incompleteGamma is its genuine Euler tail integral.
  Rescaling that integral changes the threshold to r*x. Substitution
  r=1/b then changes it to x/b and moves the scale b into the hazard's
  denominator, recovering the printed finite display literally.
-/
public import Stats.Probability.GammaHazard
public import Stats.Kappa.CubicStudent

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual positive-axis Gamma density after rescaling its Euler
kernel to rate one. Section VI's r is a rate, not a scale. -/
theorem gammaPDFReal_eq_scaled (a : ℝ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    gammaPDFReal a r x = r / Real.Gamma a *
      ((r * x) ^ (a - 1) * Real.exp (-(r * x))) := by
  have hp : r ^ a = r * r ^ (a - 1) := by
    calc
      r ^ a = r ^ ((a - 1) + 1) := by congr 1; ring
      _ = r * r ^ (a - 1) := by rw [Real.rpow_add hr, Real.rpow_one]; ring
  simp only [gammaPDFReal, hx.le, ite_true]
  rw [Real.mul_rpow hr.le hx.le, hp]
  ring

/-- The upper incomplete-Gamma integral is the actual population
survival times Gamma(a), for positive shape, rate and threshold.
This proves the source display from the density, by t=r*x. -/
theorem gammaMeasure_survival_eq_incompleteGamma {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    (gammaMeasure a r).real (Ioi x) = incompleteGamma a (r * x) / Real.Gamma a := by
  rw [gammaMeasure_survival_eq_integral ha hr]
  calc
    _ = (r / Real.Gamma a) *
        ∫ y : ℝ in Ioi x, (r * y) ^ (a - 1) * Real.exp (-(r * y)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact gammaPDFReal_eq_scaled a hr (hx.trans hy)
    _ = (r / Real.Gamma a) * (r⁻¹ * incompleteGamma a (r * x)) := by
      rw [integral_comp_mul_left_Ioi (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) x hr]
      rfl
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        _ = (r * r⁻¹) * (incompleteGamma a (r * x) * (Real.Gamma a)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hr.ne', one_mul]; rfl

/-- Multiplying the actual population survival by the complete Gamma
recovers the Euler tail integral (Section VI). This also fixes which
argument is rescaled when converting rate to scale. -/
theorem gammaMeasure_survival_mul_gamma {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    (gammaMeasure a r).real (Ioi x) * Real.Gamma a = incompleteGamma a (r * x) := by
  exact (eq_div_iff (Real.Gamma_pos_of_pos ha).ne').mp
    (gammaMeasure_survival_eq_incompleteGamma ha hr hx)

/-- Positivity of the genuine incomplete-Gamma tail integral follows
from a proper unit-rate Gamma population and its positive survival. -/
theorem incompleteGamma_pos {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    0 < incompleteGamma a z := by
  have h := gammaMeasure_survival_eq_incompleteGamma (r := 1) ha (by norm_num) hz
  simp only [one_mul] at h
  have he : incompleteGamma a z = (gammaMeasure a 1).real (Ioi z) * Real.Gamma a :=
    (eq_div_iff (Real.Gamma_pos_of_pos ha).ne').mp h |>.symm
  rw [he]
  exact mul_pos (gammaMeasure_survival_pos ha (by norm_num) hz) (Real.Gamma_pos_of_pos ha)

/-- Section VI's finite hazard formula in the RATE convention used
by its density and moment match. The denominator is the proved
upper incomplete-Gamma integral, not an assumed survival formula. -/
theorem gammaHazard_eq_incompleteGamma {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    gammaHazard a r x =
      r * (r * x) ^ (a - 1) * Real.exp (-(r * x)) / incompleteGamma a (r * x) := by
  rw [gammaHazard, gammaPDFReal_eq_scaled a hr hx,
    gammaMeasure_survival_eq_incompleteGamma ha hr hx]
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hi : incompleteGamma a (r * x) ≠ 0 := (incompleteGamma_pos ha (mul_pos hr hx)).ne'
  field_simp

/-- Actual survival with an explicit SCALE b equals Gamma(a,x/b)/Gamma(a).
The actual probability law therefore has rate 1/b (Section VI). -/
theorem gammaMeasure_survival_scale {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    (gammaMeasure a (1 / b)).real (Ioi x) = incompleteGamma a (x / b) / Real.Gamma a := by
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm b⁻¹ x] using
    gammaMeasure_survival_eq_incompleteGamma ha (one_div_pos.mpr hb) hx

/-- The literal Section VI hazard display is correct when its b is
SCALE, explicitly 1/r. The source's earlier beta is RATE, so using
the same parameter for both would change the probability law. -/
theorem gammaHazard_scale_eq_incompleteGamma {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    gammaHazard a (1 / b) x =
      Real.exp (-(x / b)) * (x / b) ^ (a - 1) / (b * incompleteGamma a (x / b)) := by
  rw [gammaHazard_eq_incompleteGamma ha (one_div_pos.mpr hb) hx]
  have he : 1 / b * x = x / b := by ring
  rw [he]
  ring

/-- Section VI's reciprocal hazard limit is valid with SCALE b.
The actual law is Gamma(a,rate=1/b); with rate r the limit is r. -/
theorem gammaHazard_scale_tendsto_inverse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (gammaHazard a (1 / b)) atTop (𝓝 (1 / b)) :=
  gammaHazard_tendsto_rate ha (one_div_pos.mpr hb)

example : gammaPDFReal 2 3 1 = (3 : ℝ) / Real.Gamma 2 *
    ((3 * 1 : ℝ) ^ (2 - 1 : ℝ) * Real.exp (-(3 * 1))) :=
  gammaPDFReal_eq_scaled 2 (by norm_num) (by norm_num)

example : (gammaMeasure 2 3).real (Ioi 1) = incompleteGamma 2 (3 * 1) / Real.Gamma 2 :=
  gammaMeasure_survival_eq_incompleteGamma (by norm_num) (by norm_num) (by norm_num)

example : (gammaMeasure 2 3).real (Ioi 1) * Real.Gamma 2 = incompleteGamma 2 (3 * 1) :=
  gammaMeasure_survival_mul_gamma (by norm_num) (by norm_num) (by norm_num)

example : 0 < incompleteGamma 2 3 := incompleteGamma_pos (by norm_num) (by norm_num)

example : gammaHazard 2 3 1 =
    (3 * (3 * 1 : ℝ) ^ (2 - 1 : ℝ) * Real.exp (-(3 * 1))) / incompleteGamma 2 (3 * 1) :=
  gammaHazard_eq_incompleteGamma (by norm_num) (by norm_num) (by norm_num)

example : (gammaMeasure 2 (1 / 3)).real (Ioi 1) = incompleteGamma 2 (1 / 3) / Real.Gamma 2 :=
  gammaMeasure_survival_scale (by norm_num) (by norm_num) (by norm_num)

example : gammaHazard 2 (1 / 3) 1 =
    Real.exp (-(1 / 3)) * (1 / 3 : ℝ) ^ (2 - 1 : ℝ) / (3 * incompleteGamma 2 (1 / 3)) :=
  gammaHazard_scale_eq_incompleteGamma (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (gammaHazard 2 (1 / 3)) atTop (𝓝 (1 / 3)) :=
  gammaHazard_scale_tendsto_inverse (by norm_num) (by norm_num)

#print axioms gammaMeasure_survival_eq_incompleteGamma
#print axioms gammaMeasure_survival_mul_gamma
#print axioms incompleteGamma_pos
#print axioms gammaHazard_eq_incompleteGamma
#print axioms gammaHazard_scale_eq_incompleteGamma
#print axioms gammaHazard_scale_tendsto_inverse

end TailOptionPricing
