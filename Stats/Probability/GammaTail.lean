module

/-
  Actual Gamma survival and hazard, arXiv:1912.00277v2, Section VI.
  The source's density uses a RATE beta, but its hazard-limit claim
  uses the scale formula 1/beta. Actual unit-shape Gamma laws already
  distinguish these conventions. General-shape calculus follows in
  the modules importing this one.
-/
public import Stats.Probability.GammaMoments
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.CDF

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual Gamma survival is the integral of its proved density,
with positive shape and rate as in Section VI. -/
theorem gammaMeasure_survival_eq_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaMeasure a r).real (Ioi x) = ∫ t : ℝ in Ioi x, gammaPDFReal a r t := by
  have h := realDensity_setIntegral (gammaPDFReal a r) (measurable_gammaPDFReal a r)
    (gammaPDFReal_nonneg ha hr) (fun _ : ℝ => (1 : ℝ)) (Ioi x)
  change (∫ _t : ℝ in Ioi x, (1 : ℝ) ∂gammaMeasure a r) =
    ∫ t : ℝ in Ioi x, 1 * gammaPDFReal a r t at h
  simpa only [setIntegral_const, smul_eq_mul, mul_one, one_mul] using h

/-- Actual Gamma tail probabilities tend to zero, independently of
any claimed density-tail approximation (Section VI). -/
theorem gammaMeasure_survival_tendsto_zero {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun x => (gammaMeasure a r).real (Ioi x)) atTop (𝓝 0) := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have he (x : ℝ) : (gammaMeasure a r).real (Ioi x) = 1 - cdf (gammaMeasure a r) x := by
    rw [cdf_eq_real]
    simpa using (measureReal_compl (μ := gammaMeasure a r) (s := Iic x) measurableSet_Iic)
  simp_rw [he]
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_self] using hc.sub (tendsto_cdf_atTop (gammaMeasure a r))

/-- Unit-shape Gamma has the actual exponential density on its
positive support. This is a density identity, not a new law definition. -/
theorem gammaPDFReal_shape_one (r : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal 1 r x = r * Real.exp (-(r * x)) := by
  simp [gammaPDFReal, hx]

/-- Actual unit-shape Gamma survival, obtained by integrating its
density. It is exactly exponential, with rate r (Section VI). -/
theorem gammaMeasure_shape_one_survival {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    (gammaMeasure 1 r).real (Ioi x) = Real.exp (-(r * x)) := by
  rw [gammaMeasure_survival_eq_integral (by norm_num) hr]
  calc
    _ = ∫ t : ℝ in Ioi x, r * Real.exp ((-r) * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [gammaPDFReal_shape_one r (hx.trans ht.le)]
      simp only [neg_mul]
    _ = r * (-Real.exp ((-r) * x) / (-r)) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hr)]
    _ = _ := by field_simp

/-- Section VI's hazard uses the actual real density divided by the
actual population survival. The second parameter is a rate. -/
noncomputable def gammaHazard (a r x : ℝ) : ℝ :=
  gammaPDFReal a r x / (gammaMeasure a r).real (Ioi x)

/-- The actual unit-shape Gamma hazard is its rate at every
nonnegative threshold (Section VI), already refuting 1/r as the
general rate-parametrized hazard limit. -/
theorem gammaHazard_shape_one {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    gammaHazard 1 r x = r := by
  rw [gammaHazard, gammaPDFReal_shape_one r hx, gammaMeasure_shape_one_survival hr hx]
  exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)

theorem gammaHazard_shape_one_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (gammaHazard 1 r) atTop (𝓝 r) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (gammaHazard_shape_one hr hx).symm

/-- A proper Gamma(1,rate=2) population contradicts Section VI's
printed asymptotic failure rate 1/beta under its own rate convention. -/
theorem gamma_rate_hazard_counterexample :
    ¬Tendsto (gammaHazard 1 2) atTop (𝓝 (1 / 2)) := by
  intro h
  have he := tendsto_nhds_unique (gammaHazard_shape_one_tendsto (r := 2) (by norm_num)) h
  norm_num at he

example : IsProbabilityMeasure (gammaMeasure 1 2) :=
  isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)

example : (gammaMeasure 2 3).real (Ioi 1) = ∫ t : ℝ in Ioi 1, gammaPDFReal 2 3 t :=
  gammaMeasure_survival_eq_integral (by norm_num) (by norm_num) _

example : Tendsto (fun x => (gammaMeasure 2 3).real (Ioi x)) atTop (𝓝 0) :=
  gammaMeasure_survival_tendsto_zero (by norm_num) (by norm_num)

example : gammaPDFReal 1 2 1 = 2 * Real.exp (-(2 * 1)) :=
  gammaPDFReal_shape_one _ (by norm_num)

example : (gammaMeasure 1 2).real (Ioi 1) = Real.exp (-(2 * 1)) :=
  gammaMeasure_shape_one_survival (by norm_num) (by norm_num)

example : gammaHazard 1 2 1 = 2 := gammaHazard_shape_one (by norm_num) (by norm_num)

example : Tendsto (gammaHazard 1 2) atTop (𝓝 2) := gammaHazard_shape_one_tendsto (by norm_num)

#print axioms gammaMeasure_survival_eq_integral
#print axioms gammaHazard_shape_one
#print axioms gamma_rate_hazard_counterexample

end TailOptionPricing
