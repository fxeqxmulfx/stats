module

/-
  Actual Gamma density and survival calculus for the corrected hazard
  limit in arXiv:1912.00277v2, Section VI. The derivative is established
  on the positive domain; density L1 is derived from the Euler kernel
  before differentiating the actual population survival.
-/
public import Stats.Probability.GammaTail
public import Stats.Calculus.CallPrice
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The source's Gamma density on positive inputs as an exponential
log kernel, keeping its rate parametrization (Section VI). -/
theorem gammaPDFReal_eq_exp (a r : ℝ) {x : ℝ} (hx : 0 < x) :
    gammaPDFReal a r x = r ^ a / Real.Gamma a *
      Real.exp ((a - 1) * Real.log x - r * x) := by
  simp only [gammaPDFReal, hx.le, ite_true, Real.rpow_def_of_pos hx,
    Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  rw [mul_comm (Real.log x) (a - 1)]
  ring

/-- The actual Gamma log-density derivative is (a-1)/x-r on the
positive domain. Multiplying it by the actual density gives its
ordinary derivative (Section VI's hazard calculation). -/
theorem gammaPDFReal_hasDerivAt (a r : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaPDFReal a r) (((a - 1) / x - r) * gammaPDFReal a r x) x := by
  have hl : HasDerivAt (fun y : ℝ => r * y) r x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul r
  have hi : HasDerivAt (fun y : ℝ => (a - 1) * Real.log y - r * y)
      ((a - 1) * x⁻¹ - r) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul (a - 1)).fun_sub hl
  have he := hi.exp.const_mul (r ^ a / Real.Gamma a)
  have hloc : gammaPDFReal a r =ᶠ[𝓝 x]
      (fun y : ℝ => r ^ a / Real.Gamma a * Real.exp ((a - 1) * Real.log y - r * y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact gammaPDFReal_eq_exp a r hy
  have h := he.congr_of_eventuallyEq hloc
  convert h using 1
  rw [gammaPDFReal_eq_exp a r hx]
  simp only [div_eq_mul_inv]
  ring

theorem gammaPDFReal_continuousOn_pos (a r : ℝ) : ContinuousOn (gammaPDFReal a r) (Ioi 0) := by
  intro x hx
  exact (gammaPDFReal_hasDerivAt a r hx).continuousAt.continuousWithinAt

/-- Actual density L1 on the positive half-line follows from the
independent Gamma/Euler integral kernel, not from the hazard limit. -/
theorem gammaPDFReal_integrableOn_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (gammaPDFReal a r) (Ioi 0) := by
  have hk : IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
        (by linarith) (by norm_num) hr)
  have hc : IntegrableOn (fun x : ℝ => r ^ a / Real.Gamma a *
      (x ^ (a - 1) * Real.exp (-(r * x)))) (Ioi 0) := hk.const_mul _
  apply hc.congr_fun _ measurableSet_Ioi
  intro x hx
  simp [gammaPDFReal, hx.le, mul_assoc]

/-- Differentiate the actual population survival, using its density
integral, independently established L1 and continuity (Section VI). -/
theorem gammaMeasure_survival_hasDerivAt {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun y => (gammaMeasure a r).real (Ioi y)) (-gammaPDFReal a r x) x := by
  have h := hasDerivAt_integral_Ioi hx (gammaPDFReal_integrableOn_pos ha hr)
    (gammaPDFReal_continuousOn_pos a r)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (gammaMeasure_survival_eq_integral ha hr))

/-- The actual hazard denominator is strictly positive throughout
the positive domain, from the actual density's positive support. -/
theorem gammaMeasure_survival_pos {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    0 < (gammaMeasure a r).real (Ioi x) := by
  have hs : Function.support (gammaPDFReal a r) ∩ Ioi x = Ioi x := by
    apply inter_eq_right.mpr
    intro t ht
    change gammaPDFReal a r t ≠ 0
    exact (gammaPDFReal_pos ha hr (hx.trans ht)).ne'
  rw [gammaMeasure_survival_eq_integral ha hr,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (gammaPDFReal_nonneg ha hr))
      ((gammaPDFReal_integrableOn_pos ha hr).mono_set (Ioi_subset_Ioi hx.le)), hs]
  simp

example : gammaPDFReal 2 3 1 = (3 : ℝ) ^ (2 : ℝ) / Real.Gamma 2 *
    Real.exp (((2 : ℝ) - 1) * Real.log 1 - 3 * 1) :=
  gammaPDFReal_eq_exp _ _ (by norm_num)

example : HasDerivAt (gammaPDFReal 2 3) (((2 - 1) / 1 - 3) * gammaPDFReal 2 3 1) 1 :=
  gammaPDFReal_hasDerivAt _ _ (by norm_num)

example : IntegrableOn (gammaPDFReal 2 3) (Ioi 0) :=
  gammaPDFReal_integrableOn_pos (by norm_num) (by norm_num)

example : HasDerivAt (fun y => (gammaMeasure 2 3).real (Ioi y)) (-gammaPDFReal 2 3 1) 1 :=
  gammaMeasure_survival_hasDerivAt (by norm_num) (by norm_num) (by norm_num)

example : 0 < (gammaMeasure 2 3).real (Ioi 1) :=
  gammaMeasure_survival_pos (by norm_num) (by norm_num) (by norm_num)

#print axioms gammaPDFReal_hasDerivAt
#print axioms gammaMeasure_survival_hasDerivAt
#print axioms gammaMeasure_survival_pos

end TailOptionPricing
