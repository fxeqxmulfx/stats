module

/-
  Actual lognormal hazard, arXiv:1912.00277v2, Section VI.
  The proved density and actual survival give the source's erfc
  formula. Gaussian standardization and the proved Mills ratio
  then give the zero hazard limit for every nonzero log variance.
-/
public import Stats.Probability.LognormalDensity
public import Stats.BinaryForecasts.GaussianLaw
public import Stats.BlackScholes.Erfc
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Standardization of the actual Gaussian real density, needed to
relate Section VI's lognormal hazard to the proved Gaussian tail ratio. -/
theorem gaussianPDFReal_eq_standard (m : ℝ) {v : NNReal} (hv : v ≠ 0) (y : ℝ) :
    gaussianPDFReal m v y = gaussianPDFReal 0 1 ((y - m) / √(v : ℝ)) / √(v : ℝ) := by
  have hvp : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : √(v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hvp
  have he : -((y - m) / √(v : ℝ)) ^ 2 / 2 = -(y - m) ^ 2 / (2 * (v : ℝ)) := by
    rw [div_pow, Real.sq_sqrt v.coe_nonneg]
    ring
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), he]
  ring

namespace LognormalMeasure

/-- Actual density-to-survival hazard on the continuous lognormal
domain of Section VI. Its density representation requires v nonzero. -/
noncomputable def lognormalHazard (m : ℝ) (v : NNReal) (x : ℝ) : ℝ :=
  (lognormalPDF m v x).toReal / (lognormalReal m v).real (Ioi x)

/-- On positive inputs, the actual density numerator is the Gaussian
log density divided by the input, including its Jacobian (Section VI). -/
theorem lognormalHazard_eq (m : ℝ) (v : NNReal) {x : ℝ} (hx : 0 < x) :
    lognormalHazard m v x = gaussianPDFReal m v (Real.log x) /
      (x * (lognormalReal m v).real (Ioi x)) := by
  rw [lognormalHazard, lognormalPDF_of_pos m v hx,
    ENNReal.toReal_ofReal (div_nonneg (gaussianPDFReal_nonneg _ _ _) hx.le), div_div]

/-- The whole-law Gaussian log transform gives the actual lognormal
survival as a standard Gaussian upper-tail probability (Section VI). -/
theorem lognormalReal_survival_eq_standard {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    (lognormalReal m v).real (Ioi x) =
      (gaussianReal 0 1).real (Ioi ((Real.log x - m) / √(v : ℝ))) := by
  rw [lognormalReal_real_Ioi hv hx, one_sub_stdNormalCdf]

/-- The actual hazard denominator is positive throughout the
positive continuous domain, rather than a total division by zero. -/
theorem lognormalReal_survival_pos {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (lognormalReal m v).real (Ioi x) := by
  rw [lognormalReal_survival_eq_standard hv hx]
  exact stdNormal_real_Ioi_pos _

/-- Factor the actual hazard into the Gaussian Mills ratio and a log
scaling factor. The log-threshold condition makes the canceled factor
nonzero and holds eventually in Section VI's limit. -/
theorem lognormalHazard_factorization {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) (hlog : m < Real.log x) :
    lognormalHazard m v x =
      (gaussianPDFReal 0 1 ((Real.log x - m) / √(v : ℝ)) /
        (((Real.log x - m) / √(v : ℝ)) *
          (gaussianReal 0 1).real (Ioi ((Real.log x - m) / √(v : ℝ))))) *
        (((Real.log x - m) / √(v : ℝ)) / (√(v : ℝ) * x)) := by
  have hvp : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : √(v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hvp
  have hz : Real.log x - m ≠ 0 := (sub_pos.mpr hlog).ne'
  have ht : (gaussianReal 0 1).real (Ioi ((Real.log x - m) / √(v : ℝ))) ≠ 0 :=
    (stdNormal_real_Ioi_pos _).ne'
  rw [lognormalHazard_eq m v hx, lognormalReal_survival_eq_standard hv hx,
    gaussianPDFReal_eq_standard m hv (Real.log x)]
  field_simp

example : gaussianPDFReal 1 1 2 = gaussianPDFReal 0 1 ((2 - 1) / √(1 : ℝ)) / √(1 : ℝ) := by
  simpa only [NNReal.coe_one] using gaussianPDFReal_eq_standard 1 (v := 1) (by norm_num) 2

example : lognormalHazard 0 1 1 = gaussianPDFReal 0 1 (Real.log 1) /
    (1 * (lognormalReal 0 1).real (Ioi 1)) := lognormalHazard_eq _ _ (by norm_num)

example : (lognormalReal 0 1).real (Ioi 1) =
    (gaussianReal 0 1).real (Ioi ((Real.log 1 - 0) / √(1 : ℝ))) := by
  simpa only [NNReal.coe_one] using
    lognormalReal_survival_eq_standard (m := 0) (v := 1) (x := 1) (by norm_num) (by norm_num)

example : 0 < (lognormalReal 0 1).real (Ioi 1) :=
  lognormalReal_survival_pos (v := 1) (by norm_num) (by norm_num)

example : lognormalHazard 0 1 (Real.exp 1) =
    (gaussianPDFReal 0 1 ((Real.log (Real.exp 1) - 0) / √(1 : ℝ)) /
      (((Real.log (Real.exp 1) - 0) / √(1 : ℝ)) *
        (gaussianReal 0 1).real (Ioi ((Real.log (Real.exp 1) - 0) / √(1 : ℝ))))) *
      (((Real.log (Real.exp 1) - 0) / √(1 : ℝ)) / (√(1 : ℝ) * Real.exp 1)) := by
  simpa only [NNReal.coe_one] using lognormalHazard_factorization (m := 0) (v := 1)
    (x := Real.exp 1) (by norm_num) (Real.exp_pos _) (by simp)

#print axioms lognormalReal_survival_pos
#print axioms lognormalHazard_factorization

private theorem sqrt_hazard_prefactor : √(2 / Real.pi) = 2 / √(2 * Real.pi) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hπ : √Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have h₂ : √(2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Section VI's actual lognormal failure rate, with sigma=sqrt(v).
The erfc denominator is nonzero because actual survival is positive;
v is the positive log variance. -/
theorem lognormalHazard_eq_erfc (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    lognormalHazard m v x =
      √(2 / Real.pi) * Real.exp (-(m - Real.log x) ^ 2 / (2 * (v : ℝ))) /
        (√(v : ℝ) * x * erfc ((Real.log x - m) / (√2 * √(v : ℝ)))) := by
  have hvp : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : √(v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hvp
  have hπ : √(2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have harg : ((Real.log x - m) / √(v : ℝ)) / √2 =
      (Real.log x - m) / (√2 * √(v : ℝ)) := by
    rw [div_div, mul_comm √(v : ℝ) √2]
  have he : erfc ((Real.log x - m) / (√2 * √(v : ℝ))) ≠ 0 := by
    have ht := lognormalReal_survival_pos (m := m) hv hx
    rw [lognormalReal_real_Ioi hv hx, one_sub_stdNormalCdf_eq_half_erfc, harg] at ht
    intro hz
    rw [hz, mul_zero] at ht
    exact lt_irrefl 0 ht
  rw [lognormalHazard_eq m v hx, lognormalReal_real_Ioi hv hx,
    one_sub_stdNormalCdf_eq_half_erfc, harg, gaussianPDFReal,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), sqrt_hazard_prefactor,
    show (m - Real.log x) ^ 2 = (Real.log x - m) ^ 2 by ring]
  field_simp

example : lognormalHazard 0 1 1 =
    √(2 / Real.pi) * Real.exp (-(0 - Real.log 1) ^ 2 / (2 * (1 : ℝ))) /
      (√(1 : ℝ) * 1 * erfc ((Real.log 1 - 0) / (√2 * √(1 : ℝ)))) := by
  simpa only [NNReal.coe_one] using lognormalHazard_eq_erfc 0
    (v := 1) (x := 1) (by norm_num) (by norm_num)

#print axioms lognormalHazard_eq_erfc

/-- Section VI's standardized Gaussian threshold tends to infinity. -/
theorem lognormal_standardized_log_tendsto_atTop (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (fun x : ℝ => (Real.log x - m) / √(v : ℝ)) atTop atTop := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  apply Filter.Tendsto.atTop_div_const hs
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_atTop.mp Real.tendsto_log_atTop) (b + m)] with x hx
  linarith

/-- Section VI's actual hazard scaling factor tends to zero by
log(x)/x and 1/x. -/
theorem lognormal_log_scale_tendsto_zero (m : ℝ) (v : NNReal) :
    Tendsto (fun x : ℝ => ((Real.log x - m) / √(v : ℝ)) / (√(v : ℝ) * x))
      atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).tendsto_div_nhds_zero
  have hm : Tendsto (fun x : ℝ => m / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul m
  have h := ((hl.sub hm).div_const √(v : ℝ)).div_const √(v : ℝ)
  simp only [sub_self, zero_div] at h
  convert h using 1
  funext x
  simp only [div_eq_mul_inv, mul_inv_rev, sub_mul]
  ring

/-- Section VI's actual lognormal hazard tends to zero: the Gaussian
Mills ratio tends to one and its lognormal scaling factor to zero. -/
theorem lognormalHazard_tendsto_zero (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (lognormalHazard m v) atTop (𝓝 0) := by
  have hm : Tendsto (fun z : ℝ => gaussianPDFReal 0 1 z /
      (z * (gaussianReal 0 1).real (Ioi z))) atTop (𝓝 1) := by
    simpa only [stdNormal_tail_mean] using stdNormal_tailMean_ratio_tendsto
  have hz := lognormal_standardized_log_tendsto_atTop m hv
  have h := (hm.comp hz).mul (lognormal_log_scale_tendsto_zero m v)
  simp only [Function.comp_def, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_atTop.mp Real.tendsto_log_atTop) (m + 1)] with x hx hlog
  exact (lognormalHazard_factorization hv hx (by linarith)).symm

example : Tendsto (fun x : ℝ => (Real.log x - 0) / √(1 : ℝ)) atTop atTop := by
  simpa only [NNReal.coe_one] using lognormal_standardized_log_tendsto_atTop 0 (v := 1) (by norm_num)

example : Tendsto (lognormalHazard 0 1) atTop (𝓝 0) :=
  lognormalHazard_tendsto_zero 0 (by norm_num)

#print axioms lognormalHazard_tendsto_zero

end LognormalMeasure
end TailOptionPricing
