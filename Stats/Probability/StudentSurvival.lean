module

/-
  Actual Student survival and its calculus, arXiv:1912.00277v2,
  Section VI. Properness and independent density L1 were proved from
  the actual Gamma precision model. This module differentiates actual
  probabilities and proves reflection of actual events, before using
  any proposed power-law tail asymptotic.
-/
public import Stats.EpistemicUncertainty.GammaCompoundStudent
public import Stats.Calculus.CallPrice
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual Student event probability is its real density integral,
with positive degrees of freedom and scale (Section VI). -/
theorem studentMeasure_real_eq_setIntegral (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (A : Set ℝ) :
    (studentMeasure μ ν s).real A = ∫ x in A, studentPDFReal μ ν s x := by
  have h := realDensity_setIntegral (studentPDFReal μ ν s)
    (studentPDFReal_measurable μ ν s) (studentPDFReal_nonneg μ hν hs)
    (fun _ : ℝ => (1 : ℝ)) A
  change (∫ _x in A, (1 : ℝ) ∂studentMeasure μ ν s) =
    ∫ x in A, 1 * studentPDFReal μ ν s x at h
  simpa only [setIntegral_const, smul_eq_mul, mul_one, one_mul] using h

theorem studentMeasure_survival_eq_integral (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    (studentMeasure μ ν s).real (Ioi x) = ∫ t in Ioi x, studentPDFReal μ ν s t :=
  studentMeasure_real_eq_setIntegral μ hν hs _

/-- Differentiate the actual survival probability, using independently
proved real-density L1 and continuity at every finite threshold. -/
theorem studentMeasure_survival_hasDerivAt (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun y => (studentMeasure μ ν s).real (Ioi y))
      (-studentPDFReal μ ν s x) x := by
  have he : (fun y => (studentMeasure μ ν s).real (Ioi y)) =
      (fun y => ∫ t in Ioi y, studentPDFReal μ ν s t) := by
    funext y
    exact studentMeasure_survival_eq_integral μ hν hs y
  rw [he]
  exact hasDerivAt_integral_Ioi (a := x - 1) (by linarith)
    (studentPDFReal_integrable μ hν hs).integrableOn
    (studentPDFReal_continuous μ s hν).continuousOn

/-- The actual survival is continuous everywhere, including all
thresholds in the small-df cases without finite outcome means. -/
theorem studentMeasure_survival_continuous (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Continuous (fun x => (studentMeasure μ ν s).real (Ioi x)) :=
  continuous_iff_continuousAt.mpr (fun x => (studentMeasure_survival_hasDerivAt μ hν hs x).continuousAt)

/-- Every actual Student right survival is strictly positive, at
every threshold, from its everywhere positive integrable density. -/
theorem studentMeasure_survival_pos (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    0 < (studentMeasure μ ν s).real (Ioi x) := by
  have hp : Function.support (studentPDFReal μ ν s) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (studentPDFReal_pos μ hν hs t).ne'
  rw [studentMeasure_survival_eq_integral μ hν hs,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (studentPDFReal_nonneg μ hν hs))
      (studentPDFReal_integrable μ hν hs).integrableOn, hp, univ_inter]
  simp

/-- Actual Student probabilities tend to zero in the right tail by
proper probability normalization, independently of any power law. -/
theorem studentMeasure_survival_tendsto_zero (μ : ℝ) {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x => (studentMeasure μ ν s).real (Ioi x)) atTop (𝓝 0) := by
  let := studentMeasure_probability μ hν hs
  have he (x : ℝ) : (studentMeasure μ ν s).real (Ioi x) = 1 - cdf (studentMeasure μ ν s) x := by
    rw [cdf_eq_real]
    simpa using (measureReal_compl (μ := studentMeasure μ ν s) (s := Iic x) measurableSet_Iic)
  simp_rw [he]
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_self] using hc.sub (tendsto_cdf_atTop (studentMeasure μ ν s))

/-- Reflection about location mu preserves actual Student event
probabilities. This upgrades density symmetry to a whole-law property
by Lebesgue reflection, as required for Section VI's two tails. -/
theorem studentMeasure_reflected_apply (μ ν s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    studentMeasure μ ν s ((fun x => 2 * μ - x) ⁻¹' A) = studentMeasure μ ν s A := by
  have hpre : MeasurableSet ((fun x : ℝ => 2 * μ - x) ⁻¹' A) :=
    hA.preimage (measurable_const.sub measurable_id)
  rw [studentMeasure_apply_density μ ν s hpre, studentMeasure_apply_density μ ν s hA,
    ← lintegral_indicator hpre, ← lintegral_indicator hA]
  calc
    _ = ∫⁻ x : ℝ, A.indicator (studentPDF μ ν s) (2 * μ - x) := by
      apply lintegral_congr
      intro x
      by_cases hx : 2 * μ - x ∈ A
      · rw [indicator_of_mem (show x ∈ (fun y => 2 * μ - y) ⁻¹' A from hx),
          indicator_of_mem hx, studentPDF_reflection]
      · rw [indicator_of_notMem (show x ∉ (fun y => 2 * μ - y) ⁻¹' A from hx),
          indicator_of_notMem hx]
    _ = _ := lintegral_sub_left_eq_self _ (2 * μ)

/-- Section VI's left and right actual Student tails are equal at
reflected thresholds, without identifying probabilities by a density
value at a single point. -/
theorem studentMeasure_leftTail_eq_survival (μ ν s x : ℝ) :
    (studentMeasure μ ν s).real (Iio (2 * μ - x)) = (studentMeasure μ ν s).real (Ioi x) := by
  have he : (fun y : ℝ => 2 * μ - y) ⁻¹' Ioi x = Iio (2 * μ - x) := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  have h := studentMeasure_reflected_apply μ ν s (A := Ioi x) measurableSet_Ioi
  rw [he] at h
  exact congrArg ENNReal.toReal h

example : (studentMeasure 1 4 2).real (Ici 3) = ∫ x in Ici 3, studentPDFReal 1 4 2 x :=
  studentMeasure_real_eq_setIntegral 1 (by norm_num) (by norm_num) _

example (x : ℝ) : (studentMeasure 1 4 2).real (Ioi x) = ∫ t in Ioi x, studentPDFReal 1 4 2 t :=
  studentMeasure_survival_eq_integral 1 (by norm_num) (by norm_num) x

example (x : ℝ) : HasDerivAt (fun y => (studentMeasure 1 4 2).real (Ioi y))
    (-studentPDFReal 1 4 2 x) x := studentMeasure_survival_hasDerivAt 1 (by norm_num) (by norm_num) x

example (x : ℝ) : 0 < (studentMeasure 1 (1 / 2) 2).real (Ioi x) :=
  studentMeasure_survival_pos 1 (by norm_num) (by norm_num) x

example : Continuous (fun x => (studentMeasure 1 (1 / 2) 2).real (Ioi x)) :=
  studentMeasure_survival_continuous 1 (by norm_num) (by norm_num)

example : Tendsto (fun x => (studentMeasure 1 (1 / 2) 2).real (Ioi x)) atTop (𝓝 0) :=
  studentMeasure_survival_tendsto_zero 1 (by norm_num) (by norm_num)

example : studentMeasure 1 4 2 ((fun x : ℝ => 2 * 1 - x) ⁻¹' Ici 3) = studentMeasure 1 4 2 (Ici 3) :=
  studentMeasure_reflected_apply 1 4 2 measurableSet_Ici

example (x : ℝ) : (studentMeasure 1 4 2).real (Iio (2 * 1 - x)) =
    (studentMeasure 1 4 2).real (Ioi x) := studentMeasure_leftTail_eq_survival 1 4 2 x

#print axioms studentMeasure_survival_hasDerivAt
#print axioms studentMeasure_survival_continuous
#print axioms studentMeasure_survival_pos
#print axioms studentMeasure_survival_tendsto_zero
#print axioms studentMeasure_reflected_apply
#print axioms studentMeasure_leftTail_eq_survival

end TailOptionPricing
