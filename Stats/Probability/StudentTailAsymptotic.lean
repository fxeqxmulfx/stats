module

/-
  Actual Student survival power law and regular variation,
  arXiv:1912.00277v2, Section VI. The positive density coefficient
  determines the actual survival coefficient by L'Hopital, using
  independently proved survival calculus. Reflection handles the
  left tail; distinct degrees of freedom give a strict asymptotic
  comparison of genuine probability tails, with no order assumption.
-/
public import Stats.Probability.StudentSurvival
public import Stats.Probability.StudentDensityAsymptotic
public import Stats.Theorem1
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- The actual Student survival coefficient derived below is the
density coefficient divided by the positive tail exponent nu. -/
noncomputable def studentSurvivalTailConstant (ν s : ℝ) : ℝ := studentDensityTailConstant ν s / ν

theorem studentSurvivalTailConstant_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    0 < studentSurvivalTailConstant ν s := div_pos (studentDensityTailConstant_pos hν hs) hν

/-- Actual Student right survival divided by x^(-nu) tends to an
explicit positive finite constant. All nu>0 and scales s>0 are allowed,
including cases with no finite first moment (Section VI). -/
theorem studentMeasure_survival_div_rpow_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (studentMeasure μ ν s).real (Ioi x) / x ^ (-ν))
      atTop (𝓝 (studentSurvivalTailConstant ν s)) := by
  have hd (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y : ℝ => y ^ (-ν)) ((-ν) * x ^ (-ν - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hn (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : (-ν) * x ^ (-ν - 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hν.ne') (Real.rpow_pos_of_pos hx _).ne'
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi
    (fun x _ => studentMeasure_survival_hasDerivAt μ hν hs x) hd hn
    (studentMeasure_survival_tendsto_zero μ hν hs) (tendsto_rpow_neg_atTop hν)
    (studentPDFReal_powerTail_ratio_tendsto μ hν hs)

/-- Equivalent actual survival normalization by the positive power
x^nu. This is the population tail-index statement, not a density proxy. -/
theorem studentMeasure_survival_rpow_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => x ^ ν * (studentMeasure μ ν s).real (Ioi x))
      atTop (𝓝 (studentSurvivalTailConstant ν s)) := by
  apply (studentMeasure_survival_div_rpow_tendsto μ hν hs).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv, inv_inv, mul_comm]

/-- The reflected actual left tail has the same power-law coefficient
and exponent as the right tail (Section VI's two-sided fat tails). -/
theorem studentMeasure_leftTail_div_rpow_tendsto (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (studentMeasure μ ν s).real (Iio (2 * μ - x)) / x ^ (-ν))
      atTop (𝓝 (studentSurvivalTailConstant ν s)) := by
  simpa only [studentMeasure_leftTail_eq_survival] using
    studentMeasure_survival_div_rpow_tendsto μ hν hs

/-- The actual Student survival is regularly varying with index -nu,
using the project's existing definition of the class (Section VI). -/
theorem studentMeasure_survival_regularlyVarying (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    IsRegularlyVarying (fun x => (studentMeasure μ ν s).real (Ioi x)) (-ν) := by
  intro b hb
  have hscale : Tendsto (fun x : ℝ => x * b) atTop atTop := by
    simpa only [id_eq] using tendsto_id.atTop_mul_const hb
  have ht := studentMeasure_survival_rpow_tendsto μ hν hs
  have hc : studentSurvivalTailConstant ν s ≠ 0 := (studentSurvivalTailConstant_pos hν hs).ne'
  have hl := ((ht.comp hscale).div ht hc).mul_const (b ^ (-ν))
  simp only [Function.comp_def, div_self hc, one_mul] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hp : x ^ ν ≠ 0 := (Real.rpow_pos_of_pos hx ν).ne'
  have hbp : b ^ ν ≠ 0 := (Real.rpow_pos_of_pos hb ν).ne'
  have htail : (studentMeasure μ ν s).real (Ioi x) ≠ 0 := (studentMeasure_survival_pos μ hν hs x).ne'
  simp only [Pi.div_apply]
  rw [Real.mul_rpow hx.le hb.le, Real.rpow_neg hb.le]
  field_simp

theorem studentMeasure_leftTail_regularlyVarying (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) :
    IsRegularlyVarying (fun x => (studentMeasure μ ν s).real (Iio (2 * μ - x))) (-ν) := by
  simpa only [studentMeasure_leftTail_eq_survival] using studentMeasure_survival_regularlyVarying μ hν hs

/-- A Student law with larger df has asymptotically negligible right
tail relative to any smaller-df Student law, at arbitrary locations
and positive scales. This makes Section VI's tail comparison precise. -/
theorem studentMeasure_survival_ratio_tendsto_zero (μ₁ μ₂ : ℝ) {ν₁ ν₂ s₁ s₂ : ℝ}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hν : ν₂ < ν₁) :
    Tendsto (fun x => (studentMeasure μ₁ ν₁ s₁).real (Ioi x) /
      (studentMeasure μ₂ ν₂ s₂).real (Ioi x)) atTop (𝓝 0) := by
  have h₁ := studentMeasure_survival_rpow_tendsto μ₁ hν₁ hs₁
  have h₂ := studentMeasure_survival_rpow_tendsto μ₂ hν₂ hs₂
  have hc : studentSurvivalTailConstant ν₂ s₂ ≠ 0 := (studentSurvivalTailConstant_pos hν₂ hs₂).ne'
  have hp : Tendsto (fun x : ℝ => x ^ (ν₂ - ν₁)) atTop (𝓝 0) := by
    have he : ν₂ - ν₁ = -(ν₁ - ν₂) := by ring
    rw [he]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hν)
  have hl := (h₁.div h₂ hc).mul hp
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx₁ : x ^ ν₁ ≠ 0 := (Real.rpow_pos_of_pos hx ν₁).ne'
  have hx₂ : x ^ ν₂ ≠ 0 := (Real.rpow_pos_of_pos hx ν₂).ne'
  have htail : (studentMeasure μ₂ ν₂ s₂).real (Ioi x) ≠ 0 :=
    (studentMeasure_survival_pos μ₂ hν₂ hs₂ x).ne'
  simp only [Pi.div_apply]
  rw [Real.rpow_sub hx]
  field_simp

/-- Smaller Student df eventually gives a strictly larger actual
survival probability, independently of positive scales and locations. -/
theorem eventually_studentMeasure_survival_lt (μ₁ μ₂ : ℝ) {ν₁ ν₂ s₁ s₂ : ℝ}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hν : ν₂ < ν₁) :
    ∀ᶠ x in atTop, (studentMeasure μ₁ ν₁ s₁).real (Ioi x) <
      (studentMeasure μ₂ ν₂ s₂).real (Ioi x) := by
  have h := (studentMeasure_survival_ratio_tendsto_zero μ₁ μ₂ hν₁ hν₂ hs₁ hs₂ hν).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h] with x hx
  exact (div_lt_one (studentMeasure_survival_pos μ₂ hν₂ hs₂ x)).mp hx

example : 0 < studentSurvivalTailConstant (1 / 2) 2 :=
  studentSurvivalTailConstant_pos (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => (studentMeasure 1 (1 / 2) 2).real (Ioi x) / x ^ (-(1 / 2 : ℝ)))
    atTop (𝓝 (studentSurvivalTailConstant (1 / 2) 2)) :=
  studentMeasure_survival_div_rpow_tendsto 1 (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => x ^ (1 / 2 : ℝ) * (studentMeasure 1 (1 / 2) 2).real (Ioi x))
    atTop (𝓝 (studentSurvivalTailConstant (1 / 2) 2)) :=
  studentMeasure_survival_rpow_tendsto 1 (by norm_num) (by norm_num)

example : Tendsto (fun x : ℝ => (studentMeasure 1 4 2).real (Iio (2 * 1 - x)) / x ^ (-4 : ℝ))
    atTop (𝓝 (studentSurvivalTailConstant 4 2)) :=
  studentMeasure_leftTail_div_rpow_tendsto 1 (by norm_num) (by norm_num)

example : IsRegularlyVarying (fun x => (studentMeasure 1 4 2).real (Ioi x)) (-4) :=
  studentMeasure_survival_regularlyVarying 1 (by norm_num) (by norm_num)

example : IsRegularlyVarying (fun x => (studentMeasure 1 4 2).real (Iio (2 * 1 - x))) (-4) :=
  studentMeasure_leftTail_regularlyVarying 1 (by norm_num) (by norm_num)

example : Tendsto (fun x => (studentMeasure 1 4 2).real (Ioi x) /
    (studentMeasure 0 2 3).real (Ioi x)) atTop (𝓝 0) :=
  studentMeasure_survival_ratio_tendsto_zero 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∀ᶠ x in atTop, (studentMeasure 1 4 2).real (Ioi x) < (studentMeasure 0 2 3).real (Ioi x) :=
  eventually_studentMeasure_survival_lt 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms studentMeasure_survival_div_rpow_tendsto
#print axioms studentMeasure_leftTail_div_rpow_tendsto
#print axioms studentMeasure_survival_regularlyVarying
#print axioms studentMeasure_leftTail_regularlyVarying
#print axioms studentMeasure_survival_ratio_tendsto_zero
#print axioms eventually_studentMeasure_survival_lt

end TailOptionPricing
