module

/-
  Actual Gamma-distribution real-order moments,
  arXiv:1912.00277v2, Section VI. The paper's beta parameter is
  a RATE, as in Mathlib's gammaMeasure. Every moment below has a
  separate L1 proof and requires alpha+p>0. Negative-order moments
  will be needed for Gaussian mixtures with Gamma precision.
-/
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Moments.Variance
public import Stats.Probability.DensityIntegration

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Density-weighted powers have the Gamma integral's kernel a.e.;
the single boundary point zero is Lebesgue-null (Section VI). -/
theorem gammaMeasure_rpow_density_ae (a r p : ℝ) :
    (fun x : ℝ => x ^ p * gammaPDFReal a r x) =ᵐ[volume]
      (Ioi 0).indicator (fun x => r ^ a / Real.Gamma a *
        (x ^ (a + p - 1) * Real.exp (-(r * x)))) := by
  have hz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hz] with x hx₀
  by_cases hx : 0 < x
  · have he : x ^ p * x ^ (a - 1) = x ^ (a + p - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simp only [gammaPDFReal, hx.le, ite_true, indicator_of_mem (show x ∈ Ioi 0 from hx)]
    calc
      _ = r ^ a / Real.Gamma a * ((x ^ p * x ^ (a - 1)) * Real.exp (-(r * x))) := by ring
      _ = _ := by rw [he]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx₀
    simp [gammaPDFReal, not_le.mpr hn, hx]

/-- Actual Gamma moment integrability is proved from its Euler
kernel before evaluating the integral. The source's rate and shape
must be positive, and a negative order p requires a+p>0 (Section VI). -/
theorem gammaMeasure_integrable_rpow {a r p : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hap : 0 < a + p) :
    Integrable (fun x : ℝ => x ^ p) (gammaMeasure a r) := by
  have hk : IntegrableOn (fun x : ℝ => x ^ (a + p - 1) * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := a + p - 1) (b := r) (by linarith) (by norm_num) hr)
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr (hk.const_mul (r ^ a / Real.Gamma a))
  have hd : Integrable (fun x : ℝ => x ^ p * gammaPDFReal a r x) volume :=
    hi.congr (gammaMeasure_rpow_density_ae a r p).symm
  have h := (realDensity_integrableOn_iff (gammaPDFReal a r) (measurable_gammaPDFReal a r)
    (gammaPDFReal_nonneg ha hr) (fun x : ℝ => x ^ p) (s := univ) MeasurableSet.univ).mpr
      (by simpa only [IntegrableOn, Measure.restrict_univ] using hd)
  change Integrable (fun x : ℝ => x ^ p)
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  simpa only [IntegrableOn, Measure.restrict_univ] using h

/-- Actual real-order Gamma moments, including the inverse moments
needed for random precision: E[X^p]=r^(-p)*Gamma(a+p)/Gamma(a),
with r the source's RATE (Section VI). -/
theorem gammaMeasure_moment_rpow {a r p : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hap : 0 < a + p) :
    (∫ x : ℝ, x ^ p ∂gammaMeasure a r) =
      r ^ (-p) * Real.Gamma (a + p) / Real.Gamma a := by
  have hd := realDensity_setIntegral (gammaPDFReal a r) (measurable_gammaPDFReal a r)
    (gammaPDFReal_nonneg ha hr) (fun x : ℝ => x ^ p) univ
  simp only [Measure.restrict_univ] at hd
  change (∫ x : ℝ, x ^ p ∂volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [hd, integral_congr_ae (gammaMeasure_rpow_density_ae a r p),
    integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hap hr]
  have he : r ^ a * (1 / r) ^ (a + p) = r ^ (-p) := by
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = (r ^ a * (1 / r) ^ (a + p)) * Real.Gamma (a + p) / Real.Gamma a := by ring
    _ = _ := by rw [he]

/-- Actual Gamma mean for the Section VI moment match; no desired
mean is supplied as an input property of the distribution. -/
theorem gammaMeasure_mean {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x : ℝ, x ∂gammaMeasure a r) = a / r := by
  have h := gammaMeasure_moment_rpow (p := 1) ha hr (by linarith)
  simp only [Real.rpow_one] at h
  rw [h, Real.rpow_neg_one, Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

/-- Actual second Gamma moment, from the proved real-order integral
and the Gamma recurrence (Section VI's mean/CV matching). -/
theorem gammaMeasure_moment_two {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x : ℝ, x ^ 2 ∂gammaMeasure a r) = a * (a + 1) / r ^ 2 := by
  have h := gammaMeasure_moment_rpow (p := (2 : ℕ)) ha hr (by positivity)
  simp only [Real.rpow_natCast] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hg : Real.Gamma (a + 2) = (a + 1) * a * Real.Gamma a := by
    rw [show a + 2 = (a + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith), Real.Gamma_add_one ha.ne']
    ring
  have hp : r ^ (-(2 : ℝ)) = (r ^ 2)⁻¹ := by
    have ht := Real.rpow_neg hr.le (2 : ℕ)
    simp only [Real.rpow_natCast] at ht
    norm_num only [Nat.cast_ofNat] at ht
    exact ht
  rw [hg, hp]
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

/-- Actual Gamma variance. Its L2 input is derived from the separately
proved real-power L1, not from the desired variance formula (Section VI). -/
theorem gammaMeasure_variance {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance (fun x : ℝ => x) (gammaMeasure a r) = a / r ^ 2 := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have hpow : Integrable (fun x : ℝ => x ^ 2) (gammaMeasure a r) := by
    simpa only [Real.rpow_natCast] using
      gammaMeasure_integrable_rpow (p := (2 : ℕ)) ha hr (by positivity)
  have hl2 : MemLp (fun x : ℝ => x) 2 (gammaMeasure a r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hpow
  rw [variance_eq_sub hl2]
  change (∫ x : ℝ, x ^ 2 ∂gammaMeasure a r) - (∫ x : ℝ, x ∂gammaMeasure a r) ^ 2 = _
  rw [gammaMeasure_moment_two ha hr, gammaMeasure_mean ha hr]
  field_simp
  ring

/-- Section VI's Gamma squared coefficient of variation, as an actual
variance-to-squared-mean ratio. The parameter r is a rate. -/
theorem gammaMeasure_squared_cv {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    variance (fun x : ℝ => x) (gammaMeasure a r) /
      (∫ x : ℝ, x ∂gammaMeasure a r) ^ 2 = 1 / a := by
  rw [gammaMeasure_variance ha hr, gammaMeasure_mean ha hr]
  field_simp

/-- The source's actual Gamma CV equals 1/sqrt(shape), with the
positive mean and rate ensuring the square-root convention (Section VI). -/
theorem gammaMeasure_cv {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    √(variance (fun x : ℝ => x) (gammaMeasure a r)) /
      (∫ x : ℝ, x ∂gammaMeasure a r) = 1 / √a := by
  rw [gammaMeasure_variance ha hr, gammaMeasure_mean ha hr]
  calc
    _ = √a / a := by rw [Real.sqrt_div ha.le, Real.sqrt_sq hr.le]; field_simp
    _ = _ := by
      have hs : √a ≠ 0 := Real.sqrt_ne_zero'.mpr ha
      field_simp
      nlinarith [Real.sq_sqrt ha.le]

example : Integrable (fun x : ℝ => x ^ (-1 : ℝ)) (gammaMeasure 2 3) :=
  gammaMeasure_integrable_rpow (by norm_num) (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ^ (-1 : ℝ) ∂gammaMeasure 2 3) =
    (3 : ℝ) ^ (-(-1 : ℝ)) * Real.Gamma (2 + (-1)) / Real.Gamma 2 :=
  gammaMeasure_moment_rpow (by norm_num) (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ∂gammaMeasure 2 3) = 2 / 3 := gammaMeasure_mean (by norm_num) (by norm_num)

example : (∫ x : ℝ, x ^ 2 ∂gammaMeasure 2 3) = 2 * (2 + 1) / 3 ^ 2 :=
  gammaMeasure_moment_two (by norm_num) (by norm_num)

example : variance (fun x : ℝ => x) (gammaMeasure 2 3) = 2 / 3 ^ 2 :=
  gammaMeasure_variance (by norm_num) (by norm_num)

example : variance (fun x : ℝ => x) (gammaMeasure 2 3) /
    (∫ x : ℝ, x ∂gammaMeasure 2 3) ^ 2 = 1 / 2 :=
  gammaMeasure_squared_cv (by norm_num) (by norm_num)

example : √(variance (fun x : ℝ => x) (gammaMeasure 2 3)) /
    (∫ x : ℝ, x ∂gammaMeasure 2 3) = 1 / √2 :=
  gammaMeasure_cv (by norm_num) (by norm_num)

#print axioms gammaMeasure_integrable_rpow
#print axioms gammaMeasure_moment_rpow
#print axioms gammaMeasure_mean
#print axioms gammaMeasure_variance
#print axioms gammaMeasure_cv

end TailOptionPricing
