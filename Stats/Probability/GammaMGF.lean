module

/-
  Actual Gamma exponential moments, arXiv:1912.00277v2, Section VI.
  The source calls Gamma heavy-tailed in the slower-than-exponential
  sense. Every proper Gamma law actually has positive exponential
  moments below its RATE r. Independent Euler-kernel L1 and the
  actual density integral prove this classification and its MGF.
-/
public import Stats.Probability.GammaMoments
public import Mathlib.Probability.Moments.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Weighting the actual real density by exp(t*x) shifts its Euler
kernel's rate from r to r-t, a.e. on positive inputs (Section VI). -/
theorem gammaMeasure_exp_density_ae (a r t : ℝ) :
    (fun x : ℝ => Real.exp (t * x) * gammaPDFReal a r x) =ᵐ[volume]
      (Ioi 0).indicator (fun x => r ^ a / Real.Gamma a *
        (x ^ (a - 1) * Real.exp (-((r - t) * x)))) := by
  have hg := gammaMeasure_rpow_density_ae a r 0
  simp only [Real.rpow_zero, one_mul, add_zero] at hg
  filter_upwards [hg] with x hx
  rw [hx]
  by_cases hp : x ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hp]
    have he : Real.exp (t * x) * Real.exp (-(r * x)) = Real.exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = r ^ a / Real.Gamma a *
          (x ^ (a - 1) * (Real.exp (t * x) * Real.exp (-(r * x)))) := by ring
      _ = _ := by rw [he]
  · simp [hp]

/-- Actual exp(t*X) is L1 for every t below the Gamma rate, independently
of the MGF's value. Positive shape and rate give the source's genuine
proper population; the shifted Euler kernel has rate r-t>0. -/
theorem gammaMeasure_integrable_exp_mul {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  have hrt : 0 < r - t := sub_pos.mpr ht
  have hk : IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-((r - t) * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r - t)
        (by linarith) (by norm_num) hrt)
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr (hk.const_mul (r ^ a / Real.Gamma a))
  have hd : Integrable (fun x : ℝ => Real.exp (t * x) * gammaPDFReal a r x) volume :=
    hi.congr (gammaMeasure_exp_density_ae a r t).symm
  have h := (realDensity_integrableOn_iff (gammaPDFReal a r) (measurable_gammaPDFReal a r)
    (gammaPDFReal_nonneg ha hr) (fun x : ℝ => Real.exp (t * x)) (s := univ) MeasurableSet.univ).mpr
      (by simpa only [IntegrableOn, Measure.restrict_univ] using hd)
  change Integrable (fun x : ℝ => Real.exp (t * x))
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  simpa only [IntegrableOn, Measure.restrict_univ] using h

/-- Actual Gamma exponential-moment integral, with independent L1
proved above. The rate convention gives (r/(r-t))^a (Section VI). -/
theorem gammaMeasure_integral_exp_mul {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    (∫ x : ℝ, Real.exp (t * x) ∂gammaMeasure a r) = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := sub_pos.mpr ht
  have hd := realDensity_setIntegral (gammaPDFReal a r) (measurable_gammaPDFReal a r)
    (gammaPDFReal_nonneg ha hr) (fun x : ℝ => Real.exp (t * x)) univ
  simp only [Measure.restrict_univ] at hd
  change (∫ x : ℝ, Real.exp (t * x)
    ∂volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [hd, integral_congr_ae (gammaMeasure_exp_density_ae a r t),
    integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrt,
    Real.div_rpow hr.le hrt.le a, one_div, Real.inv_rpow hrt.le]
  have hp : (r - t) ^ a ≠ 0 := (Real.rpow_pos_of_pos hrt a).ne'
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

/-- The actual moment-generating function for the source's Gamma
precision law, on its finite interval to the left of rate r. -/
theorem mgf_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    mgf (fun x : ℝ => x) (gammaMeasure a r) t = (r / (r - t)) ^ a :=
  gammaMeasure_integral_exp_mul ha hr ht

/-- An actual exponential upper bound on Gamma survival, derived
from its independently integrable MGF. Every 0<t<r supplies a genuine
exponential tail bound, correcting Section VI's classification. -/
theorem gammaMeasure_survival_le_exp {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht₀ : 0 ≤ t) (ht : t < r) (x : ℝ) :
    (gammaMeasure a r).real (Ioi x) ≤ Real.exp (-t * x) * (r / (r - t)) ^ a := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have h := measure_ge_le_exp_mul_mgf (X := fun y : ℝ => y) (μ := gammaMeasure a r) x ht₀
    (gammaMeasure_integrable_exp_mul ha hr ht)
  change (gammaMeasure a r).real (Ici x) ≤ _ at h
  rw [mgf_gammaMeasure ha hr ht] at h
  exact (measureReal_mono (show Ioi x ⊆ Ici x from fun _ hy => hy.le)).trans h

/-- Every proper Gamma law has a strictly positive exponential moment.
This corrects Section VI's Gamma heavy-tail classification under the
standard criterion of no finite positive exponential moment. -/
theorem gammaMeasure_has_positive_exponential_moment {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  refine ⟨r / 2, by positivity, gammaMeasure_integrable_exp_mul ha hr ?_⟩
  linarith

/-- Formal refutation of the source's Gamma heavy-tail claim, when
“heavy” means no finite positive exponential moment. The correction
holds for every proper positive shape and rate (Section VI). -/
theorem gammaMeasure_not_no_positive_exponential_moment {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ¬(∀ t : ℝ, 0 < t → ¬Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r)) := by
  obtain ⟨t, ht, hi⟩ := gammaMeasure_has_positive_exponential_moment ha hr
  intro h
  exact h t ht hi

/-- A concrete proper Gamma(1,rate=2) law has E[exp(X)]=2, contradicting
the printed no-positive-exponential-moment interpretation (Section VI). -/
theorem gamma_positive_exponential_moment_counterexample :
    IsProbabilityMeasure (gammaMeasure 1 2) ∧
      Integrable (fun x : ℝ => Real.exp x) (gammaMeasure 1 2) ∧
      (∫ x : ℝ, Real.exp x ∂gammaMeasure 1 2) = 2 := by
  refine ⟨isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num), ?_, ?_⟩
  · simpa only [one_mul] using gammaMeasure_integrable_exp_mul
      (a := 1) (r := 2) (t := 1) (by norm_num) (by norm_num) (by norm_num)
  · have h := gammaMeasure_integral_exp_mul
      (a := 1) (r := 2) (t := 1) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact h

example : Integrable (fun x : ℝ => Real.exp (1 * x)) (gammaMeasure 2 3) :=
  gammaMeasure_integrable_exp_mul (by norm_num) (by norm_num) (by norm_num)

example : (∫ x : ℝ, Real.exp (1 * x) ∂gammaMeasure 2 3) = ((3 : ℝ) / (3 - 1)) ^ (2 : ℝ) :=
  gammaMeasure_integral_exp_mul (by norm_num) (by norm_num) (by norm_num)

example : mgf (fun x : ℝ => x) (gammaMeasure 2 3) 1 = ((3 : ℝ) / (3 - 1)) ^ (2 : ℝ) :=
  mgf_gammaMeasure (by norm_num) (by norm_num) (by norm_num)

example : (gammaMeasure 2 3).real (Ioi 4) ≤
    Real.exp (-1 * 4) * ((3 : ℝ) / (3 - 1)) ^ (2 : ℝ) :=
  gammaMeasure_survival_le_exp (a := 2) (r := 3) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4

example : ∃ t : ℝ, 0 < t ∧ Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure 2 3) :=
  gammaMeasure_has_positive_exponential_moment (by norm_num) (by norm_num)

example : ¬(∀ t : ℝ, 0 < t → ¬Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure 2 3)) :=
  gammaMeasure_not_no_positive_exponential_moment (by norm_num) (by norm_num)

#print axioms gammaMeasure_integrable_exp_mul
#print axioms gammaMeasure_integral_exp_mul
#print axioms gammaMeasure_survival_le_exp
#print axioms gammaMeasure_not_no_positive_exponential_moment
#print axioms gamma_positive_exponential_moment_counterexample

end TailOptionPricing
