module

/-
  Sharp real-order moment domain of the actual Gamma law,
  arXiv:1912.00277v2, Section VI. The inverse precision moments used
  by the compound model fail at and below shape plus order zero.
  Necessity is proved from the genuine density near zero; the
  exponential factor is bounded below there by a positive constant.
  Every natural precision moment lies inside the resulting domain.
  Negative orders can reach its singular endpoint; these are the
  orders needed when precision is converted to outcome dispersion.
-/
public import Stats.Probability.GammaMoments
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter

namespace TailOptionPricing

/-- Actual Gamma real-order moment L1 holds exactly when a+p>0.
The converse is independent of any formal Gamma-ratio value: on (0,1)
the genuine Euler density controls the nonintegrable boundary power.
This supplies the missing inverse-moment restrictions in Section VI.
The coefficient r^a/Gamma(a) is strictly positive. On (0,1),
exp(-r*x)>=exp(-r)>0. Dividing by their product bounds the singular
power by an L1 function. Its necessary exponent condition is
-1<a+p-1, precisely a+p>0. -/
theorem gammaMeasure_integrable_rpow_iff {a r p : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x ^ p) (gammaMeasure a r) ↔ 0 < a + p := by
  refine ⟨?_, gammaMeasure_integrable_rpow ha hr⟩
  intro h
  have hi : IntegrableOn (fun x : ℝ => x ^ p) univ
      (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) := by
    change IntegrableOn (fun x : ℝ => x ^ p) univ (gammaMeasure a r)
    simpa only [IntegrableOn, Measure.restrict_univ] using h
  have hd : Integrable (fun x : ℝ => x ^ p * gammaPDFReal a r x) volume := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (realDensity_integrableOn_iff (gammaPDFReal a r) (measurable_gammaPDFReal a r)
        (gammaPDFReal_nonneg ha hr) (fun x : ℝ => x ^ p) MeasurableSet.univ).mp hi
  have hk : IntegrableOn (fun x : ℝ => r ^ a / Real.Gamma a *
      (x ^ (a + p - 1) * Real.exp (-(r * x)))) (Ioi 0) :=
    (integrable_indicator_iff measurableSet_Ioi).mp
      (hd.congr (gammaMeasure_rpow_density_ae a r p))
  have hsmall := hk.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hx => hx.1)
  let C : ℝ := r ^ a / Real.Gamma a * Real.exp (-r)
  have hc : 0 < C := mul_pos (div_pos (Real.rpow_pos_of_pos hr a)
    (Real.Gamma_pos_of_pos ha)) (Real.exp_pos _)
  have hbound : IntegrableOn (fun x : ℝ => C⁻¹ * (r ^ a / Real.Gamma a *
      (x ^ (a + p - 1) * Real.exp (-(r * x))))) (Ioo 0 1) := hsmall.const_mul C⁻¹
  have hpow : IntegrableOn (fun x : ℝ => x ^ (a + p - 1)) (Ioo 0 1) := by
    apply hbound.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
    have he : Real.exp (-r) ≤ Real.exp (-(r * x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hx.2])
    have hkbound : C * x ^ (a + p - 1) ≤ r ^ a / Real.Gamma a *
        (x ^ (a + p - 1) * Real.exp (-(r * x))) := by
      have he' := mul_le_mul_of_nonneg_left he
        (mul_nonneg (div_pos (Real.rpow_pos_of_pos hr a) (Real.Gamma_pos_of_pos ha)).le
          (Real.rpow_nonneg hxpos.le (a + p - 1)))
      dsimp [C]
      nlinarith only [he']
    calc
      _ = C⁻¹ * (C * x ^ (a + p - 1)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hkbound (inv_nonneg.mpr hc.le)
  have hp := (intervalIntegral.integrableOn_Ioo_rpow_iff (t := 1) (by norm_num)).mp hpow
  linarith

/-- At and below the real-order boundary the actual Gamma power
is not L1, even though a formal ratio of Gamma functions can be written. -/
theorem gammaMeasure_not_integrable_rpow {a r p : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hap : a + p ≤ 0) :
    ¬Integrable (fun x : ℝ => x ^ p) (gammaMeasure a r) := by
  intro h
  exact (not_lt_of_ge hap) ((gammaMeasure_integrable_rpow_iff ha hr).mp h)

/-- Inverse standard-deviation powers needed by Section VI's compound
have the precise prior threshold a>k/2, including equality failure. -/
theorem gammaMeasure_inverse_order_integrable_iff {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ (-(k : ℝ) / 2)) (gammaMeasure a r) ↔ (k : ℝ) / 2 < a := by
  rw [gammaMeasure_integrable_rpow_iff ha hr]
  constructor <;> intro h <;> linarith

/-- The actual mean conditional variance 1/Lambda is finite exactly
for Gamma shape above one; positive rate alone does not suffice. -/
theorem gammaMeasure_integrable_inv_iff {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x⁻¹) (gammaMeasure a r) ↔ 1 < a := by
  have he : (fun x : ℝ => x ^ (-1 : ℝ)) = (fun x : ℝ => x⁻¹) := by
    funext x
    exact Real.rpow_neg_one x
  rw [← he, gammaMeasure_integrable_rpow_iff ha hr]
  constructor <;> intro h <;> linarith

/-- Every natural power is independently L1 under the actual Gamma
population, proving Section VI's finite polynomial-moment claim. -/
theorem gammaMeasure_integrable_pow {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gammaMeasure a r) := by
  simpa only [Real.rpow_natCast] using
    gammaMeasure_integrable_rpow (p := (k : ℝ)) ha hr (by positivity)

/-- Actual natural Gamma moments, throughout their independently
proved L1 domain. Negative orders retain the sharp restriction above. -/
theorem gammaMeasure_moment_pow {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂gammaMeasure a r) =
      r ^ (-(k : ℝ)) * Real.Gamma (a + (k : ℝ)) / Real.Gamma a := by
  simpa only [Real.rpow_natCast] using
    gammaMeasure_moment_rpow (p := (k : ℝ)) ha hr (by positivity)

/-- A proper unit-shape, unit-rate prior already has infinite inverse
moment: a concrete actual-probability witness for the boundary error. -/
theorem gamma_inverse_boundary_counterexample :
    IsProbabilityMeasure (gammaMeasure 1 1) ∧
      ¬Integrable (fun x : ℝ => x⁻¹) (gammaMeasure 1 1) := by
  refine ⟨isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num), ?_⟩
  rw [gammaMeasure_integrable_inv_iff (by norm_num) (by norm_num)]
  norm_num

example : Integrable (fun x : ℝ => x ^ (-1 : ℝ)) (gammaMeasure 2 3) ↔ 0 < (2 : ℝ) + -1 :=
  gammaMeasure_integrable_rpow_iff (by norm_num) (by norm_num)

example : ¬Integrable (fun x : ℝ => x ^ (-2 : ℝ)) (gammaMeasure 2 3) :=
  gammaMeasure_not_integrable_rpow (by norm_num) (by norm_num) (by norm_num)

example : Integrable (fun x : ℝ => x ^ (-(4 : ℝ) / 2)) (gammaMeasure 3 2) ↔ (4 : ℝ) / 2 < 3 :=
  gammaMeasure_inverse_order_integrable_iff (by norm_num) (by norm_num) 4

example : Integrable (fun x : ℝ => x⁻¹) (gammaMeasure 2 3) ↔ (1 : ℝ) < 2 :=
  gammaMeasure_integrable_inv_iff (by norm_num) (by norm_num)

example : Integrable (fun x : ℝ => x ^ 4) (gammaMeasure 2 3) :=
  gammaMeasure_integrable_pow (by norm_num) (by norm_num) 4

example : (∫ x : ℝ, x ^ 4 ∂gammaMeasure 2 3) =
    (3 : ℝ) ^ (-(4 : ℝ)) * Real.Gamma (2 + (4 : ℝ)) / Real.Gamma 2 :=
  gammaMeasure_moment_pow (by norm_num) (by norm_num) 4

#print axioms gammaMeasure_integrable_rpow_iff
#print axioms gammaMeasure_not_integrable_rpow
#print axioms gammaMeasure_inverse_order_integrable_iff
#print axioms gammaMeasure_integrable_inv_iff
#print axioms gammaMeasure_integrable_pow
#print axioms gammaMeasure_moment_pow
#print axioms gamma_inverse_boundary_counterexample

end TailOptionPricing
