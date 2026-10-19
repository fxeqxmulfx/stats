module

/-
  Evaluate the actual Normal--Gamma density, arXiv:1912.00277v2,
  Section VI, Eqs. compoundGamma and compoundGamma2. The real Euler
  kernel is independently L1 before passing from its nonnegative
  integral to the evaluated real integral. Shape and RATE are positive;
  no finite outcome-moment hypothesis is needed for the density.
-/
public import Stats.EpistemicUncertainty.GammaCompoundDensity
public import Stats.EpistemicUncertainty.CompoundIntegrand

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- The actual conditional Gaussian density with general location,
written in positive precision, as used in Section VI's compound. -/
theorem epistemic_gaussianPDFReal_precision_location (μ : ℝ) {l : ℝ}
    (hl : 0 < l) (x : ℝ) : gaussianPDFReal μ (l⁻¹).toNNReal x =
      √l * Real.exp (-l * (x - μ) ^ 2 / 2) / √(2 * Real.pi) := by
  have he : gaussianPDFReal μ (l⁻¹).toNNReal x =
      gaussianPDFReal 0 (l⁻¹).toNNReal (x - μ) := by
    simp only [gaussianPDFReal, sub_zero]
  rw [he, epistemic_gaussianPDFReal_precision hl]

/-- The product of actual precision and conditional outcome densities
is the source's single Euler kernel (Eq. compoundGamma). -/
theorem epistemic_gamma_compound_density_product {a r l : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hl : 0 < l) (μ x : ℝ) :
    gammaPDF a r l * gaussianPDF μ (l⁻¹).toNNReal x = ENNReal.ofReal
      (r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
        (l ^ (a + 1 / 2 - 1) * Real.exp (-((r + (x - μ) ^ 2 / 2) * l)))) := by
  rw [gammaPDF, gaussianPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr l)]
  congr 1
  rw [epistemic_gaussianPDFReal_precision_location μ hl]
  simp only [gammaPDFReal, hl.le, ite_true]
  have hp : l ^ (a - 1) * √l = l ^ (a + 1 / 2 - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl]
    congr 1
    ring
  have he : Real.exp (-(r * l)) * Real.exp (-l * (x - μ) ^ 2 / 2) =
      Real.exp (-((r + (x - μ) ^ 2 / 2) * l)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
        ((l ^ (a - 1) * √l) *
          (Real.exp (-(r * l)) * Real.exp (-l * (x - μ) ^ 2 / 2))) := by ring
    _ = _ := by rw [hp, he]

/-- Independent L1 of the exact compound Euler kernel, before its
value is evaluated. Its shape is a+1/2 and rate r+(x-mu)^2/2. -/
theorem epistemic_gamma_compound_kernel_integrable (μ x : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) : IntegrableOn (fun l : ℝ =>
      r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
        (l ^ (a + 1 / 2 - 1) * Real.exp (-((r + (x - μ) ^ 2 / 2) * l)))) (Ioi 0) := by
  have hk : IntegrableOn (fun l : ℝ => l ^ (a + 1 / 2 - 1) *
      Real.exp (-((r + (x - μ) ^ 2 / 2) * l))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := a + 1 / 2 - 1) (b := r + (x - μ) ^ 2 / 2)
        (by linarith) (by norm_num) (by positivity))
  exact hk.const_mul _

/-- Evaluate Eq. compoundGamma's independently integrable Euler
kernel, obtaining the literal first line of Eq. compoundGamma2. -/
theorem epistemic_gamma_compound_kernel_integral (μ x : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    (∫ l : ℝ in Ioi 0, r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
      (l ^ (a + 1 / 2 - 1) * Real.exp (-((r + (x - μ) ^ 2 / 2) * l)))) =
      r ^ a / (Real.Gamma a * √(2 * Real.pi)) * Real.Gamma (a + 1 / 2) /
        (r + (x - μ) ^ 2 / 2) ^ (a + 1 / 2) := by
  have hb : 0 < r + (x - μ) ^ 2 / 2 := by positivity
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb,
    one_div, Real.inv_rpow hb.le]
  ring

/-- The closed formula is the actual normalized compound density,
not merely a candidate integral. All positive shapes are allowed
(Section VI, Eq. compoundGamma2, with r a rate). -/
theorem epistemicNormalGammaDensity_eq_closed (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    epistemicNormalGammaDensity μ a r x = ENNReal.ofReal
      (r ^ a / (Real.Gamma a * √(2 * Real.pi)) * Real.Gamma (a + 1 / 2) /
        (r + (x - μ) ^ 2 / 2) ^ (a + 1 / 2)) := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  rw [epistemicNormalGammaDensity_eq_lintegral]
  calc
    _ = ∫⁻ l : ℝ in Ioi 0, ENNReal.ofReal
        (r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
          (l ^ (a + 1 / 2 - 1) * Real.exp (-((r + (x - μ) ^ 2 / 2) * l)))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      exact epistemic_gamma_compound_density_product ha hr hl μ x
    _ = ENNReal.ofReal (∫ l : ℝ in Ioi 0,
        r ^ a / (Real.Gamma a * √(2 * Real.pi)) *
          (l ^ (a + 1 / 2 - 1) * Real.exp (-((r + (x - μ) ^ 2 / 2) * l)))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (epistemic_gamma_compound_kernel_integrable μ x ha hr)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
      have hlpos : 0 < l := hl
      exact mul_nonneg (div_nonneg (Real.rpow_nonneg hr.le _)
        (mul_nonneg hΓ.le (Real.sqrt_nonneg _)))
        (mul_nonneg (Real.rpow_nonneg hlpos.le _) (Real.exp_pos _).le)
    _ = _ := by rw [epistemic_gamma_compound_kernel_integral μ x ha hr]

/-- Equality of actual probability measures with the evaluated
closed density, retaining the source rate convention (Section VI). -/
theorem epistemicNormalGammaLaw_eq_closed_density (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    epistemicNormalGammaLaw μ a r = volume.withDensity (fun x => ENNReal.ofReal
      (r ^ a / (Real.Gamma a * √(2 * Real.pi)) * Real.Gamma (a + 1 / 2) /
        (r + (x - μ) ^ 2 / 2) ^ (a + 1 / 2))) := by
  rw [epistemicNormalGammaLaw_eq_withDensity μ ha hr]
  congr 1
  funext x
  exact epistemicNormalGammaDensity_eq_closed μ ha hr x

/-- In particular the actual compound density is finite at every
outcome, strengthening a.e. finiteness without any moment assumption. -/
theorem epistemicNormalGammaDensity_lt_top (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) : epistemicNormalGammaDensity μ a r x < ⊤ := by
  rw [epistemicNormalGammaDensity_eq_closed μ ha hr]
  exact ENNReal.ofReal_lt_top

example (x : ℝ) : gaussianPDFReal 1 ((2 : ℝ)⁻¹).toNNReal x =
    √2 * Real.exp (-2 * (x - 1) ^ 2 / 2) / √(2 * Real.pi) :=
  epistemic_gaussianPDFReal_precision_location 1 (by norm_num) x

example (x : ℝ) : gammaPDF 3 2 1 * gaussianPDF 1 ((1 : ℝ)⁻¹).toNNReal x = ENNReal.ofReal
    ((2 : ℝ) ^ (3 : ℝ) / (Real.Gamma 3 * √(2 * Real.pi)) *
      ((1 : ℝ) ^ (3 + 1 / 2 - 1 : ℝ) * Real.exp (-((2 + (x - 1) ^ 2 / 2) * 1)))) :=
  epistemic_gamma_compound_density_product (by norm_num) (by norm_num) (by norm_num) 1 x

example (x : ℝ) : IntegrableOn (fun l : ℝ =>
    (2 : ℝ) ^ (3 : ℝ) / (Real.Gamma 3 * √(2 * Real.pi)) *
      (l ^ (3 + 1 / 2 - 1 : ℝ) * Real.exp (-((2 + (x - 1) ^ 2 / 2) * l)))) (Ioi 0) :=
  epistemic_gamma_compound_kernel_integrable 1 x (by norm_num) (by norm_num)

example (x : ℝ) : (∫ l : ℝ in Ioi 0,
    (2 : ℝ) ^ (3 : ℝ) / (Real.Gamma 3 * √(2 * Real.pi)) *
      (l ^ (3 + 1 / 2 - 1 : ℝ) * Real.exp (-((2 + (x - 1) ^ 2 / 2) * l)))) =
    (2 : ℝ) ^ (3 : ℝ) / (Real.Gamma 3 * √(2 * Real.pi)) * Real.Gamma (3 + 1 / 2) /
      (2 + (x - 1) ^ 2 / 2) ^ (3 + 1 / 2 : ℝ) :=
  epistemic_gamma_compound_kernel_integral 1 x (by norm_num) (by norm_num)

example (x : ℝ) : epistemicNormalGammaDensity 0 (1 / 4) 2 x = ENNReal.ofReal
    ((2 : ℝ) ^ (1 / 4 : ℝ) / (Real.Gamma (1 / 4) * √(2 * Real.pi)) * Real.Gamma (1 / 4 + 1 / 2) /
      (2 + (x - 0) ^ 2 / 2) ^ (1 / 4 + 1 / 2 : ℝ)) :=
  epistemicNormalGammaDensity_eq_closed 0 (by norm_num) (by norm_num) x

example : epistemicNormalGammaLaw 0 (1 / 4) 2 = volume.withDensity (fun x => ENNReal.ofReal
    ((2 : ℝ) ^ (1 / 4 : ℝ) / (Real.Gamma (1 / 4) * √(2 * Real.pi)) * Real.Gamma (1 / 4 + 1 / 2) /
      (2 + (x - 0) ^ 2 / 2) ^ (1 / 4 + 1 / 2 : ℝ))) :=
  epistemicNormalGammaLaw_eq_closed_density 0 (by norm_num) (by norm_num)

example (x : ℝ) : epistemicNormalGammaDensity 0 (1 / 4) 2 x < ⊤ :=
  epistemicNormalGammaDensity_lt_top 0 (by norm_num) (by norm_num) x

#print axioms epistemic_gamma_compound_density_product
#print axioms epistemic_gamma_compound_kernel_integrable
#print axioms epistemic_gamma_compound_kernel_integral
#print axioms epistemicNormalGammaDensity_eq_closed
#print axioms epistemicNormalGammaLaw_eq_closed_density

end TailOptionPricing
