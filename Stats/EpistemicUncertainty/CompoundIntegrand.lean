module

/-
  The explicit exponential integrand in arXiv:1912.00277v2,
  Section V, Eq. compound. Positive log-precision standard deviation
  S and positive precision l are explicit. The two independently
  proved probability densities multiply to the source's expression.
-/
public import Stats.EpistemicUncertainty.CompoundDensity

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

open LognormalMeasure

/-- Section V's log-precision Gaussian density with variance S squared,
written in its positive standard deviation S. -/
theorem epistemic_gaussianPDFReal_zero_sq {S : ℝ} (hS : 0 < S) (y : ℝ) :
    gaussianPDFReal 0 (NNReal.mk (S ^ 2) (sq_nonneg S)) y =
      Real.exp (-y ^ 2 / (2 * S ^ 2)) / (√(2 * Real.pi) * S) := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_mk, sub_zero]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    Real.sqrt_sq_eq_abs, abs_of_pos hS]
  ring

/-- The source's conditional precision-parametrized Gaussian density,
derived from the actual Gaussian variance 1/l (Section V, Eq. precnorm). -/
theorem epistemic_gaussianPDFReal_precision {l : ℝ} (hl : 0 < l) (x : ℝ) :
    gaussianPDFReal 0 (l⁻¹).toNNReal x =
      √l * Real.exp (-l * x ^ 2 / 2) / √(2 * Real.pi) := by
  unfold gaussianPDFReal
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hl.le)]
  simp only [sub_zero]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.sqrt_inv]
  have he : -x ^ 2 / (2 * l⁻¹) = -l * x ^ 2 / 2 := by field_simp
  rw [he]
  have hp : √(2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hs : √l ≠ 0 := Real.sqrt_ne_zero'.mpr hl
  field_simp

/-- The literal product of the actual lognormal precision density and
conditional Gaussian density is the single exponential integrand in
Section V, Eq. compound. Both positive-parameter conditions are explicit. -/
theorem epistemic_compound_density_product {S l : ℝ} (hS : 0 < S) (hl : 0 < l) (x : ℝ) :
    lognormalPDF 0 (NNReal.mk (S ^ 2) (sq_nonneg S)) l *
      gaussianPDF 0 (l⁻¹).toNNReal x =
        ENNReal.ofReal (Real.exp (-((Real.log l) ^ 2 + l * S ^ 2 * x ^ 2) / (2 * S ^ 2)) /
          (2 * Real.pi * √l * S)) := by
  rw [lognormalPDF_of_pos _ _ hl, gaussianPDF,
    ← ENNReal.ofReal_mul (div_nonneg (gaussianPDFReal_nonneg _ _ _) hl.le)]
  congr 1
  rw [epistemic_gaussianPDFReal_zero_sq hS, epistemic_gaussianPDFReal_precision hl]
  have he : Real.exp (-(Real.log l) ^ 2 / (2 * S ^ 2)) * Real.exp (-l * x ^ 2 / 2) =
      Real.exp (-((Real.log l) ^ 2 + l * S ^ 2 * x ^ 2) / (2 * S ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [← he]
  have hp : √(2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hs : √l ≠ 0 := Real.sqrt_ne_zero'.mpr hl
  field_simp
  ring_nf
  rw [Real.sq_sqrt hl.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi * 2)]
  ring

/-- Section V, Eq. compound, now the explicit exponential density of
the actual independently constructed Normal–Lognormal probability law. -/
theorem epistemicNormalLognormalDensity_eq_exp_integral {S : ℝ} (hS : 0 < S) (x : ℝ) :
    epistemicNormalLognormalDensity 0 0 (NNReal.mk (S ^ 2) (sq_nonneg S)) x =
      ∫⁻ l : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-((Real.log l) ^ 2 + l * S ^ 2 * x ^ 2) / (2 * S ^ 2)) /
          (2 * Real.pi * √l * S)) := by
  have hv : NNReal.mk (S ^ 2) (sq_nonneg S) ≠ 0 := by
    intro h
    have hz := congrArg (fun v : NNReal => (v : ℝ)) h
    change S ^ 2 = 0 at hz
    exact (sq_pos_of_pos hS).ne' hz
  rw [epistemicNormalLognormalDensity_eq_lintegral _ _ hv]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  exact epistemic_compound_density_product hS hl x

example (y : ℝ) : gaussianPDFReal 0 (NNReal.mk ((1 : ℝ) ^ 2) (by positivity)) y =
    Real.exp (-y ^ 2 / (2 * (1 : ℝ) ^ 2)) / (√(2 * Real.pi) * 1) :=
  epistemic_gaussianPDFReal_zero_sq (by norm_num) _

example (x : ℝ) : gaussianPDFReal 0 ((2 : ℝ)⁻¹).toNNReal x =
    √2 * Real.exp (-2 * x ^ 2 / 2) / √(2 * Real.pi) :=
  epistemic_gaussianPDFReal_precision (by norm_num) _

example (x : ℝ) : lognormalPDF 0 (NNReal.mk ((1 : ℝ) ^ 2) (by positivity)) 2 *
    gaussianPDF 0 ((2 : ℝ)⁻¹).toNNReal x = ENNReal.ofReal
      (Real.exp (-((Real.log 2) ^ 2 + 2 * (1 : ℝ) ^ 2 * x ^ 2) / (2 * (1 : ℝ) ^ 2)) /
        (2 * Real.pi * √2 * 1)) := epistemic_compound_density_product (by norm_num) (by norm_num) _

example (x : ℝ) :
    epistemicNormalLognormalDensity 0 0 (NNReal.mk ((1 : ℝ) ^ 2) (by positivity)) x =
      ∫⁻ l : ℝ in Ioi 0, ENNReal.ofReal
        (Real.exp (-((Real.log l) ^ 2 + l * (1 : ℝ) ^ 2 * x ^ 2) / (2 * (1 : ℝ) ^ 2)) /
          (2 * Real.pi * √l * 1)) :=
  epistemicNormalLognormalDensity_eq_exp_integral (by norm_num) _

#print axioms epistemic_compound_density_product
#print axioms epistemicNormalLognormalDensity_eq_exp_integral

end TailOptionPricing
