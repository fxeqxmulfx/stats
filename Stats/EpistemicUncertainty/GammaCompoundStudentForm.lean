module

/-
  Student form of the actual Normal--Gamma density,
  arXiv:1912.00277v2, Section VI, Eq. compoundGamma2. The second
  displayed formula uses the Gamma RATE in its denominator. In the
  conventional Student parametrization, degrees of freedom are 2*a
  and SCALE is sqrt(r/a). Each algebraic change is proved below.
-/
public import Stats.EpistemicUncertainty.GammaCompoundIntegral
public import Stats.Probability.StudentDensity

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Factoring the positive Gamma rate out of the evaluated density
gives the second line of Eq. compoundGamma2, taking its b to mean r.
This is a rate formula, before converting to conventional Student scale. -/
theorem epistemic_gamma_closed_eq_rate_form (μ x : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    r ^ a / (Real.Gamma a * √(2 * Real.pi)) * Real.Gamma (a + 1 / 2) /
      (r + (x - μ) ^ 2 / 2) ^ (a + 1 / 2) =
    Real.Gamma (a + 1 / 2) / (Real.Gamma a * √(2 * Real.pi * r)) *
      (1 + (x - μ) ^ 2 / (2 * r)) ^ (-(a + 1 / 2)) := by
  let u : ℝ := 1 + (x - μ) ^ 2 / (2 * r)
  have hu : 0 < u := by dsimp [u]; positivity
  have hb : r + (x - μ) ^ 2 / 2 = r * u := by dsimp [u]; field_simp
  have hp : r ^ (a + 1 / 2) = r ^ a * √r := by
    rw [Real.rpow_add hr, ← Real.sqrt_eq_rpow]
  have hs : √(2 * Real.pi * r) = √(2 * Real.pi) * √r :=
    Real.sqrt_mul (by positivity) r
  rw [hb, Real.mul_rpow hr.le hu.le, hp, hs, Real.rpow_neg hu.le]
  have hg : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hrp : r ^ a ≠ 0 := (Real.rpow_pos_of_pos hr a).ne'
  have hup : u ^ (a + 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  have hsr : √r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hsp : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- The conventional Student parameters df=2*a and scale=sqrt(r/a)
give exactly the rate-form kernel of Eq. compoundGamma2. The source
instead calls r the scale; this explicit substitution corrects it. -/
theorem studentPDFReal_gamma_parameters (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    studentPDFReal μ (2 * a) √(r / a) x =
      Real.Gamma (a + 1 / 2) / (Real.Gamma a * √(2 * Real.pi * r)) *
        (1 + (x - μ) ^ 2 / (2 * r)) ^ (-(a + 1 / 2)) := by
  have hn : (2 * a + 1) / 2 = a + 1 / 2 := by ring
  have ha₂ : 2 * a / 2 = a := by ring
  have hs : √(2 * a * Real.pi) * √(r / a) = √(2 * Real.pi * r) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * a * Real.pi)]
    congr 1
    field_simp
  have hb : 1 + ((x - μ) / √(r / a)) ^ 2 / (2 * a) =
      1 + (x - μ) ^ 2 / (2 * r) := by
    rw [div_pow, Real.sq_sqrt (div_nonneg hr.le ha.le)]
    field_simp
  unfold studentPDFReal
  rw [hn, ha₂, hb, mul_assoc, hs]

/-- The actual compound density has the source's second closed form,
with the Gamma rate consistently used in the coefficient and power. -/
theorem epistemicNormalGammaDensity_eq_rate_form (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    epistemicNormalGammaDensity μ a r x = ENNReal.ofReal
      (Real.Gamma (a + 1 / 2) / (Real.Gamma a * √(2 * Real.pi * r)) *
        (1 + (x - μ) ^ 2 / (2 * r)) ^ (-(a + 1 / 2))) := by
  rw [epistemicNormalGammaDensity_eq_closed μ ha hr,
    epistemic_gamma_closed_eq_rate_form μ x ha hr]

/-- Actual Normal--Gamma density equals the conventional Student
density with df 2*a and scale sqrt(r/a), for every positive shape
and rate. The compound was normalized independently (Section VI). -/
theorem epistemicNormalGammaDensity_eq_studentPDF (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    epistemicNormalGammaDensity μ a r x = studentPDF μ (2 * a) √(r / a) x := by
  rw [epistemicNormalGammaDensity_eq_rate_form μ ha hr, studentPDF,
    studentPDFReal_gamma_parameters μ ha hr]

/-- The actual compound density is strictly positive at every finite
outcome for all proper Gamma shapes and rates (Section VI). -/
theorem epistemicNormalGammaDensity_pos (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (x : ℝ) : 0 < epistemicNormalGammaDensity μ a r x := by
  rw [epistemicNormalGammaDensity_eq_studentPDF μ ha hr]
  exact studentPDF_pos μ (by positivity) (Real.sqrt_pos.mpr (div_pos hr ha)) x

/-- Equality of whole probability measures with the correctly scaled
conventional Student law, not merely equality of formal kernels.
The source's claim of scale r is corrected to sqrt(r/a). -/
theorem epistemicNormalGammaLaw_eq_studentMeasure (μ : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    epistemicNormalGammaLaw μ a r = studentMeasure μ (2 * a) √(r / a) := by
  rw [epistemicNormalGammaLaw_eq_withDensity μ ha hr, studentMeasure]
  congr 1
  funext x
  exact epistemicNormalGammaDensity_eq_studentPDF μ ha hr x

/-- A proper shape-two, rate-two population has Student scale one.
Its actual density at zero differs from the conventional scale-two
density, refuting Section VI's printed rate-as-scale density claim. -/
theorem epistemic_gamma_student_scale_counterexample :
    IsProbabilityMeasure (epistemicNormalGammaLaw 0 2 2) ∧
      (epistemicNormalGammaDensity 0 2 2 0).toReal ≠ studentPDFReal 0 4 2 0 := by
  refine ⟨epistemicNormalGammaLaw_probability 0 (by norm_num) (by norm_num), ?_⟩
  have h := epistemicNormalGammaDensity_eq_studentPDF 0
    (a := 2) (r := 2) (by norm_num) (by norm_num) 0
  norm_num at h
  rw [h, studentPDF, ENNReal.toReal_ofReal (studentPDFReal_nonneg 0 (by norm_num) (by norm_num) 0)]
  exact studentPDFReal_scale_one_ne_two 0 (by norm_num)

example (x : ℝ) :
    (2 : ℝ) ^ (3 : ℝ) / (Real.Gamma 3 * √(2 * Real.pi)) * Real.Gamma (3 + 1 / 2) /
      (2 + (x - 1) ^ 2 / 2) ^ (3 + 1 / 2 : ℝ) =
    Real.Gamma (3 + 1 / 2) / (Real.Gamma 3 * √(2 * Real.pi * 2)) *
      (1 + (x - 1) ^ 2 / (2 * 2)) ^ (-(3 + 1 / 2 : ℝ)) :=
  epistemic_gamma_closed_eq_rate_form 1 x (by norm_num) (by norm_num)

example (x : ℝ) : studentPDFReal 1 (2 * 3) √((2 : ℝ) / 3) x =
    Real.Gamma (3 + 1 / 2) / (Real.Gamma 3 * √(2 * Real.pi * 2)) *
      (1 + (x - 1) ^ 2 / (2 * 2)) ^ (-(3 + 1 / 2 : ℝ)) :=
  studentPDFReal_gamma_parameters 1 (by norm_num) (by norm_num) x

example (x : ℝ) : epistemicNormalGammaDensity 1 3 2 x = ENNReal.ofReal
    (Real.Gamma (3 + 1 / 2) / (Real.Gamma 3 * √(2 * Real.pi * 2)) *
      (1 + (x - 1) ^ 2 / (2 * 2)) ^ (-(3 + 1 / 2 : ℝ))) :=
  epistemicNormalGammaDensity_eq_rate_form 1 (by norm_num) (by norm_num) x

example (x : ℝ) : epistemicNormalGammaDensity 0 (1 / 4) 2 x =
    studentPDF 0 (2 * (1 / 4)) √((2 : ℝ) / (1 / 4)) x :=
  epistemicNormalGammaDensity_eq_studentPDF 0 (by norm_num) (by norm_num) x

example (x : ℝ) : 0 < epistemicNormalGammaDensity 0 (1 / 4) 2 x :=
  epistemicNormalGammaDensity_pos 0 (by norm_num) (by norm_num) x

example : epistemicNormalGammaLaw 0 (1 / 4) 2 =
    studentMeasure 0 (2 * (1 / 4)) √((2 : ℝ) / (1 / 4)) :=
  epistemicNormalGammaLaw_eq_studentMeasure 0 (by norm_num) (by norm_num)

#print axioms epistemic_gamma_closed_eq_rate_form
#print axioms studentPDFReal_gamma_parameters
#print axioms epistemicNormalGammaDensity_eq_rate_form
#print axioms epistemicNormalGammaDensity_eq_studentPDF
#print axioms epistemicNormalGammaDensity_pos
#print axioms epistemicNormalGammaLaw_eq_studentMeasure
#print axioms epistemic_gamma_student_scale_counterexample

end TailOptionPricing
