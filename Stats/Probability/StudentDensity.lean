module

/-
  Conventional location/scale Student density used to check
  arXiv:1912.00277v2, Section VI, Eq. compoundGamma2. The degrees of
  freedom are nu and the standard Student scale is s. Its normalization
  and equality with the actual Gamma precision compound are proved in
  GammaCompoundStudent, independently of this explicit density formula.
  In the conventional coordinates, the centered outcome is divided
  by s and the density coefficient is divided by s. These two roles
  fix which parameter is the Student scale when comparing formulas.
-/
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Conventional Student density with location mu, degrees of freedom
nu and scale s (Section VI). The source's Gamma rate is not this scale. -/
noncomputable def studentPDFReal (μ ν s x : ℝ) : ℝ :=
  Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s) *
    (1 + ((x - μ) / s) ^ 2 / ν) ^ (-((ν + 1) / 2))

/-- Nonnegative-valued version of the conventional Student density.
Properness for positive degrees of freedom and scale is proved from
the actual Normal--Gamma law, not assumed in this definition. -/
noncomputable def studentPDF (μ ν s x : ℝ) : ENNReal := ENNReal.ofReal (studentPDFReal μ ν s x)

/-- Candidate conventional Student law. Its normalization is a theorem
derived from the independently normalized Gamma mixture (Section VI). -/
noncomputable def studentMeasure (μ ν s : ℝ) : Measure ℝ :=
  volume.withDensity (studentPDF μ ν s)

theorem studentPDFReal_measurable (μ ν s : ℝ) : Measurable (studentPDFReal μ ν s) := by
  unfold studentPDFReal
  fun_prop

theorem studentPDF_measurable (μ ν s : ℝ) : Measurable (studentPDF μ ν s) := by
  unfold studentPDF
  exact ENNReal.measurable_ofReal.comp (studentPDFReal_measurable μ ν s)

/-- Positive degrees of freedom and scale give positive density at
every finite outcome, including the location (Section VI). -/
theorem studentPDFReal_pos (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    0 < studentPDFReal μ ν s x := by
  have hg₁ : 0 < Real.Gamma ((ν + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hg₂ : 0 < Real.Gamma (ν / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hb : 0 < 1 + ((x - μ) / s) ^ 2 / ν := by positivity
  unfold studentPDFReal
  exact mul_pos (div_pos hg₁ (mul_pos (mul_pos hg₂ (Real.sqrt_pos.mpr (by positivity))) hs))
    (Real.rpow_pos_of_pos hb _)

theorem studentPDFReal_nonneg (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    0 ≤ studentPDFReal μ ν s x := (studentPDFReal_pos μ hν hs x).le

/-- Positive degrees of freedom make the density continuous on the
whole outcome line; its power base is always strictly positive. -/
theorem studentPDFReal_continuous (μ s : ℝ) {ν : ℝ} (hν : 0 < ν) :
    Continuous (studentPDFReal μ ν s) := by
  unfold studentPDFReal
  have hb : Continuous (fun x : ℝ => 1 + ((x - μ) / s) ^ 2 / ν) := by fun_prop
  exact (hb.rpow_const (fun x => Or.inl (show 0 < 1 + ((x - μ) / s) ^ 2 / ν by positivity).ne')).const_mul _

theorem studentPDF_pos (μ : ℝ) {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    0 < studentPDF μ ν s x := ENNReal.ofReal_pos.mpr (studentPDFReal_pos μ hν hs x)

theorem studentPDF_lt_top (μ ν s x : ℝ) : studentPDF μ ν s x < ⊤ := ENNReal.ofReal_lt_top

/-- The density at its location equals its usual Gamma normalizing
coefficient, before any rate/scale identification (Section VI). -/
theorem studentPDFReal_at_location (μ ν s : ℝ) :
    studentPDFReal μ ν s μ =
      Real.Gamma ((ν + 1) / 2) / (Real.Gamma (ν / 2) * √(ν * Real.pi) * s) := by
  simp only [studentPDFReal, sub_self, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, Real.one_rpow, mul_one]

/-- Changing location and scale acts on the standard density by the
Jacobian 1/s. This identifies the conventional scale parameter. -/
theorem studentPDFReal_location_scale (μ ν s x : ℝ) :
    studentPDFReal μ ν s x = s⁻¹ * studentPDFReal 0 ν 1 ((x - μ) / s) := by
  simp only [studentPDFReal, sub_zero, div_one, mul_one]
  ring

/-- Reflection about the location preserves the conventional Student
density, as required by the symmetric compound model (Section VI). -/
theorem studentPDFReal_reflection (μ ν s x : ℝ) :
    studentPDFReal μ ν s (2 * μ - x) = studentPDFReal μ ν s x := by
  have he : (2 * μ - x - μ) / s = -((x - μ) / s) := by ring
  simp only [studentPDFReal, he, neg_sq]

theorem studentPDF_reflection (μ ν s x : ℝ) :
    studentPDF μ ν s (2 * μ - x) = studentPDF μ ν s x := by
  unfold studentPDF
  rw [studentPDFReal_reflection]

/-- Two distinct conventional scales already give distinct positive
density values at the location. Used to refute Section VI's printed
rate-as-scale claim with degrees of freedom four. -/
theorem studentPDFReal_scale_one_ne_two (μ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    studentPDFReal μ ν 1 μ ≠ studentPDFReal μ ν 2 μ := by
  have hp := studentPDFReal_pos μ hν (show (0 : ℝ) < 1 by norm_num) μ
  have he : studentPDFReal μ ν 2 μ = studentPDFReal μ ν 1 μ / 2 := by
    simp only [studentPDFReal_at_location, mul_one]
    ring
  rw [he]
  linarith

example : Measurable (studentPDFReal 1 4 2) := studentPDFReal_measurable 1 4 2

example : Measurable (studentPDF 1 4 2) := studentPDF_measurable 1 4 2

example (x : ℝ) : 0 < studentPDFReal 1 4 2 x :=
  studentPDFReal_pos 1 (by norm_num) (by norm_num) x

example (x : ℝ) : 0 ≤ studentPDFReal 1 4 2 x :=
  studentPDFReal_nonneg 1 (by norm_num) (by norm_num) x

example : Continuous (studentPDFReal 1 4 2) :=
  studentPDFReal_continuous 1 2 (by norm_num)

example (x : ℝ) : 0 < studentPDF 1 4 2 x := studentPDF_pos 1 (by norm_num) (by norm_num) x

example (x : ℝ) : studentPDF 1 4 2 x < ⊤ := studentPDF_lt_top 1 4 2 x

example : studentPDFReal 1 4 2 1 =
    Real.Gamma (((4 : ℝ) + 1) / 2) / (Real.Gamma (4 / 2) * √(4 * Real.pi) * 2) :=
  studentPDFReal_at_location 1 4 2

example (x : ℝ) : studentPDFReal 1 4 2 x = (2 : ℝ)⁻¹ * studentPDFReal 0 4 1 ((x - 1) / 2) :=
  studentPDFReal_location_scale 1 4 2 x

example (x : ℝ) : studentPDFReal 1 4 2 (2 * 1 - x) = studentPDFReal 1 4 2 x :=
  studentPDFReal_reflection 1 4 2 x

example (x : ℝ) : studentPDF 1 4 2 (2 * 1 - x) = studentPDF 1 4 2 x :=
  studentPDF_reflection 1 4 2 x

example : studentPDFReal 0 4 1 0 ≠ studentPDFReal 0 4 2 0 :=
  studentPDFReal_scale_one_ne_two 0 (by norm_num)

#print axioms studentPDFReal_pos
#print axioms studentPDFReal_continuous
#print axioms studentPDFReal_location_scale
#print axioms studentPDFReal_scale_one_ne_two

end TailOptionPricing
