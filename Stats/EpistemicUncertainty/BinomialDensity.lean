module

/-
  Actual finite constant-error Gaussian density, arXiv:1912.00277v2,
  Section III. Positive component scales connect the already constructed
  probability population to the printed normalized binomial density.
-/
public import Stats.EpistemicUncertainty.BinomialCollapse

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

private theorem binomial_withDensity_sum (s : Finset ℕ) (f : ℕ → ℝ → ENNReal)
    (hf : ∀ j, Measurable (f j)) :
    volume.withDensity (fun x => ∑ j ∈ s, f j x) =
      ∑ j ∈ s, volume.withDensity (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    simp only [sum_insert hj]
    change volume.withDensity (f j + (fun x => ∑ k ∈ s, f k x)) = _
    rw [withDensity_add_left (hf j), ih]

/-- Every standard deviation in Section III's binomial mixture is
positive on the source domain, including the two endpoint branches. -/
theorem epistemicBinomialScale_pos (n j : ℕ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    0 < σ * (1 + ε) ^ j * (1 - ε) ^ (n - j) :=
  mul_pos (mul_pos hσ (pow_pos (by linarith) _)) (pow_pos (by linarith) _)

/-- The real-valued density printed in Section III, with binomial
probability choose(n,j)/2^n and the actual component variances. Its
identification with the independently constructed law is proved below. -/
noncomputable def epistemicBinomialDensity (n : ℕ) (μ σ ε x : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) *
    gaussianPDFReal μ
      (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2) (sq_nonneg _)) x

/-- Nonnegativity of Section III's finite binomial Gaussian expression. -/
theorem epistemicBinomialDensity_nonneg (n : ℕ) (μ σ ε x : ℝ) :
    0 ≤ epistemicBinomialDensity n μ σ ε x := by
  apply sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)

/-- Measurability of the source's finite Gaussian density (Section III). -/
theorem epistemicBinomialDensity_measurable (n : ℕ) (μ σ ε : ℝ) :
    Measurable (epistemicBinomialDensity n μ σ ε) :=
  Finset.measurable_sum _ (fun _ _ => measurable_const.mul (measurable_gaussianPDFReal _ _))

/-- L1 of the density follows from each genuine Gaussian component,
independently of its normalization or its law identification (Section III). -/
theorem epistemicBinomialDensity_integrable (n : ℕ) (μ σ ε : ℝ) :
    Integrable (epistemicBinomialDensity n μ σ ε) := by
  apply integrable_finsetSum
  intro j hj
  exact (integrable_gaussianPDFReal _ _).const_mul _

/-- The actual recursively generated population has exactly Section
III's binomial density on sigma>0, 0<=epsilon<1. Positivity excludes
the zero-variance Gaussian atoms for which a Lebesgue density fails. -/
theorem epistemicBranchLaw_eq_withDensity (n : ℕ) (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    epistemicBranchLaw n μ σ ε =
      volume.withDensity (fun x => ENNReal.ofReal (epistemicBinomialDensity n μ σ ε x)) := by
  have hp : (fun x => ENNReal.ofReal (epistemicBinomialDensity n μ σ ε x)) =
      (fun x => ∑ j ∈ range (n + 1), ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
        (n.choose j : ℝ)) * gaussianPDF μ
          (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2) (sq_nonneg _)) x) := by
    funext x
    unfold epistemicBinomialDensity
    rw [ENNReal.ofReal_sum_of_nonneg (by
      intro j hj
      exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _))]
    apply sum_congr rfl
    intro j hj
    exact ENNReal.ofReal_mul (by positivity)
  rw [epistemicBranchLaw_eq_binomial_mixture, hp]
  rw [binomial_withDensity_sum (range (n + 1))
    (fun j x => ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (n.choose j : ℝ)) * gaussianPDF μ
      (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2) (sq_nonneg _)) x)
    (fun _ => measurable_const.mul (measurable_gaussianPDF _ _))]
  apply sum_congr rfl
  intro j hj
  have hv : (NNReal.mk ((σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2)
      (sq_nonneg _) : NNReal) ≠ 0 := by
    intro hz
    have hz' : (σ * (1 + ε) ^ j * (1 - ε) ^ (n - j)) ^ 2 = 0 :=
      congrArg (fun v : NNReal => (v : ℝ)) hz
    exact (pow_ne_zero 2 (ne_of_gt (epistemicBinomialScale_pos n j hσ hε₀ hε₁))) hz'
  rw [gaussianReal_of_var_ne_zero μ hv]
  exact (withDensity_smul' _ _ ENNReal.ofReal_ne_top).symm

/-- Section III's actual mixture density integrates to one. This is
deduced from the already proved probability law and density bridge. -/
theorem epistemicBinomialDensity_lintegral (n : ℕ) (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (epistemicBinomialDensity n μ σ ε x)) = 1 := by
  have hm := congrArg (fun ν : Measure ℝ => ν univ)
    (epistemicBranchLaw_eq_withDensity n μ hσ hε₀ hε₁)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using hm.symm

/-- The printed real density has total integral one (Section III). -/
theorem epistemicBinomialDensity_integral (n : ℕ) (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (∫ x : ℝ, epistemicBinomialDensity n μ σ ε x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (epistemicBinomialDensity_nonneg n μ σ ε))
    (epistemicBinomialDensity_measurable n μ σ ε).aestronglyMeasurable,
    epistemicBinomialDensity_lintegral n μ hσ hε₀ hε₁, ENNReal.toReal_one]

/-- Actual event probabilities are integrals of the printed density
(Section III). In particular this supplies the genuine survival integral,
before any closed-form Gaussian tail or erfc rewrite. -/
theorem epistemicBranchLaw_real_eq_integral_density (n : ℕ) (μ : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (epistemicBranchLaw n μ σ ε).real s =
      ∫ x in s, epistemicBinomialDensity n μ σ ε x := by
  unfold Measure.real
  rw [epistemicBranchLaw_eq_withDensity n μ hσ hε₀ hε₁, withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (epistemicBinomialDensity_nonneg n μ σ ε))
    (epistemicBinomialDensity_measurable n μ σ ε).aestronglyMeasurable.restrict).symm

example (j : ℕ) : 0 < (2 : ℝ) * (1 + 1 / 2) ^ j * (1 - 1 / 2) ^ (2 - j) :=
  epistemicBinomialScale_pos _ _ (by norm_num) (by norm_num) (by norm_num)

example : epistemicBranchLaw 2 1 2 (1 / 2) = volume.withDensity
    (fun x => ENNReal.ofReal (epistemicBinomialDensity 2 1 2 (1 / 2) x)) :=
  epistemicBranchLaw_eq_withDensity _ _ (by norm_num) (by norm_num) (by norm_num)

example : (∫⁻ x : ℝ, ENNReal.ofReal (epistemicBinomialDensity 2 1 2 (1 / 2) x)) = 1 :=
  epistemicBinomialDensity_lintegral _ _ (by norm_num) (by norm_num) (by norm_num)

example : (∫ x : ℝ, epistemicBinomialDensity 2 1 2 (1 / 2) x) = 1 :=
  epistemicBinomialDensity_integral _ _ (by norm_num) (by norm_num) (by norm_num)

example : Integrable (epistemicBinomialDensity 2 1 2 (1 / 2)) :=
  epistemicBinomialDensity_integrable _ _ _ _

example : (epistemicBranchLaw 2 1 2 (1 / 2)).real (Ici 3) =
    ∫ x in Ici 3, epistemicBinomialDensity 2 1 2 (1 / 2) x :=
  epistemicBranchLaw_real_eq_integral_density _ _ (by norm_num) (by norm_num)
    (by norm_num) measurableSet_Ici

#print axioms epistemicBranchLaw_eq_withDensity
#print axioms epistemicBinomialDensity_integral
#print axioms epistemicBranchLaw_real_eq_integral_density

end TailOptionPricing
