module

/-
  Actual general fair sign-vector density, arXiv:1912.00277v2,
  Section II, Eq. gn and matrix M. Its 2^n Gaussian components are
  derived from the already constructed actual varying-error law.
-/
public import Stats.EpistemicUncertainty.SignExpansion

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

private theorem sign_withDensity_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    volume.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, volume.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    change volume.withDensity (f i + (fun x => ∑ j ∈ s, f j x)) = _
    rw [withDensity_add_left (hf i), ih]

/-- The literal 2^n-component Gaussian density of Section II's Eq. gn,
written as 2^(-n) times the sum over every sign vector and its scale. -/
noncomputable def epistemicSignDensity (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ n * ∑ b : Fin n → Bool,
    gaussianPDFReal μ (NNReal.mk ((epistemicSignScale n σ ε b) ^ 2) (sq_nonneg _)) x

/-- The source sign-vector Gaussian expression is nonnegative. -/
theorem epistemicSignDensity_nonneg (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) (x : ℝ) :
    0 ≤ epistemicSignDensity n μ σ ε x :=
  mul_nonneg (by positivity) (sum_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _))

/-- Measurability of the actual finite sign-vector density (Section II). -/
theorem epistemicSignDensity_measurable (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) :
    Measurable (epistemicSignDensity n μ σ ε) :=
  (Finset.measurable_sum _ (fun _ _ => measurable_gaussianPDFReal _ _)).const_mul _

/-- L1 of Section II's density follows from its genuine Gaussian
components, independently of normalization or the actual law bridge. -/
theorem epistemicSignDensity_integrable (n : ℕ) (μ σ : ℝ) (ε : ℕ → ℝ) :
    Integrable (epistemicSignDensity n μ σ ε) :=
  (integrable_finsetSum _ (fun _ _ => integrable_gaussianPDFReal _ _)).const_mul _

/-- Section II's actual recursively constructed population has exactly
Eq. gn's sign-vector Lebesgue density. Positive source scales exclude
zero-variance atoms. The law is not defined by this density identity. -/
theorem epistemicLayerBranchLaw_eq_signDensity (n : ℕ) (μ : ℝ) {σ : ℝ} {ε : ℕ → ℝ}
    (hσ : 0 < σ) (hε : ∀ i < n, 0 ≤ ε i ∧ ε i < 1) :
    epistemicLayerBranchLaw n μ σ ε =
      volume.withDensity (fun x => ENNReal.ofReal (epistemicSignDensity n μ σ ε x)) := by
  have hw : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (1 / 2 : ENNReal) ^ n := by
    rw [ENNReal.ofReal_pow (by positivity)]
    norm_num [ENNReal.ofReal_div_of_pos]
  have hp : (fun x => ENNReal.ofReal (epistemicSignDensity n μ σ ε x)) =
      (fun x => ∑ b : Fin n → Bool, (1 / 2 : ENNReal) ^ n *
        gaussianPDF μ (NNReal.mk ((epistemicSignScale n σ ε b) ^ 2) (sq_nonneg _)) x) := by
    funext x
    unfold epistemicSignDensity
    rw [ENNReal.ofReal_mul (by positivity), hw,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _), mul_sum]
    rfl
  rw [epistemicLayerBranchLaw_eq_sign_mixture, hp,
    sign_withDensity_sum univ (fun b x => (1 / 2 : ENNReal) ^ n *
      gaussianPDF μ (NNReal.mk ((epistemicSignScale n σ ε b) ^ 2) (sq_nonneg _)) x)
      (fun _ => measurable_const.mul (measurable_gaussianPDF _ _))]
  apply sum_congr rfl
  intro b hb
  have hv : (NNReal.mk ((epistemicSignScale n σ ε b) ^ 2) (sq_nonneg _) : NNReal) ≠ 0 := by
    intro hz
    have hz' : (epistemicSignScale n σ ε b) ^ 2 = 0 :=
      congrArg (fun v : NNReal => (v : ℝ)) hz
    exact (pow_ne_zero 2 (ne_of_gt (epistemicSignScale_pos n b hσ hε))) hz'
  rw [gaussianReal_of_var_ne_zero μ hv]
  exact (withDensity_smul' _ _ (by finiteness)).symm

/-- The source's general fair sign-vector density has actual total
nonnegative integral one, by its proved probability law (Section II). -/
theorem epistemicSignDensity_lintegral (n : ℕ) (μ : ℝ) {σ : ℝ} {ε : ℕ → ℝ}
    (hσ : 0 < σ) (hε : ∀ i < n, 0 ≤ ε i ∧ ε i < 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (epistemicSignDensity n μ σ ε x)) = 1 := by
  have h := congrArg (fun ν : Measure ℝ => ν univ)
    (epistemicLayerBranchLaw_eq_signDensity n μ hσ hε)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

/-- The real integral of Eq. gn's actual density is one (Section II). -/
theorem epistemicSignDensity_integral (n : ℕ) (μ : ℝ) {σ : ℝ} {ε : ℕ → ℝ}
    (hσ : 0 < σ) (hε : ∀ i < n, 0 ≤ ε i ∧ ε i < 1) :
    (∫ x : ℝ, epistemicSignDensity n μ σ ε x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (epistemicSignDensity_nonneg n μ σ ε))
    (epistemicSignDensity_measurable n μ σ ε).aestronglyMeasurable,
    epistemicSignDensity_lintegral n μ hσ hε, ENNReal.toReal_one]

/-- Actual measurable event probabilities are the restricted integrals
of Section II's explicit sign-vector density. -/
theorem epistemicLayerBranchLaw_real_eq_signDensity (n : ℕ) (μ : ℝ) {σ : ℝ} {ε : ℕ → ℝ}
    (hσ : 0 < σ) (hε : ∀ i < n, 0 ≤ ε i ∧ ε i < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (epistemicLayerBranchLaw n μ σ ε).real s = ∫ x in s, epistemicSignDensity n μ σ ε x := by
  unfold Measure.real
  rw [epistemicLayerBranchLaw_eq_signDensity n μ hσ hε, withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (epistemicSignDensity_nonneg n μ σ ε))
    (epistemicSignDensity_measurable n μ σ ε).aestronglyMeasurable.restrict).symm

example : epistemicLayerBranchLaw 2 1 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) =
    volume.withDensity (fun x => ENNReal.ofReal
      (epistemicSignDensity 2 1 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) x)) := by
  apply epistemicLayerBranchLaw_eq_signDensity _ _ (by norm_num)
  intro i hi
  interval_cases i <;> norm_num

example : (∫⁻ x : ℝ, ENNReal.ofReal
    (epistemicSignDensity 2 1 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) x)) = 1 := by
  apply epistemicSignDensity_lintegral _ _ (by norm_num)
  intro i hi
  interval_cases i <;> norm_num

example : (∫ x : ℝ, epistemicSignDensity 2 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) x) = 1 := by
  apply epistemicSignDensity_integral _ _ (by norm_num)
  intro i hi
  interval_cases i <;> norm_num

example : (epistemicLayerBranchLaw 2 1 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)).real (Ici 3) =
    ∫ x in Ici 3, epistemicSignDensity 2 1 2 (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i) x := by
  apply epistemicLayerBranchLaw_real_eq_signDensity _ _ (by norm_num) ?_ measurableSet_Ici
  intro i hi
  interval_cases i <;> norm_num

#print axioms epistemicLayerBranchLaw_eq_signDensity
#print axioms epistemicSignDensity_integral
#print axioms epistemicLayerBranchLaw_real_eq_signDensity

end TailOptionPricing
