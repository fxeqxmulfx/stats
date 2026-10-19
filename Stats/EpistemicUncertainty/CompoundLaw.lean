module

/-
  Genuine Normal–Lognormal precision mixture,
  arXiv:1912.00277v2, Section V, Eq. compound. Independently sample
  precision Lambda with the existing actual lognormal law and a
  standard Gaussian innovation. Conditional standard deviation is
  Lambda^(-1/2), hence conditional variance is 1/Lambda.
-/
public import Stats.Probability.LognormalDensity
public import Stats.Probability.GaussianMixtureMoments

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

open LognormalMeasure

/-- Positive precision converted to a standard-deviation power,
Section V's parametrization lambda=1/sigma squared. -/
theorem epistemic_inverseSqrt_pow {l : ℝ} (hl : 0 < l) (k : ℕ) :
    (l ^ (-1 / 2 : ℝ)) ^ k = l ^ (-(k : ℝ) / 2) := by
  rw [← Real.rpow_natCast (l ^ (-1 / 2 : ℝ)) k,
    ← Real.rpow_mul hl.le (-1 / 2) (k : ℝ)]
  congr 1
  ring

theorem epistemic_inverseSqrt_sq {l : ℝ} (hl : 0 < l) :
    (l ^ (-1 / 2 : ℝ)) ^ 2 = l⁻¹ := by
  rw [epistemic_inverseSqrt_pow hl]
  norm_num [Real.rpow_neg_one]

/-- The actual standard-deviation prior induced by the lognormal
precision in Section V. No distributional approximation is assumed. -/
noncomputable def epistemicLognormalScaleLaw (m : ℝ) (v : NNReal) : Measure ℝ :=
  (lognormalReal m v).map (fun l : ℝ => l ^ (-1 / 2 : ℝ))

instance epistemicLognormalScaleLaw_probability (m : ℝ) (v : NNReal) :
    IsProbabilityMeasure (epistemicLognormalScaleLaw m v) := by
  unfold epistemicLognormalScaleLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

theorem epistemicLognormalScaleLaw_ae_pos (m : ℝ) (v : NNReal) :
    ∀ᵐ s ∂epistemicLognormalScaleLaw m v, 0 < s := by
  unfold epistemicLognormalScaleLaw
  apply (ae_map_iff (by fun_prop) measurableSet_Ioi).mpr
  exact (lognormalReal_ae_pos m v).mono (fun l hl => Real.rpow_pos_of_pos hl _)

/-- Every natural standard-deviation moment is L1 because the actual
precision prior has all negative real-order moments (Section V). -/
theorem epistemicLognormalScaleLaw_integrable_pow (m : ℝ) (v : NNReal) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (epistemicLognormalScaleLaw m v) := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => s ^ k) := by fun_prop
  rw [epistemicLognormalScaleLaw, integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable]
  change Integrable (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) (lognormalReal m v)
  have he : (fun l : ℝ => l ^ (-(k : ℝ) / 2)) =ᵐ[lognormalReal m v]
      (fun l : ℝ => (l ^ (-1 / 2 : ℝ)) ^ k) := by
    filter_upwards [lognormalReal_ae_pos m v] with l hl
    exact (epistemic_inverseSqrt_pow hl k).symm
  exact (lognormalReal_integrable_rpow m v _).congr he

/-- Actual moments of the induced dispersion prior, derived by
change of law and the proved inverse-precision moments (Section V). -/
theorem epistemicLognormalScaleLaw_moment_pow (m : ℝ) (v : NNReal) (k : ℕ) :
    (∫ s : ℝ, s ^ k ∂epistemicLognormalScaleLaw m v) =
      Real.exp (-(k : ℝ) * m / 2 + (v : ℝ) * (k : ℝ) ^ 2 / 8) := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have hf : Measurable (fun s : ℝ => s ^ k) := by fun_prop
  rw [epistemicLognormalScaleLaw, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  calc
    _ = ∫ l : ℝ, l ^ (-(k : ℝ) / 2) ∂lognormalReal m v := by
      apply integral_congr_ae
      filter_upwards [lognormalReal_ae_pos m v] with l hl
      exact epistemic_inverseSqrt_pow hl k
    _ = _ := by rw [lognormalReal_moment_rpow]; congr 1; ring

/-- Section V's actual Normal–Lognormal compound, with location mu,
Gaussian log-precision mean m and log-precision variance v. Its
conditional Gaussian has actual variance 1/Lambda on positive precision. -/
noncomputable def epistemicNormalLognormalLaw (μ m : ℝ) (v : NNReal) : Measure ℝ :=
  epistemicGaussianMixtureLaw μ (epistemicLognormalScaleLaw m v)

instance epistemicNormalLognormalLaw_probability (μ m : ℝ) (v : NNReal) :
    IsProbabilityMeasure (epistemicNormalLognormalLaw μ m v) := by
  unfold epistemicNormalLognormalLaw
  infer_instance

/-- An actual independent precision draw and Gaussian innovation
generate the whole compound measure, Section V's probabilistic model. -/
theorem epistemicNormalLognormalLaw_outcome_model (μ m : ℝ) (v : NNReal) :
    ((lognormalReal m v).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => μ + p.1 ^ (-1 / 2 : ℝ) * p.2) =
        epistemicNormalLognormalLaw μ m v := by
  have hm : Measurable (fun l : ℝ => l ^ (-1 / 2 : ℝ)) := by fun_prop
  have ho : Measurable (fun p : ℝ × ℝ => μ + p.1 * p.2) := by fun_prop
  have he := Measure.map_prod_map (lognormalReal m v) (gaussianReal 0 1) hm measurable_id
  rw [Measure.map_id] at he
  rw [epistemicNormalLognormalLaw, ← epistemicGaussianMixtureLaw_outcome_model,
    epistemicLognormalScaleLaw, he, Measure.map_map ho (hm.prodMap measurable_id)]
  rfl

/-- All actual compound centered powers are L1, independently of
their eventual moment formulas (Section V). -/
theorem epistemicNormalLognormalLaw_integrable_sub_pow (μ m : ℝ) (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => (x - μ) ^ k) (epistemicNormalLognormalLaw μ m v) :=
  epistemicGaussianMixtureLaw_integrable_sub_pow μ _ k
    (epistemicLognormalScaleLaw_integrable_pow m v k)

example : (4 ^ (-1 / 2 : ℝ)) ^ 3 = (4 : ℝ) ^ (-(3 : ℝ) / 2) :=
  epistemic_inverseSqrt_pow (by norm_num) 3

example : (4 ^ (-1 / 2 : ℝ)) ^ 2 = (4 : ℝ)⁻¹ := epistemic_inverseSqrt_sq (by norm_num)

example : IsProbabilityMeasure (epistemicNormalLognormalLaw 1 0 1) := inferInstance

#print axioms epistemicLognormalScaleLaw_moment_pow
#print axioms epistemicNormalLognormalLaw_outcome_model
#print axioms epistemicNormalLognormalLaw_integrable_sub_pow

end TailOptionPricing
