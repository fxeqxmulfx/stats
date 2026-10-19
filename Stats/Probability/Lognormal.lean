module

/-
  Genuine lognormal probability laws and all real-order moments.
  Sources: arXiv:1912.00277v2, Section V, precision prior and compound
  moments; arXiv:1802.05495v3, Appendix B, lognormal raw moments.
  The law is the exponential pushforward of an actual Gaussian.
  Integrability is proved independently of the moment identity.
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Stats.Kappa.LognormalMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing.LognormalMeasure

/-- The actual precision prior is supported on strictly positive
values, independently of any density or moment formula (Section V). -/
theorem lognormalReal_ae_pos (m : ℝ) (v : NNReal) : ∀ᵐ x ∂lognormalReal m v, 0 < x := by
  unfold lognormalReal
  exact (ae_map_iff Real.measurable_exp.aemeasurable measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall Real.exp_pos)

/-- The logarithm of the actual prior has exactly the prescribed
Gaussian law; equality concerns the whole measure (Section V). -/
theorem lognormalReal_map_log (m : ℝ) (v : NNReal) :
    (lognormalReal m v).map Real.log = gaussianReal m v := by
  rw [lognormalReal, Measure.map_map Real.measurable_log Real.measurable_exp]
  have he : Real.log ∘ Real.exp = (id : ℝ → ℝ) := funext Real.log_exp
  rw [he, Measure.map_id]

/-- Every real power, including negative powers, is genuinely L1 under
the lognormal precision prior (Section V). Gaussian exponential L1 is
proved before evaluating the corresponding moment. -/
theorem lognormalReal_integrable_rpow (m : ℝ) (v : NNReal) (p : ℝ) :
    Integrable (fun x : ℝ => x ^ p) (lognormalReal m v) := by
  have hm : Measurable (fun x : ℝ => x ^ p) := by fun_prop
  rw [lognormalReal, integrable_map_measure hm.aestronglyMeasurable Real.measurable_exp.aemeasurable]
  change Integrable (fun x : ℝ => (Real.exp x) ^ p) (gaussianReal m v)
  simp_rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  simpa only [mul_comm] using (integrable_exp_mul_gaussianReal (μ := m) (v := v) p)

/-- Actual real-order lognormal moments, including inverse precision
moments needed by the Normal–Lognormal compound (Section V):
E[X^p] = exp(p*m + v*p squared/2). -/
theorem lognormalReal_moment_rpow (m : ℝ) (v : NNReal) (p : ℝ) :
    (∫ x : ℝ, x ^ p ∂lognormalReal m v) = Real.exp (p * m + (v : ℝ) * p ^ 2 / 2) := by
  have hm : Measurable (fun x : ℝ => x ^ p) := by fun_prop
  rw [lognormalReal, integral_map Real.measurable_exp.aemeasurable hm.aestronglyMeasurable]
  simp_rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  simpa only [mgf, id_eq, mul_comm] using
    (mgf_gaussianReal (HasLaw.id (μ := gaussianReal m v)) p)

/-- Natural powers are L1 under the actual law, as required by the
raw-moment formulas of arXiv:1802.05495v3, Appendix B. -/
theorem lognormalReal_integrable_pow (m : ℝ) (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (lognormalReal m v) := by
  simpa only [Real.rpow_natCast] using lognormalReal_integrable_rpow m v (k : ℝ)

/-- Actual natural-order moments, not a definitional formula for an
abstract moment sequence (arXiv:1802.05495v3, Appendix B). -/
theorem lognormalReal_moment_pow (m : ℝ) (v : NNReal) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂lognormalReal m v) =
      Real.exp ((k : ℝ) * m + (v : ℝ) * (k : ℝ) ^ 2 / 2) := by
  simpa only [Real.rpow_natCast] using lognormalReal_moment_rpow m v (k : ℝ)

/-- Actual lognormal mean, used when matching the Section V prior to
Gamma distributions and when checking mean-preserving uncertainty. -/
theorem lognormalReal_mean (m : ℝ) (v : NNReal) :
    (∫ x : ℝ, x ∂lognormalReal m v) = Real.exp (m + (v : ℝ) / 2) := by
  simpa only [Real.rpow_one, one_pow, one_mul, mul_one] using lognormalReal_moment_rpow m v 1

/-- Actual inverse-precision expectation determines the conditional
Gaussian mixture variance (arXiv:1912.00277v2, Section V). -/
theorem lognormalReal_inverse_mean (m : ℝ) (v : NNReal) :
    (∫ x : ℝ, x⁻¹ ∂lognormalReal m v) = Real.exp (-m + (v : ℝ) / 2) := by
  simpa only [Real.rpow_neg_one, neg_one_mul, neg_sq, one_pow, mul_one] using
    lognormalReal_moment_rpow m v (-1)

/-- Actual variance of the lognormal prior, for Section VI's matching
to a Gamma law. L2 follows independently from the actual second-moment
integrability theorem, before using the variance identity. -/
theorem lognormalReal_variance (m : ℝ) (v : NNReal) :
    variance (fun x : ℝ => x) (lognormalReal m v) =
      (Real.exp (v : ℝ) - 1) * Real.exp (2 * m + (v : ℝ)) := by
  have hl2 : MemLp (fun x : ℝ => x) 2 (lognormalReal m v) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      (lognormalReal_integrable_pow m v 2)
  rw [variance_eq_sub hl2]
  change (∫ x : ℝ, x ^ 2 ∂lognormalReal m v) -
    (∫ x : ℝ, x ∂lognormalReal m v) ^ 2 = _
  rw [lognormalReal_moment_pow, lognormalReal_mean]
  norm_num only [Nat.cast_ofNat]
  have hs : Real.exp (m + (v : ℝ) / 2) ^ 2 = Real.exp (2 * m + (v : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hs]
  have he : 2 * m + (v : ℝ) * 4 / 2 = (2 * m + (v : ℝ)) + (v : ℝ) := by ring
  rw [he, Real.exp_add]
  ring

/-- The squared coefficient of variation of the actual prior depends
only on its log variance (arXiv:1912.00277v2, Section VI). -/
theorem lognormalReal_squared_cv (m : ℝ) (v : NNReal) :
    variance (fun x : ℝ => x) (lognormalReal m v) /
      (∫ x : ℝ, x ∂lognormalReal m v) ^ 2 = Real.exp (v : ℝ) - 1 := by
  rw [lognormalReal_variance, lognormalReal_mean, ← Real.exp_nat_mul]
  have he : (2 : ℕ) * (m + (v : ℝ) / 2) = 2 * m + (v : ℝ) := by push_cast; ring
  rw [he]
  exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)

/-- The actual lognormal CV in arXiv:1912.00277v2, Section VI.
Its value is independent of log location, including zero log variance. -/
theorem lognormalReal_cv (m : ℝ) (v : NNReal) :
    √(variance (fun x : ℝ => x) (lognormalReal m v)) /
      (∫ x : ℝ, x ∂lognormalReal m v) = √(Real.exp (v : ℝ) - 1) := by
  rw [lognormalReal_variance, lognormalReal_mean]
  have hd : 0 ≤ Real.exp (v : ℝ) - 1 := by
    linarith [Real.add_one_le_exp (v : ℝ), v.coe_nonneg]
  rw [Real.sqrt_mul hd]
  have he : Real.exp (2 * m + (v : ℝ)) = Real.exp (m + (v : ℝ) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he, Real.sqrt_sq (Real.exp_pos _).le, mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]

example : IsProbabilityMeasure (lognormalReal 0 1) := inferInstance

example : (lognormalReal 0 1).map Real.log = gaussianReal 0 1 := lognormalReal_map_log _ _

example : (∫ x : ℝ, x⁻¹ ∂lognormalReal 0 1) = Real.exp (1 / 2) := by
  simpa using lognormalReal_inverse_mean 0 1

#print axioms lognormalReal_map_log
#print axioms lognormalReal_integrable_rpow
#print axioms lognormalReal_moment_rpow
#print axioms lognormalReal_variance
#print axioms lognormalReal_squared_cv
#print axioms lognormalReal_cv

end TailOptionPricing.LognormalMeasure
