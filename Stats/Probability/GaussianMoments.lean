module

/-
  Actual centered Gaussian moments used by arXiv:1907.11162v3, Remark 1,
  and the centered specialization of arXiv:1802.05495v3, Eq. 17.
  Moments are derived from the genuine Gaussian MGF, with independent
  L1 proofs for every natural power. They are not formula definitions.
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory

namespace TailOptionPricing

/-- Every natural power of the actual Gaussian observation is L1,
including order zero and a degenerate variance (the cited moment models). -/
theorem gaussianReal_integrable_pow (μ : ℝ) (v : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal μ v) := by
  have h : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal μ v) :=
    (memLp_id_gaussianReal' n (by finiteness)).integrable_norm_pow'
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ n) (gaussianReal μ v) :=
    (measurable_id.pow_const n).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  simpa only [Real.norm_eq_abs, abs_pow] using h

private theorem gaussianMGF_hasDerivAt_one (v t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (v * s ^ 2 / 2))
      (v * t * exp (v * t ^ 2 / 2)) t := by
  convert ((((hasDerivAt_id' t).pow 2).const_mul v).div_const 2).exp using 1
  dsimp only [Pi.pow_apply]
  ring

private theorem gaussianMGF_hasDerivAt_two (v t : ℝ) :
    HasDerivAt (fun s : ℝ => v * s * exp (v * s ^ 2 / 2))
      ((v + v ^ 2 * t ^ 2) * exp (v * t ^ 2 / 2)) t := by
  convert ((hasDerivAt_id' t).const_mul v).mul (gaussianMGF_hasDerivAt_one v t)
    using 1
  ring

private theorem gaussianMGF_hasDerivAt_three (v t : ℝ) :
    HasDerivAt (fun s : ℝ => (v + v ^ 2 * s ^ 2) * exp (v * s ^ 2 / 2))
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * exp (v * t ^ 2 / 2)) t := by
  have hp := (((hasDerivAt_id' t).pow 2).const_mul (v ^ 2)).const_add v
  convert hp.mul (gaussianMGF_hasDerivAt_one v t) using 1
  dsimp only [Pi.pow_apply]
  ring

private theorem gaussianMGF_hasDerivAt_four_zero (v : ℝ) :
    HasDerivAt (fun s : ℝ => (3 * v ^ 2 * s + v ^ 3 * s ^ 3) * exp (v * s ^ 2 / 2))
      (3 * v ^ 2) 0 := by
  have hp := ((hasDerivAt_id' (0 : ℝ)).const_mul (3 * v ^ 2)).add
    (((hasDerivAt_id' (0 : ℝ)).pow 3).const_mul (v ^ 3))
  convert hp.mul (gaussianMGF_hasDerivAt_one v 0) using 1
  simp

/-- Actual second moment of the centered Gaussian used in the source's
variance-uncertainty calculation. It is obtained by differentiating its MGF. -/
theorem gaussianReal_zero_moment_two (v : NNReal) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by simp) 2
  rw [mgf_fun_id_gaussianReal] at hm
  simp only [zero_mul, zero_add] at hm
  have h1 : deriv (fun t : ℝ => exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v : ℝ) * t * exp ((v : ℝ) * t ^ 2 / 2) :=
    funext (fun t => (gaussianMGF_hasDerivAt_one v t).deriv)
  rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one, h1,
    (gaussianMGF_hasDerivAt_two v 0).deriv] at hm
  simpa using hm.symm

/-- Actual fourth moment of the centered Gaussian in Remark 1 and the
equal-mean specialization of Eq. 17. Four MGF derivatives give 3v². -/
theorem gaussianReal_zero_moment_four (v : NNReal) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 v)
    (by simp) 4
  rw [mgf_fun_id_gaussianReal] at hm
  simp only [zero_mul, zero_add] at hm
  have h1 : deriv (fun t : ℝ => exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (v : ℝ) * t * exp ((v : ℝ) * t ^ 2 / 2) :=
    funext (fun t => (gaussianMGF_hasDerivAt_one v t).deriv)
  have h2 : deriv (fun t : ℝ => (v : ℝ) * t * exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * exp ((v : ℝ) * t ^ 2 / 2) :=
    funext (fun t => (gaussianMGF_hasDerivAt_two v t).deriv)
  have h3 : deriv (fun t : ℝ => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) *
      exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * exp ((v : ℝ) * t ^ 2 / 2) :=
    funext (fun t => (gaussianMGF_hasDerivAt_three v t).deriv)
  rw [iteratedDeriv_succ (n := 3), iteratedDeriv_succ (n := 2),
    iteratedDeriv_succ (n := 1), iteratedDeriv_one, h1, h2, h3,
    (gaussianMGF_hasDerivAt_four_zero v).deriv] at hm
  exact hm.symm

example : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 25) :=
  gaussianReal_integrable_pow _ _ _

example : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 25) = 25 :=
  gaussianReal_zero_moment_two _

example : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 25) = 1875 := by
  rw [gaussianReal_zero_moment_four]
  norm_num

#print axioms gaussianReal_integrable_pow
#print axioms gaussianReal_zero_moment_two
#print axioms gaussianReal_zero_moment_four

end TailOptionPricing
