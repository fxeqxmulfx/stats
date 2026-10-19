module

/-
  An exact rational integral used to certify the corrected Pareto row of
  arXiv:1802.05495v3, Table I. The constant is a derived regression bound,
  not a value asserted by the paper and not a numerical quadrature result.
-/
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

/-- Integrability of the rational lower-bound kernel on the full closed
integration interval, including both endpoints. -/
theorem pareto_two_rational_intervalIntegrable :
    IntervalIntegrable (fun y : ℝ => y * (2 - y) / (y + 2) ^ 6) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  have hd : ∀ y ∈ uIcc (0 : ℝ) 2, y + 2 ≠ 0 := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hy
    linarith [hy.1]
  exact (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).div
    ((continuousOn_id.add continuousOn_const).pow 6) (fun y hy => pow_ne_zero 6 (hd y hy))

/-- Exact auxiliary value for the corrected Table I Pareto ratio at
`α = 2`, proved by the fundamental theorem of calculus. -/
theorem pareto_two_rational_integral :
    (∫ y in (0 : ℝ)..2, y * (2 - y) / (y + 2) ^ 6) = 23 / 7680 := by
  let F : ℝ → ℝ := fun y => ((y + 2) ^ 3)⁻¹ / 3 -
    3 * ((y + 2) ^ 4)⁻¹ / 2 + 8 * ((y + 2) ^ 5)⁻¹ / 5
  have hF : ∀ y ∈ uIcc (0 : ℝ) 2,
      HasDerivAt F (y * (2 - y) / (y + 2) ^ 6) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hy
    have hd : y + 2 ≠ 0 := by linarith [hy.1]
    have hi : HasDerivAt (fun x : ℝ => x + 2) 1 y := (hasDerivAt_id y).add_const 2
    have h3 := ((hi.pow 3).inv (pow_ne_zero 3 hd)).div_const 3
    have h4 := (((hi.pow 4).inv (pow_ne_zero 4 hd)).const_mul 3).div_const 2
    have h5 := (((hi.pow 5).inv (pow_ne_zero 5 hd)).const_mul 8).div_const 5
    convert (h3.sub h4).add h5 using 1
    norm_num
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    pareto_two_rational_intervalIntegrable
  norm_num [F] at h
  exact h

end TailOptionPricing
