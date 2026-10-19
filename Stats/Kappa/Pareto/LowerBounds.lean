module

/-
  Exact lower bounds for the corrected Pareto expression in Taleb,
  arXiv:1802.05495v3, Table I, at alpha = 2. These analytic certificates
  distinguish the convergent Beta difference from the old zero expression.
-/
public import Stats.Kappa.Pareto.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace TailOptionPricing

/-- A uniform lower bound for the negative-parameter Beta kernel used in
Table I at `α = 2`; both endpoints are excluded. -/
theorem betaKernel_two_lower_bound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    27 ≤ betaKernel (-2) (-1) t := by
  have h1 : 0 < 1 - t := by linarith
  have ha : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hb : t ^ 2 * (1 - t) ≤ 4 / 27 := by
    have h := mul_nonneg (sq_nonneg (t - 2 / 3)) (by linarith : 0 ≤ t + 1 / 3)
    nlinarith
  have hp := mul_le_mul ha hb (mul_nonneg (sq_nonneg t) h1.le)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hd : 0 < t ^ 3 * (1 - t) ^ 2 := mul_pos (pow_pos ht 3) (pow_pos h1 2)
  have hprod : t ^ 3 * (1 - t) ^ 2 ≤ 1 / 27 := by nlinarith [hp]
  have heq : betaKernel (-2) (-1) t = 1 / (t ^ (3 : ℕ) * (1 - t) ^ (2 : ℕ)) := by
    unfold betaKernel
    norm_num only [show ((-2 : ℝ) - 1) = -(3 : ℕ) from by norm_num,
      show ((-1 : ℝ) - 1) = -(2 : ℕ) from by norm_num]
    simp only [Real.rpow_neg ht.le, Real.rpow_neg h1.le, Real.rpow_ofNat]
    field_simp
  rw [heq, le_div_iff₀ hd]
  nlinarith

example : 27 ≤ betaKernel (-2) (-1) (1 / 2) :=
  betaKernel_two_lower_bound (by norm_num) (by norm_num)

/-- The proper Beta difference bounds the interval length from below.
This is a convergent-integral inequality for the corrected Table I row. -/
theorem incompleteBetaCentered_two_sub_lower_bound {u v : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) (huv : u ≤ v) :
    27 * (v - u) ≤ incompleteBetaCentered v (-2) (-1) -
      incompleteBetaCentered u (-2) (-1) := by
  rw [incompleteBetaCentered_sub _ _ hv hu]
  have h := intervalIntegral.integral_mono_on huv
    (intervalIntegrable_const (c := (27 : ℝ)))
    (betaKernel_intervalIntegrable (-2) (-1) hu hv)
    (fun t ht => betaKernel_two_lower_bound (hu.1.trans_le ht.1) (ht.2.trans_lt hv.2))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

example : 27 * ((2 / 3 : ℝ) - 1 / 3) ≤
    incompleteBetaCentered (2 / 3) (-2) (-1) - incompleteBetaCentered (1 / 3) (-2) (-1) :=
  incompleteBetaCentered_two_sub_lower_bound (by norm_num) (by norm_num) (by norm_num)

/-- A rational lower bound for the corrected outer integrand at `α = 2`.
Unlike the former expression, it is nonzero throughout the interior. -/
theorem paretoIntegrand_two_lower_bound {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) :
    216 * (y * (2 - y) / (y + 2) ^ 6) ≤ paretoIntegrand 2 y := by
  let u := 1 / (y + 2)
  let v := (y + 1) / (y + 2)
  have hd : 0 < y + 2 := by linarith
  have hend := pareto_beta_endpoints hy
  have huv : u ≤ v := by
    dsimp [u, v]
    exact (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  have hBeta := incompleteBetaCentered_two_sub_lower_bound hend.1 hend.2 huv
  have hc : 0 ≤ 8 * (y + 2) ^ (-5 : ℝ) * (2 - y) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hd.le _)) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hBeta hc
  have hform : paretoIntegrand 2 y =
      (8 * (y + 2) ^ (-5 : ℝ) * (2 - y)) *
        (incompleteBetaCentered v (-2) (-1) - incompleteBetaCentered u (-2) (-1)) := by
    unfold paretoIntegrand
    dsimp [u, v]
    norm_num
    ring
  have heq : (8 * (y + 2) ^ (-5 : ℝ) * (2 - y)) * (27 * (v - u)) =
      216 * (y * (2 - y) / (y + 2) ^ 6) := by
    dsimp [u, v]
    rw [show (-5 : ℝ) = -(5 : ℕ) from by norm_num,
      Real.rpow_neg hd.le, Real.rpow_natCast]
    field_simp
    ring
  calc
    216 * (y * (2 - y) / (y + 2) ^ 6) =
        (8 * (y + 2) ^ (-5 : ℝ) * (2 - y)) * (27 * (v - u)) := heq.symm
    _ ≤ _ := hmul
    _ = paretoIntegrand 2 y := hform.symm

example : 216 * ((1 : ℝ) * (2 - 1) / (1 + 2) ^ 6) ≤ paretoIntegrand 2 1 :=
  paretoIntegrand_two_lower_bound (by norm_num) (by norm_num)

end TailOptionPricing
