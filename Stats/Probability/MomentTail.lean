module

/-
  Actual tails controlled by polynomial moments. These Markov bounds
  and limits support the comparison of the Normal--Lognormal and
  Normal--Gamma outcomes in arXiv:1912.00277v2, Section VI.
  All natural absolute moments imply tails smaller than every real
  power. This does not assert exponential moments or Gaussian decay.
-/
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Polynomial Markov bound for an actual absolute-tail event.
The natural order may be zero; the threshold must be positive.
Used for Section VI's Normal--Lognormal outcome comparison. -/
theorem measureReal_abs_tail_le_moment {μ : Measure ℝ} [IsFiniteMeasure μ]
    {k : ℕ} (hi : Integrable (fun y : ℝ => y ^ k) μ) {x : ℝ} (hx : 0 < x) :
    μ.real {y | x ≤ |y|} ≤ (∫ y : ℝ, |y| ^ k ∂μ) / x ^ k := by
  have ha : Integrable (fun y : ℝ => |y| ^ k) μ := by
    simpa only [abs_pow] using hi.abs
  have hs : {y : ℝ | x ≤ |y|} ⊆ {y : ℝ | x ^ k ≤ |y| ^ k} := by
    intro y hy
    exact pow_le_pow_left₀ hx.le hy k
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun y : ℝ => pow_nonneg (abs_nonneg y) k)) ha (x ^ k)
  calc
    _ ≤ μ.real {y : ℝ | x ^ k ≤ |y| ^ k} := measureReal_mono hs
    _ ≤ _ := (le_div_iff₀ (pow_pos hx k)).mpr (by simpa only [mul_comm] using hm)

/-- If every natural power is L1 under an actual finite law, its
absolute-tail probability times x^p tends to zero for every real p.
A higher integer moment supplies the strict power gap (Section VI).
No tail-decay assumption is included among the hypotheses. -/
theorem measureReal_abs_tail_rpow_tendsto_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ) (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ p * μ.real {y | x ≤ |y|}) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt p
  let M : ℝ := ∫ y : ℝ, |y| ^ k ∂μ
  have ht : Tendsto (fun x : ℝ => M * x ^ (p - (k : ℝ))) atTop (𝓝 0) := by
    have he : p - (k : ℝ) = -((k : ℝ) - p) := by ring
    rw [he]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul M
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le p) measureReal_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    calc
      _ ≤ x ^ p * (M / x ^ k) := mul_le_mul_of_nonneg_left
        (measureReal_abs_tail_le_moment (hi k) hx) (Real.rpow_nonneg hx.le p)
      _ = M * x ^ (p - (k : ℝ)) := by
        rw [Real.rpow_sub hx, Real.rpow_natCast]
        ring

/-- Actual right tails are negligible relative to every reciprocal
real power whenever all natural moments exist. This is used for the
source's centered Normal--Lognormal population (Section VI). -/
theorem measureReal_right_tail_rpow_tendsto_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ) (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ p * μ.real (Ioi x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (measureReal_abs_tail_rpow_tendsto_zero hi p)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le p) measureReal_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le p)
    apply measureReal_mono _ (by finiteness)
    intro y hy
    exact hy.le.trans (le_abs_self y)

/-- The reflected actual left tail has the same upper bound, without
any symmetry assumption on the finite population (Section VI). -/
theorem measureReal_left_tail_rpow_tendsto_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ) (p : ℝ) :
    Tendsto (fun x : ℝ => x ^ p * μ.real (Iio (-x))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (measureReal_abs_tail_rpow_tendsto_zero hi p)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le p) measureReal_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le p)
    apply measureReal_mono _ (by finiteness)
    intro y hy
    change y < -x at hy
    exact (show x ≤ -y by linarith).trans (neg_le_abs y)

/-- Equal power normalization cancels from a tail ratio. A vanishing
normalized numerator and nonzero normalized denominator give an actual
zero ratio limit. Used to compare Section VI's outcome populations. -/
theorem tendsto_ratio_zero_of_rpow_limits {f g : ℝ → ℝ} {p C : ℝ}
    (hf : Tendsto (fun x : ℝ => x ^ p * f x) atTop (𝓝 0))
    (hg : Tendsto (fun x : ℝ => x ^ p * g x) atTop (𝓝 C)) (hC : C ≠ 0) :
    Tendsto (fun x : ℝ => f x / g x) atTop (𝓝 0) := by
  have ht := hf.div hg hC
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Pi.div_apply]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hx p).ne'

/-- All natural moments exclude an actual positive-coefficient
power-tail asymptotic at every finite real exponent (Section VI).
This conclusion concerns the actual survival, not a density formula. -/
theorem measureReal_right_tail_not_power_asymptotic {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun y : ℝ => y ^ k) μ) (p : ℝ) {C : ℝ} (hC : 0 < C) :
    ¬Tendsto (fun x : ℝ => x ^ p * μ.real (Ioi x)) atTop (𝓝 C) := by
  intro h
  have he := tendsto_nhds_unique (measureReal_right_tail_rpow_tendsto_zero hi p) h
  exact hC.ne' he.symm

example : (Measure.dirac (0 : ℝ)).real {y | 1 ≤ |y|} ≤
    (∫ y : ℝ, |y| ^ 2 ∂Measure.dirac 0) / 1 ^ 2 :=
  measureReal_abs_tail_le_moment (integrable_dirac (by simp)) (by norm_num)

example : Tendsto (fun x : ℝ => x ^ (2 : ℝ) *
    (Measure.dirac (0 : ℝ)).real {y | x ≤ |y|}) atTop (𝓝 0) :=
  measureReal_abs_tail_rpow_tendsto_zero (fun _ => integrable_dirac (by simp)) 2

example : Tendsto (fun x : ℝ => x ^ (2 : ℝ) *
    (Measure.dirac (0 : ℝ)).real (Ioi x)) atTop (𝓝 0) :=
  measureReal_right_tail_rpow_tendsto_zero (fun _ => integrable_dirac (by simp)) 2

example : Tendsto (fun x : ℝ => x ^ (2 : ℝ) *
    (Measure.dirac (0 : ℝ)).real (Iio (-x))) atTop (𝓝 0) :=
  measureReal_left_tail_rpow_tendsto_zero (fun _ => integrable_dirac (by simp)) 2

#print axioms measureReal_abs_tail_le_moment
#print axioms measureReal_abs_tail_rpow_tendsto_zero
#print axioms measureReal_right_tail_rpow_tendsto_zero
#print axioms measureReal_left_tail_rpow_tendsto_zero

example : Tendsto (fun _ : ℝ => (0 : ℝ) / 1) atTop (𝓝 0) := by
  apply tendsto_ratio_zero_of_rpow_limits (p := 0) (C := 1)
  · simpa only [Real.rpow_zero, one_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  · simpa only [Real.rpow_zero, one_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1))
  · norm_num

example : ¬Tendsto (fun x : ℝ => x ^ (2 : ℝ) *
    (Measure.dirac (0 : ℝ)).real (Ioi x)) atTop (𝓝 1) :=
  measureReal_right_tail_not_power_asymptotic (fun _ => integrable_dirac (by simp))
    2 (by norm_num)

#print axioms tendsto_ratio_zero_of_rpow_limits
#print axioms measureReal_right_tail_not_power_asymptotic

end TailOptionPricing
