module

/-
  Fractional moments of the actual dispersion law in
  arXiv:1912.00277v2, Section III. This extends the natural-order
  calculation and tests Section III's infinite-depth tail discussion:
  moments of order strictly between zero and one tend to zero.
  No limiting outcome law is inferred here from higher-moment divergence.
-/
public import Stats.EpistemicUncertainty.ScaleLaw
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Actual real-order dispersion moment, extending Section III's
finite-depth calculation. Positive branch scales justify multiplicativity
of real powers; L1 follows from the independently constructed atomic law. -/
theorem epistemicScaleLaw_moment_rpow (n : ℕ) (p : ℝ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (∫ s : ℝ, s ^ p ∂epistemicScaleLaw n σ ε) =
      σ ^ p * (((1 + ε) ^ p + (1 - ε) ^ p) / 2) ^ n := by
  have hplus : 0 < 1 + ε := by linarith
  have hminus : 0 < 1 - ε := by linarith
  induction n generalizing σ with
  | zero => simp [epistemicScaleLaw]
  | succ n ih =>
    rw [epistemicScaleLaw, equalMixture_integral (epistemicScaleLaw_integrable n _ ε _)
      (epistemicScaleLaw_integrable n _ ε _), ih (mul_pos hσ hplus), ih (mul_pos hσ hminus),
      Real.mul_rpow hσ.le hplus.le, Real.mul_rpow hσ.le hminus.le,
      pow_succ (((1 + ε) ^ p + (1 - ε) ^ p) / 2) n]
    ring

/-- Strict contraction of the fractional dispersion-moment factor.
For the source's nonzero error in (0,1), strict concavity of x^p,
0<p<1, reverses the higher-order convexity comparison in Section III. -/
theorem epistemicScaleLaw_fractional_factor {p ε : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    0 < ((1 + ε) ^ p + (1 - ε) ^ p) / 2 ∧
      ((1 + ε) ^ p + (1 - ε) ^ p) / 2 < 1 := by
  have hplus : 0 < 1 + ε := by linarith
  have hminus : 0 < 1 - ε := by linarith
  constructor
  · exact div_pos (add_pos (Real.rpow_pos_of_pos hplus p) (Real.rpow_pos_of_pos hminus p))
      (by norm_num)
  · have h := (Real.strictConcaveOn_rpow hp₀ hp₁).2 hplus.le hminus.le
      (show 1 + ε ≠ 1 - ε by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at h
    have hm : (1 / 2 : ℝ) * (1 + ε) + (1 / 2) * (1 - ε) = 1 := by ring
    rw [hm, Real.one_rpow] at h
    have he : ((1 + ε) ^ p + (1 - ε) ^ p) / 2 =
        (1 / 2 : ℝ) * (1 + ε) ^ p + (1 / 2) * (1 - ε) ^ p := by ring
    rw [he]
    exact h

/-- Genuine dispersion moments of every order p in (0,1) tend to zero
for positive base scale and error in (0,1). This is an actual moment
limit for Section III's populations, without a tail-class conclusion. -/
theorem epistemicScaleLaw_fractional_moment_tendsto_zero {σ ε p : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hp₀ : 0 < p) (hp₁ : p < 1) :
    Tendsto (fun n => ∫ s : ℝ, s ^ p ∂epistemicScaleLaw n σ ε) atTop (𝓝 0) := by
  have hr := epistemicScaleLaw_fractional_factor hp₀ hp₁ hε₀ hε₁
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2
  have hc : Tendsto (fun _ : ℕ => σ ^ p) atTop (𝓝 (σ ^ p)) := tendsto_const_nhds
  have he : (fun n => ∫ s : ℝ, s ^ p ∂epistemicScaleLaw n σ ε) =
      fun n => σ ^ p * (((1 + ε) ^ p + (1 - ε) ^ p) / 2) ^ n :=
    funext (fun n => epistemicScaleLaw_moment_rpow n p hσ hε₀.le hε₁)
  rw [he]
  simpa only [mul_zero] using hc.mul ht

example : Integrable (fun s : ℝ => s ^ (1 / 2 : ℝ)) (epistemicScaleLaw 2 2 (1 / 2)) :=
  epistemicScaleLaw_integrable _ _ _ _

example : (∫ s : ℝ, s ^ (1 / 2 : ℝ) ∂epistemicScaleLaw 2 2 (1 / 2)) =
    (2 : ℝ) ^ (1 / 2 : ℝ) *
      (((1 + (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) / 2) ^ 2 :=
  epistemicScaleLaw_moment_rpow _ _ (by norm_num) (by norm_num) (by norm_num)

example : 0 < ((1 + (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) +
    (1 - (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) / 2 ∧
    ((1 + (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) + (1 - (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) / 2 < 1 :=
  epistemicScaleLaw_fractional_factor (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (fun n => ∫ s : ℝ, s ^ (1 / 2 : ℝ) ∂epistemicScaleLaw n 2 (1 / 2))
    atTop (𝓝 0) := epistemicScaleLaw_fractional_moment_tendsto_zero
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms epistemicScaleLaw_moment_rpow
#print axioms epistemicScaleLaw_fractional_factor
#print axioms epistemicScaleLaw_fractional_moment_tendsto_zero

end TailOptionPricing
