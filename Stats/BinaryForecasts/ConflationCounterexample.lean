module

/-
  A smooth nonnegative payoff refutes the fixed-density pointwise converse
  in arXiv:1907.11162v3, Definition 5 (line 347). With the actual supported
  Exp(1) density and positive threshold K=1, g(x)=(x-2)^2 gives equal
  positive integrals while varying where the density is strictly positive.
  The following source sentence assuming positive derivative is separate.
-/
public import Stats.BinaryForecasts.ExponentialLaw
public import Stats.BinaryForecasts.Conflation
public import Stats.Probability.ExponentialIntegration
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Smooth nonnegative payoff for the fixed-density converse
counterexample (arXiv:1907.11162v3, Definition 5). -/
noncomputable def conflationCounterPayoff (x : ℝ) : ℝ := (x - 2) ^ 2

private theorem counter_pow_exp_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (s := (n : ℝ)) (p := 1)
    (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by norm_num)
  simp only [Real.rpow_natCast, Real.rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi (by norm_num))

private theorem counter_kernel_integrable :
    IntegrableOn (fun x : ℝ => conflationCounterPayoff x * Real.exp (-x)) (Ioi 1) := by
  have he : (fun x : ℝ => conflationCounterPayoff x * Real.exp (-x)) =
      fun x => x ^ 2 * Real.exp (-x) - 4 * (x ^ 1 * Real.exp (-x)) +
        4 * (x ^ 0 * Real.exp (-x)) := by
    funext x
    unfold conflationCounterPayoff
    ring
  rw [he]
  exact ((counter_pow_exp_integrable 2).sub ((counter_pow_exp_integrable 1).const_mul 4)).add
    ((counter_pow_exp_integrable 0).const_mul 4)

private theorem counter_kernel_integral : (∫ x in Ioi (1 : ℝ), conflationCounterPayoff x * Real.exp (-x)) =
    Real.exp (-1) := by
  let F := fun x : ℝ => -(x ^ 2 - 2 * x + 2) * Real.exp (-x)
  have hderiv (x : ℝ) : HasDerivAt F (conflationCounterPayoff x * Real.exp (-x)) x := by
    have hp := (((hasDerivAt_id x).pow 2).sub ((hasDerivAt_id x).const_mul 2)).add_const 2
    have h := (hp.neg).mul ((hasDerivAt_id x).neg.exp)
    convert h using 1
    · funext y
      simp [F]
    · unfold conflationCounterPayoff
      norm_num
      ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).sub
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2)).add
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).const_mul 2)).neg
    norm_num at h
    convert h using 1
    funext x
    dsimp [F]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (a := 1) (by dsimp [F]; fun_prop) (fun x _ => hderiv x)
    counter_kernel_integrable hlim
  norm_num [F] at h
  exact h

private theorem counter_pdf_on_tail {x : ℝ} (hx : 1 < x) : exponentialPDFReal 1 x = Real.exp (-x) := by
  have hx0 : 0 ≤ x := by linarith
  simp [exponentialPDFReal, gammaPDFReal, hx0]

/-- Actual supported-density payoff integral in the counterexample
to arXiv:1907.11162v3, Definition 5; the value is proved by an antiderivative. -/
theorem conflationCounter_I1 : I1 conflationCounterPayoff (exponentialPDFReal 1) 1 = Real.exp (-1) := by
  unfold I1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => congrArg (conflationCounterPayoff x * ·) (counter_pdf_on_tail hx)), counter_kernel_integral]

/-- The binary substitution has the same positive value for this
nonconstant payoff (arXiv:1907.11162v3, Definition 5 counterexample). -/
theorem conflationCounter_I2 : I2 conflationCounterPayoff (exponentialPDFReal 1) 1 = Real.exp (-1) := by
  have he : (∫ x in Ioi (1 : ℝ), exponentialPDFReal 1 x) =
      ∫ x in Ioi (1 : ℝ), expDensity 1 x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [counter_pdf_on_tail hx]
    norm_num [expDensity]
  unfold I2
  rw [show conflationCounterPayoff 1 = 1 by norm_num [conflationCounterPayoff], one_mul, he,
    exp_survival_eq (by norm_num)]
  norm_num

/-- The density calculation equals the actual Exp(1) tail expectation,
not an assigned payoff value (arXiv:1907.11162v3, Definition 5 counterexample). -/
theorem conflationCounter_actual_integral :
    (∫ x in Ioi (1 : ℝ), conflationCounterPayoff x ∂expMeasure 1) = Real.exp (-1) := by
  rw [expMeasure_setIntegral (by norm_num)]
  exact conflationCounter_I1

/-- The counterexample payoff is genuinely integrable under the
actual restricted Exp(1) law (arXiv:1907.11162v3, Definition 5 counterexample). -/
theorem conflationCounter_actual_integrable : IntegrableOn conflationCounterPayoff (Ioi (1 : ℝ)) (expMeasure 1) := by
  rw [expMeasure_integrableOn_iff (by norm_num) _ _ measurableSet_Ioi]
  apply counter_kernel_integrable.congr_fun
  · intro x hx
    dsimp only
    rw [counter_pdf_on_tail hx]
  · exact measurableSet_Ioi

/-- The payoff varies above the positive threshold at points where
the exponential density is positive (arXiv:1907.11162v3, Definition 5 counterexample). -/
theorem conflationCounter_not_constant : ¬ ∃ c : ℝ, ∀ x ∈ Ioi (1 : ℝ), conflationCounterPayoff x = c := by
  rintro ⟨c, hc⟩
  have h2 := hc 2 (by norm_num)
  have h4 := hc 4 (by norm_num)
  norm_num [conflationCounterPayoff] at h2 h4
  linarith

/-- Formal counterexample to the fixed-density only-if reading of
arXiv:1907.11162v3, Definition 5. Smoothness, nonnegativity, actual L1
and strictly positive equal integrals do not imply a constant payoff.
A universal identity over every possible density is a different assertion. -/
theorem conflation_fixed_density_counterexample :
    ∃ g : ℝ → ℝ, Differentiable ℝ g ∧ (∀ x, 0 ≤ g x) ∧
      IntegrableOn g (Ioi (1 : ℝ)) (expMeasure 1) ∧
      I1 g (exponentialPDFReal 1) 1 = I2 g (exponentialPDFReal 1) 1 ∧
      0 < I1 g (exponentialPDFReal 1) 1 ∧
      ¬ ∃ c : ℝ, ∀ x ∈ Ioi (1 : ℝ), g x = c := by
  refine ⟨conflationCounterPayoff, ?_, ?_, conflationCounter_actual_integrable, ?_, ?_, conflationCounter_not_constant⟩
  · change Differentiable ℝ (fun x : ℝ => (x - 2) ^ 2)
    fun_prop
  · intro x
    exact sq_nonneg _
  · rw [conflationCounter_I1, conflationCounter_I2]
  · rw [conflationCounter_I1]
    exact Real.exp_pos _

end TailOptionPricing
