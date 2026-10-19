module

/-
  Corrected Gamma asymptotic failure rate,
  arXiv:1912.00277v2, Section VI. With the source's RATE beta in
  beta^alpha*x^(alpha-1)*exp(-beta*x)/Gamma(alpha), the actual
  hazard tends to beta, not 1/beta. L'Hopital applies to the actual
  density and actual probability survival, both tending to zero.
-/
public import Stats.Probability.GammaCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Calculus.LHopital

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Filter Topology

namespace TailOptionPricing

/-- Gamma's density kernel tends to zero at positive rate, for any
fixed real shape. Proper Gamma shapes are positive (Section VI). -/
theorem gammaPDFReal_tendsto_zero (a : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (gammaPDFReal a r) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => r ^ a / Real.Gamma a *
      (x ^ (a - 1) * Real.exp (-r * x))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a - 1) r hr).const_mul (r ^ a / Real.Gamma a)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [gammaPDFReal, hx.le, neg_mul, mul_assoc]

/-- Corrected Section VI Gamma hazard limit for every proper positive
shape and rate. The printed 1/beta uses a scale convention, whereas
the source's density and matching parameters use the rate convention. -/
theorem gammaHazard_tendsto_rate {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Tendsto (gammaHazard a r) atTop (𝓝 r) := by
  have hi : Tendsto (fun x : ℝ => (a - 1) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (a - 1)
  have ht : Tendsto (fun x : ℝ => r - (a - 1) / x) atTop (𝓝 r) := by
    simpa only [sub_zero] using hi.const_sub r
  have hd : Tendsto (fun x : ℝ =>
      (((a - 1) / x - r) * gammaPDFReal a r x) / (-gammaPDFReal a r x)) atTop (𝓝 r) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hp : gammaPDFReal a r x ≠ 0 := (gammaPDFReal_pos ha hr hx).ne'
    field_simp
    ring
  unfold gammaHazard
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi (a := (0 : ℝ))
    (f := gammaPDFReal a r)
    (f' := fun x => ((a - 1) / x - r) * gammaPDFReal a r x)
    (g := fun x => (gammaMeasure a r).real (Ioi x))
    (g' := fun x => -gammaPDFReal a r x)
    (fun x hx => gammaPDFReal_hasDerivAt a r hx)
    (fun x hx => gammaMeasure_survival_hasDerivAt ha hr hx)
    (fun x hx => neg_ne_zero.mpr (gammaPDFReal_pos ha hr hx).ne')
    (gammaPDFReal_tendsto_zero a hr) (gammaMeasure_survival_tendsto_zero ha hr) hd

/-- With the source's own density convention, reciprocal-rate hazard
limits fail for every rate other than one (Section VI). -/
theorem gammaHazard_not_tendsto_inverse_rate {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hr₁ : r ≠ 1) :
    ¬Tendsto (gammaHazard a r) atTop (𝓝 (1 / r)) := by
  intro h
  have he := tendsto_nhds_unique (gammaHazard_tendsto_rate ha hr) h
  have hs : r * r = 1 := by
    have hm := congrArg (fun x : ℝ => x * r) he
    simpa only [one_div_mul_cancel hr.ne'] using hm
  have he₁ : r = 1 := by nlinarith
  exact hr₁ he₁

example : Tendsto (gammaPDFReal 2 3) atTop (𝓝 0) := gammaPDFReal_tendsto_zero _ (by norm_num)

example : Tendsto (gammaHazard 2 3) atTop (𝓝 3) := gammaHazard_tendsto_rate (by norm_num) (by norm_num)

example : ¬Tendsto (gammaHazard 2 3) atTop (𝓝 (1 / 3)) :=
  gammaHazard_not_tendsto_inverse_rate (by norm_num) (by norm_num) (by norm_num)

#print axioms gammaPDFReal_tendsto_zero
#print axioms gammaHazard_tendsto_rate
#print axioms gammaHazard_not_tendsto_inverse_rate

end TailOptionPricing
