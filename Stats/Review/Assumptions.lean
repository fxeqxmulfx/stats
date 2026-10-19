module

/-
  Concrete certificates for strengthened algebraic interfaces after
  unused assumptions were removed. These distinguish total-integral and
  scalar identities from probabilistic claims in the six-paper review.
-/
public import Stats.Hedging
public import Stats.HiddenMoments
public import Stats.Kappa.PearsonIV
public import Stats.RiskMeasures.CVaR
public import Stats.RiskMeasures.Drawdown
public import Stats.RiskMeasures.Kelly
public import Stats.RiskMeasures.MLE
public import Stats.BinaryForecasts.Conflation

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace StatsReview

open TailOptionPricing

-- The scalar payoff identity also holds for a negative realized value.
example : (-1 : ℝ) / (1 + 0 * (-1)) = -1 := kelly_marginal_at_zero

-- Removed probability-domain assumptions were not used in this algebra.
example : paretoVaR 1 2 (-1) ≤ paretoVaR 1 2 0 :=
  paretoVaR_mono_p (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : paretoVaR 1 0 0 ≤ paretoVaR 2 0 0 :=
  paretoVaR_mono_l (by norm_num) (by norm_num)

example : paretoCVaR 1 2 (-1) ≤ paretoCVaR 1 2 0 :=
  paretoCVaR_mono_p (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : paretoSampleMaxSurvival 2 1 0 1 = 1 :=
  paretoSampleMaxSurvival_at_l (by norm_num) (by norm_num)

example : paretoMLE_asymptoticVariance 0 2 * 2 = 0 ^ 2 :=
  paretoMLE_asymptoticVariance_scaling (by norm_num)

example : n_nu 0 0 = 0 := by
  have h := n_nu_gaussian 0
  norm_num at h
  exact h

example : n_g_of_n_nu (n_nu 0 0) 0 = 0 := by
  have h := n_g_of_n_nu_n_nu (n_g := 0) (κ_g := 0) (by norm_num)
  norm_num at h
  exact h

example : kappa (fun n => (n : ℝ) + 1) 0 1 =
    2 - (Real.log 1 - Real.log 0) /
      (∑ i ∈ Finset.range (1 - 0),
        (Real.log (((0 + i + 1 : ℕ) : ℝ) + 1) -
          Real.log (((0 + i : ℕ) : ℝ) + 1))) := by
  simpa only [Nat.cast_one, Nat.cast_zero] using
    kappa_decomposition (M := fun n => (n : ℝ) + 1) (n₀ := 0) (n := 1) (by norm_num)

-- Alpha zero does not define a Pareto probability law. Both statements
-- below are valid identities of their explicitly defined total integrals.
example : paretoTailMoment 1 0 (-1) 1 =
    0 * (1 : ℝ) ^ (0 : ℝ) * (1 : ℝ) ^ (-1 - 0 : ℝ) / (0 - -1) :=
  paretoTailMoment_eq (by norm_num) (by norm_num) (by norm_num)

example : I1 id (paretoDensity 1 0) 1 = paretoTailExpectation 1 0 1 :=
  I1_pareto_id_eq

example : (∫ s in Ioi (1 : ℝ), gammaPnLIntegrand (fun _ => (1 : ℝ)) s *
    paretoDensity 1 0 s) = (1 / 2) * 1 * paretoMoment 1 0 2 :=
  gammaPnL_constant_eq

-- A smooth affine payoff supplies every analytic premise of the
-- model-free Carr–Madan alias; no Pareto parameters are needed.
example : (3 / 4 : ℝ) = 1 / 2 + 1 * (3 / 4 - 1 / 2) +
    (∫ K in (0 : ℝ)..(1 / 2), max (K - 3 / 4) 0 * 0) +
    (∫ K in (1 / 2 : ℝ)..1, max (3 / 4 - K) 0 * 0) :=
  paretoCarrMadan (g := fun x => x) (g' := fun _ => 1) (g'' := fun _ => 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    continuousOn_id continuousOn_const continuousOn_const
    (fun x _ => hasDerivAt_id x) (fun x _ => hasDerivAt_const x 1)

example : Tendsto (fun K : ℝ => Real.log (1 / K) - 1 / (1 - 1)) atTop atBot :=
  paretoVega_relative_tendsto_atBot (by norm_num)

example : Tendsto (fun n : ℕ => lognormalKappaProxy n 0 0) atTop (𝓝 0) :=
  lognormal_kappa_tendsto_zero_as_n_to_infty 0 0

-- The Pearson conditions are real scalar data, rather than assumed
-- existence of a probability density with the desired moments.
example : 2 * (1 : ℝ) = pearsonIVMADClosed 1 1 0 0 0 1 :=
  pearsonIV_mad_eq 1 1 0 0 0 1 1 (by norm_num)
    (by norm_num [pearsonIVQuad])

example : 2 * (1 : ℝ) = 2 * (1 + 0 * 0 + 0 * 0 ^ 2) * 1 / (1 - 2 * 0) :=
  pearsonIV_mad_eq_paper 1 1 0 0 0 1 1 (by norm_num)
    (by norm_num [pearsonIVQuad])

example : pearsonIV_a1_lognormal = 1 := pearsonIV_lognormal_match_a1

#print axioms TailOptionPricing.pearsonIV_mad_eq
#print axioms TailOptionPricing.paretoCarrMadan

end StatsReview
