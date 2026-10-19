module

/-
  Risk expressions and analytic ingredients under strong Pareto tails.

  This umbrella exposes CVaR/VaR expression identities, spectral
  integrals, moment-integrability thresholds, comonotone portfolio
  formulas, candidate maximum-tail bounds, pointwise Kelly derivatives
  and candidate MLE variance/interval expressions.

  The moment and tail integrals require their stated parameter domains.
  Several other definitions are scalar formulas motivated by probability:
  they do not themselves construct a portfolio law, an efficient frontier,
  an iid maximum or path drawdown, an optimal stake, or an estimator CLT
  and confidence-interval coverage. See each submodule's hypotheses and
  REVIEW.md for the distinction between proved identities and law bridges.
-/
public import Stats.RiskMeasures.CVaR
public import Stats.RiskMeasures.Spectral
public import Stats.RiskMeasures.Moments
public import Stats.RiskMeasures.MarkowitzFailure
public import Stats.RiskMeasures.Drawdown
public import Stats.RiskMeasures.Kelly
public import Stats.RiskMeasures.MLE

@[expose] public section
