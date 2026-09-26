/-
  Risk measures & portfolio theory under Pareto.

  Standard Markowitz / Sharpe theory assumes finite variance.  Under
  strong Pareto with `α ≤ 2` variance is infinite (see
  `variance_layerCake_not_integrable`), so the variance-based
  framework collapses.  This module rebuilds risk and portfolio
  primitives in Pareto-native form.

  Umbrella module — the formalisation is split into submodules:

  * `Stats.RiskMeasures.CVaR` — Item 1: `paretoCVaR` properties
    (monotonicity in `p`, `l`, scaling, `paretoCVaR ≥ paretoVaR`).
  * `Stats.RiskMeasures.Spectral` — Item 2: spectral risk-measure
    family `M_φ := ∫_0^1 φ(p)·VaR_p dp`.
  * `Stats.RiskMeasures.Moments` — Item 3: `paretoMoment` — `k`-th
    raw moment finite iff `α > k`.
  * `Stats.RiskMeasures.MarkowitzFailure` — Item 4: two-asset Pareto
    Mean-CVaR frontier under comonotone / independent dependence.
  * `Stats.RiskMeasures.Drawdown` — Item 5: drawdown tail
    asymptotic under iid Pareto returns.
  * `Stats.RiskMeasures.Kelly` — Item 6: Kelly criterion `f*` as
    unique zero of the Kelly objective's derivative.
  * `Stats.RiskMeasures.MLE` — Item 7: tail-index MLE `α̂` with
    asymptotic variance `α²/n`.

  All theorems are proved directly from existing strong-Pareto
  closed forms (Pareto.lean), the variance-breakdown machinery
  (`rpow_mul_survival_integrableOn_iff`), and Mathlib's interval
  integration.
-/
import Stats.RiskMeasures.CVaR
import Stats.RiskMeasures.Spectral
import Stats.RiskMeasures.Moments
import Stats.RiskMeasures.MarkowitzFailure
import Stats.RiskMeasures.Drawdown
import Stats.RiskMeasures.Kelly
import Stats.RiskMeasures.MLE
