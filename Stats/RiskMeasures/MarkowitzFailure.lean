module

/-
  Pareto-motivated portfolio expressions and a tail-integrability threshold.

  The portfolio mean and CVaR functions below are supplied scalar formulas.
  Their scaling and ratio identities do not construct a portfolio law or
  solve an optimization problem. A comonotone interpretation requires a
  valid driver law, finite first moment and positive aggregate loading;
  independence and a general diversification theorem are not proved here.
-/
public import Stats.RiskMeasures.CVaR
public import Stats.RiskMeasures.Moments

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 4 — Markowitz failure / Mean-CVaR frontier.

    The classical Markowitz mean-variance objective requires finite
    second moments.  Under strong Pareto with `α ≤ 2`, variance is
    infinite (`variance_layerCake_not_integrable`), so the
    optimisation is ill-defined.  The Pareto-native replacement is
    Mean-CVaR.

    The scalar formulas are motivated by a comonotone driver
    `S ~ Pareto(l,α)` and assets `S_i = c_i*S`. Their law and moment
    identifications are not constructed here. The code establishes
    linear scaling and a loading-invariant ratio for the supplied
    expressions. It neither analyzes independent assets nor proves a
    general diversification or optimization theorem. -/

/-- For `α ≤ 2`, the second-moment tail integrand `s*survival l α s` is
    not integrable on `(l, ∞)`.  Direct restatement of
    `variance_layerCake_not_integrable` in the portfolio-theory
    context. A genuine Pareto-law interpretation requires `α > 0`;
    an ordinary centered variance additionally requires a finite mean. -/
theorem markowitz_objective_ill_defined {l α : ℝ}
    (hα_le : α ≤ 2) (hl : 0 < l) :
    ¬ IntegrableOn (fun s => s * survival l α s) (Ioi l) volume :=
  variance_layerCake_not_integrable hα_le hl

/-- Candidate portfolio-mean expression
    `(w₁*c₁ + w₂*c₂)*α*l/(α-1)`. Its expected-value interpretation
    requires a valid integrable comonotone driver and a law bridge. -/
noncomputable def paretoPortfolioMean (w₁ w₂ c₁ c₂ l α : ℝ) : ℝ :=
  (w₁ * c₁ + w₂ * c₂) * (α * l / (α - 1))

/-- Candidate portfolio-CVaR expression. Interpreting the aggregate
    as a positively scaled Pareto law requires positive loading and
    valid model parameters, beyond this scalar definition. -/
noncomputable def paretoPortfolioCVaR (w₁ w₂ c₁ c₂ l α p : ℝ) : ℝ :=
  (w₁ * c₁ + w₂ * c₂) * paretoCVaR l α p

/-- The portfolio-CVaR expression equals the same formula at the
    rescaled location, by scalar homogeneity. This identity holds
    outside the domain of an actual positive-scale portfolio law. -/
theorem paretoPortfolioCVaR_eq_rescaled {w₁ w₂ c₁ c₂ l α p : ℝ} :
    paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = paretoCVaR ((w₁ * c₁ + w₂ * c₂) * l) α p := by
  unfold paretoPortfolioCVaR
  rw [paretoCVaR_scale]

/-- **Mean-CVaR ratio is loading-invariant under comonotone Pareto.**
    For non-degenerate aggregate loading `(w·c) ≠ 0`, the ratio of
    portfolio mean to portfolio CVaR depends only on `(α, l, p)`, not
    on the portfolio weights.  Every comonotone-Pareto portfolio lies
    on the **same line through the origin** in mean-CVaR coordinates.

    This is a ratio identity for the defined functions; an actual
    portfolio-risk interpretation requires their law bridges. -/
theorem paretoPortfolio_meanCVaR_ratio {w₁ w₂ c₁ c₂ l α p : ℝ}
    (h_pos : 0 < w₁ * c₁ + w₂ * c₂) (hcvar_ne : paretoCVaR l α p ≠ 0) :
    paretoPortfolioMean w₁ w₂ c₁ c₂ l α / paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = (α * l / (α - 1)) / paretoCVaR l α p := by
  unfold paretoPortfolioMean paretoPortfolioCVaR
  have h_pos_ne : (w₁ * c₁ + w₂ * c₂ : ℝ) ≠ 0 := h_pos.ne'
  field_simp

/-- The candidate portfolio-mean expression is homogeneous for
    every real scale `lam`. No expectation occurs in this identity. -/
theorem paretoPortfolioMean_scale (lam w₁ w₂ c₁ c₂ l α : ℝ) :
    paretoPortfolioMean (lam * w₁) (lam * w₂) c₁ c₂ l α
      = lam * paretoPortfolioMean w₁ w₂ c₁ c₂ l α := by
  unfold paretoPortfolioMean
  ring

/-- The candidate portfolio-CVaR expression is homogeneous for
    every real scale `lam`; this does not assert negative-scale
    homogeneity of an actual CVaR risk functional. -/
theorem paretoPortfolioCVaR_scale (lam w₁ w₂ c₁ c₂ l α p : ℝ) :
    paretoPortfolioCVaR (lam * w₁) (lam * w₂) c₁ c₂ l α p
      = lam * paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p := by
  unfold paretoPortfolioCVaR
  ring

/-- Equality of ratios of the two supplied portfolio formulas.
    The candidate curve in mean/CVaR coordinates, parameterised by
    aggregate loading `m := w₁·c₁ + w₂·c₂`, is the line
        (paretoPortfolioMean = m · α·l/(α−1),
         paretoPortfolioCVaR = m · paretoCVaR(l, α, p))
    has slope independent of `m`. This scalar identity does not
    construct an efficient frontier or prove a criterion involving
    a tail-dependence coefficient. -/
theorem paretoPortfolio_frontier_degenerate {l α p : ℝ}
    {w₁ w₂ c₁ c₂ w₁' w₂' c₁' c₂' : ℝ}
    (h_pos : 0 < w₁ * c₁ + w₂ * c₂)
    (h_pos' : 0 < w₁' * c₁' + w₂' * c₂')
    (hcvar_ne : paretoCVaR l α p ≠ 0) :
    paretoPortfolioMean w₁ w₂ c₁ c₂ l α / paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = paretoPortfolioMean w₁' w₂' c₁' c₂' l α
        / paretoPortfolioCVaR w₁' w₂' c₁' c₂' l α p := by
  rw [paretoPortfolio_meanCVaR_ratio h_pos hcvar_ne,
      paretoPortfolio_meanCVaR_ratio h_pos' hcvar_ne]


end TailOptionPricing
