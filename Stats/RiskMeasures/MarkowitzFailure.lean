/-
  Risk measures & portfolio theory under Pareto.

  ## Stats.RiskMeasures.MarkowitzFailure — mean-CVaR frontier (Item 4).

  Two-asset Pareto under comonotone and independent dependence,
  abstract no-arbitrage feasibility.  Under strong Pareto with
  `α ≤ 2`, variance is infinite and the standard Markowitz
  variance-based framework collapses; the Mean-CVaR frontier
  provides a tail-aware substitute.

  See `Stats/RiskMeasures.lean` for the umbrella module.
-/
import Stats.RiskMeasures.CVaR
import Stats.RiskMeasures.Moments

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 4 — Markowitz failure / Mean-CVaR frontier.

    The classical Markowitz mean-variance objective requires finite
    second moments.  Under strong Pareto with `α ≤ 2`, variance is
    infinite (`variance_layerCake_not_integrable`), so the
    optimisation is ill-defined.  The Pareto-native replacement is
    Mean-CVaR.

    Without full multivariate distribution machinery, we work in the
    **comonotone factor model**: a single Pareto driver `S ~ Pareto(l,
    α)` with assets `S_i := c_i · S` for component loadings `c_i`.
    Under this model:

    * Portfolio mean scales linearly in the aggregate loading
      `w · c := w₁·c₁ + w₂·c₂` (positive homogeneity of the mean).
    * Portfolio CVaR scales linearly in `w · c` (by `paretoCVaR_scale`).
    * **The Mean-CVaR ratio is invariant in `(w₁, w₂)`** — every
      portfolio lies on a single line through the origin in the
      mean-CVaR plane.  Diversification yields no improvement; this is
      the comonotone version of the diversification-breakdown theorem.

    This captures the failure of risk-reduction in the presence of
    perfect tail dependence, which is the principal obstacle to
    Markowitz / Sharpe optimisation under Pareto. -/

/-- **Markowitz mean-variance is ill-defined for `α ≤ 2`.**  The
    layer-cake integrand of `Var(S)` (i.e. `s · survival l α s`) is
    not integrable on `(l, ∞)`.  Direct restatement of
    `variance_layerCake_not_integrable` in the portfolio-theory
    context. -/
theorem markowitz_objective_ill_defined {l α : ℝ}
    (hα_le : α ≤ 2) (hl : 0 < l) :
    ¬ IntegrableOn (fun s => s * survival l α s) (Ioi l) volume :=
  variance_layerCake_not_integrable hα_le hl

/-- **Comonotone portfolio mean.**  With weights `(w₁, w₂)` on assets
    `S_i = c_i · S` driven by `S ~ Pareto(l, α)`, the portfolio mean is
        E[w₁·S₁ + w₂·S₂] = (w₁·c₁ + w₂·c₂) · l · α / (α − 1).
    Derived from `paretoMoment` at `k = 1`. -/
noncomputable def paretoPortfolioMean (w₁ w₂ c₁ c₂ l α : ℝ) : ℝ :=
  (w₁ * c₁ + w₂ * c₂) * (α * l / (α - 1))

/-- **Comonotone portfolio CVaR.**  With weights `(w₁, w₂)` on
    comonotone components, portfolio CVaR equals
    `(w₁·c₁ + w₂·c₂) · paretoCVaR(l, α, p)`, since
    `w₁·S₁ + w₂·S₂ = (w₁·c₁ + w₂·c₂) · S` is itself Pareto with scale
    `(w₁·c₁ + w₂·c₂) · l`. -/
noncomputable def paretoPortfolioCVaR (w₁ w₂ c₁ c₂ l α p : ℝ) : ℝ :=
  (w₁ * c₁ + w₂ * c₂) * paretoCVaR l α p

/-- **Comonotone portfolio CVaR via the scale transformation.**  The
    portfolio is itself Pareto(`(w·c)·l`, `α`), so its CVaR can be
    computed via `paretoCVaR` at the rescaled location.  Algebraic
    consequence of `paretoCVaR_scale`. -/
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

    Pareto diversification-breakdown: under perfect tail dependence,
    no choice of weights improves the mean-to-risk ratio. -/
theorem paretoPortfolio_meanCVaR_ratio {w₁ w₂ c₁ c₂ l α p : ℝ}
    (h_pos : 0 < w₁ * c₁ + w₂ * c₂) (hcvar_ne : paretoCVaR l α p ≠ 0) :
    paretoPortfolioMean w₁ w₂ c₁ c₂ l α / paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = (α * l / (α - 1)) / paretoCVaR l α p := by
  unfold paretoPortfolioMean paretoPortfolioCVaR
  have h_pos_ne : (w₁ * c₁ + w₂ * c₂ : ℝ) ≠ 0 := h_pos.ne'
  field_simp

/-- **Positive homogeneity of the comonotone portfolio mean.**  Scaling
    weights by `λ` scales the mean by `λ`. -/
theorem paretoPortfolioMean_scale (lam w₁ w₂ c₁ c₂ l α : ℝ) :
    paretoPortfolioMean (lam * w₁) (lam * w₂) c₁ c₂ l α
      = lam * paretoPortfolioMean w₁ w₂ c₁ c₂ l α := by
  unfold paretoPortfolioMean
  ring

/-- **Positive homogeneity of the comonotone portfolio CVaR.**  Scaling
    weights by `λ` scales the CVaR by `λ`. -/
theorem paretoPortfolioCVaR_scale (lam w₁ w₂ c₁ c₂ l α p : ℝ) :
    paretoPortfolioCVaR (lam * w₁) (lam * w₂) c₁ c₂ l α p
      = lam * paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p := by
  unfold paretoPortfolioCVaR
  ring

/-- **Pareto-native efficient frontier is degenerate under comonotone
    factors.**  The frontier in Mean-CVaR space, parameterised by
    aggregate loading `m := w₁·c₁ + w₂·c₂`, is the line
        (paretoPortfolioMean = m · α·l/(α−1),
         paretoPortfolioCVaR = m · paretoCVaR(l, α, p))
    — slope independent of `m`.  Replacing variance with CVaR does
    not, by itself, restore diversification under perfect tail
    dependence; that requires `λ_U < 1` (Tier 5). -/
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
