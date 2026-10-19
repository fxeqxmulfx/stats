module

/-
  Umbrella module for the formalization of
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  The development is split across the following sub-modules. Entries
  list mathematical ingredients, not complete paper formalizations;
  see REVIEW.md for the statement-by-statement assessment.

    Stats/Pareto.lean       — strong-Pareto core; Results 1, 2, 3 (Eqs. 2–7)
                              + calibration formula (Section II.B inversion).
    Stats/Theorem1.lean     — `IsRegularlyVarying` class; Theorem 1
                              (log returns NOT in `RV_α`), strong-Pareto and
                              Karamata-constant versions.
    Stats/RegularVariation.lean — measurable slowly varying theory,
                              full log-return theorem and call asymptotics.
    Stats/Pareto/Measure.lean — the supported Pareto probability measure.
    Stats/Copula/Basic.lean — generic copula ingredients.
    Stats/Calculus.lean     — generic FTC for `K ↦ ∫_K^∞ F(s) ds`;
                              Breeden–Litzenberger 1st/2nd derivatives;
                              continuity on `Ici l`; strict convexity on
                              `Ioi l` and `Ici l`; pure-PL butterfly bound.
    Stats/Arbitrage.lean    — abstract Eqs. (8)–(10): matched-butterfly
                              ⇒ derivative comparison ⇒ tail dominance ⇒
                              lower bound on `α`.
    Stats/LayerCake.lean    — bridge to expectation form:
                              `E[(S − K)⁺] = ∫_K^∞ ℙ(S > s) ds`.
    Stats/BlackScholes.lean — concrete lognormal Black–Scholes: `survivalLN`,
                              standard normal CDF `stdNormalCdf`, location-
                              scale, Markov tail bound, integrability, and the
                              final unconditional dominance theorem.
    Stats/CarrMadan.lean    — finite-strip Carr–Madan static-replication
                              identity for `C²` payoffs.
    Stats/RiskMeasures.lean — risk-expression identities, spectral and
                              moment integrals, portfolio/max-tail formulas,
                              pointwise Kelly derivatives and MLE candidates;
                              optimization and estimator-law bridges remain.
    Stats/Hedging.lean      — hedging under fat tails: gamma-P&L
                              distribution, Pareto-priced static replication,
                              and K-decay rates of Greeks (Pareto vs BS).
    Stats/Kappa.lean        — Taleb's κ-metric (arXiv:1802.05495v3): abstract
                              MAD interface and scaling algebra, additive
                              decomposition, supplied exponential/Gamma and
                              cubic Student MAD expressions, incomplete-Gamma
                              analysis, genuine Loulakis lognormal limit,
                              and sample-size power identities. Several
                              distributional MAD bridges remain unproved.
    Stats/BinaryForecasts.lean — binary vs. continuous payoff conflation
                              (arXiv:1907.11162v3): characteristic scale,
                              I_1/I_2 conflation identity, Pareto closed
                              form α/(α − 1), Pareto sensitivity 2K/(α−1)³,
                              Gaussian tail integral, corrected probability
                              p*, inseparability via Jensen, Brier-score
                              boundedness, Bernoulli cumulants.
    Stats/EpistemicUncertainty.lean — branching epistemic uncertainty
                              (arXiv:1912.00277v2): binomial-tree moment
                              factor M_k(ε), weighted scale second/fourth
                              moments, actual finite recursive Gaussian
                              population and outcome moments, actual
                              kurtosis inequalities and symmetry,
                              constant-error point-mass weak limit,
                              whole-law binomial Gaussian collapse,
                              decaying-error product bounds,
                              log-additivity of multiplicative errors.
    Stats/HiddenMoments.lean  — hidden moments of a probability distribution
                              (arXiv:2004.05894v1): Pareto p-th tail moment
                              closed form α·L^α·K^(p−α)/(α−p) (Eq. 2);
                              actual finite iid maximum law and the hidden
                              population mass's supported Beta(1,n) CDF and
                              mean 1/(n+1), exact general-p hidden-moment
                              pushforward, Gamma-ratio expectation and its
                              asymptotic, distribution-free hidden mass for
                              continuous-CDF populations and the scaled
                              exponential weak limit;
                              certificates refute the finite-sample
                              exponential law and necessary underestimation
                              of the arithmetic sample mean.
    Stats/SinglePointForecasts.lean — single-point forecasts for fat-tailed
                              variables (arXiv:2007.16096v1): actual supported
                              exponential-growth/Pareto law; unbiased iid
                              empirical survival with exact MSE p(1-p)/n and
                              RMSE bound 1/(2√n); actual Pareto and Bernoulli
                              counterexamples to the printed o(1/n) rate;
                              strong-Pareto first-moment threshold.

  Two paper typos found and the corrected formulas formalised:
    • Eq. (7): `(K − S₀)^(1−α)` → `(S₀ − K)^(1−α)`, `S₀^(1−α)` → `S₀^(−α)`.
    • Eq. (9): printed `∂BSC/∂K ≥ ∂C/∂K` is the wrong direction; we formalise
      the consistent `C′(K₁) ≥ BSC′(K₁)`, which gives the lower-bound form
      of Eq. (10).
-/
public import Stats.Pareto
public import Stats.Theorem1
public import Stats.Calculus
public import Stats.Arbitrage
public import Stats.LayerCake
public import Stats.BlackScholes
public import Stats.CarrMadan
public import Stats.RiskMeasures
public import Stats.Hedging
public import Stats.Kappa
public import Stats.BinaryForecasts
public import Stats.EpistemicUncertainty
public import Stats.EpistemicUncertainty.BranchingKurtosis
public import Stats.EpistemicUncertainty.BranchingLimits
public import Stats.EpistemicUncertainty.ScaleLaw
public import Stats.EpistemicUncertainty.FractionalMoments
public import Stats.EpistemicUncertainty.ScaleConcentration
public import Stats.EpistemicUncertainty.OutcomeLimit
public import Stats.EpistemicUncertainty.BinomialCollapse
public import Stats.EpistemicUncertainty.BinomialDensity
public import Stats.EpistemicUncertainty.BinomialSurvival
public import Stats.HiddenMoments
public import Stats.SinglePointForecasts
public import Stats.RegularVariation
public import Stats.Pareto.Measure
public import Stats.Copula.Basic

@[expose] public section
