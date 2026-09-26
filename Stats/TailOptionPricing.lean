/-
  Umbrella module for the formalization of
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  The development is split across the following sub-modules:

    Stats/Pareto.lean       — strong-Pareto core; Results 1, 2, 3 (Eqs. 2–7)
                              + calibration formula (Section II.B inversion).
    Stats/Theorem1.lean     — `IsRegularlyVarying` class; Theorem 1
                              (log returns NOT in `RV_α`), strong-Pareto and
                              Karamata-constant versions.
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
    Stats/RiskMeasures.lean — Pareto-native risk measures and portfolio
                              theory: CVaR / spectral / moment-finiteness /
                              Mean-CVaR frontier / drawdown / Kelly / MLE-CI.
    Stats/Hedging.lean      — hedging under fat tails: gamma-P&L
                              distribution, Pareto-priced static replication,
                              and K-decay rates of Greeks (Pareto vs BS).
    Stats/Kappa.lean        — Taleb's κ-metric (arXiv:1802.05495v3): abstract
                              definition, stable-basin invariance κ = 2 − ᾱ,
                              Gaussian/Cauchy special cases, additive
                              decomposition, exponential/Gamma closed form,
                              cubic Student T closed form via local
                              incomplete-Gamma, Loulakis' lognormal bound,
                              and the n_ν sample-size approximation.
    Stats/BinaryForecasts.lean — binary vs. continuous payoff conflation
                              (arXiv:1907.11162v3): characteristic scale,
                              I_1/I_2 conflation identity, Pareto closed
                              form α/(α − 1), Pareto sensitivity 2K/(α−1)³,
                              Gaussian tail integral, corrected probability
                              p*, inseparability via Jensen, Brier-score
                              boundedness, Bernoulli cumulants.
    Stats/EpistemicUncertainty.lean — branching epistemic uncertainty
                              (arXiv:1912.00277v2): binomial-tree moment
                              factor M_k(ε), variance σ²·(1+ε²)^n, 4th
                              moment 3σ⁴·(1+6ε²+ε⁴)^n, kurtosis ≥ 3 (strict
                              for ε ≠ 0), decaying-error variance product,
                              log-additivity of multiplicative errors.
    Stats/HiddenMoments.lean  — hidden moments of a probability distribution
                              (arXiv:2004.05894v1): Pareto p-th tail moment
                              closed form α·L^α·K^(p−α)/(α−p) (Eq. 2);
                              exact distribution of sample survival ratio
                              `(L/K_n)^α ~ Beta(1, n)` with mean 1/(n+1),
                              correcting paper's Fréchet-asymptotic 1/n.
    Stats/SinglePointForecasts.lean — single-point forecasts for fat-tailed
                              variables (arXiv:2007.16096v1): exponential
                              growth → Pareto density `X₀·exp(r·t)` with
                              r ~ Exp(λ) ⇒ Pareto(X₀, λ/t); tail
                              index/variance relation α = 1/(t·√Var(r));
                              empirical-survival std bound 1/(2√n) via
                              Bernoulli p(1−p) ≤ 1/4; Pareto mean diverges
                              at α ≤ 1 (Remark 3).

  Two paper typos found and the corrected formulas formalised:
    • Eq. (7): `(K − S₀)^(1−α)` → `(S₀ − K)^(1−α)`, `S₀^(1−α)` → `S₀^(−α)`.
    • Eq. (9): printed `∂BSC/∂K ≥ ∂C/∂K` is the wrong direction; we formalise
      the consistent `C′(K₁) ≥ BSC′(K₁)`, which gives the lower-bound form
      of Eq. (10).
-/
import Stats.Pareto
import Stats.Theorem1
import Stats.Calculus
import Stats.Arbitrage
import Stats.LayerCake
import Stats.BlackScholes
import Stats.CarrMadan
import Stats.RiskMeasures
import Stats.Hedging
import Stats.Kappa
import Stats.BinaryForecasts
import Stats.EpistemicUncertainty
import Stats.HiddenMoments
import Stats.SinglePointForecasts
