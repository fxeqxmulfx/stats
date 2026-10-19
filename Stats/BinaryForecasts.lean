module

/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  Headline thesis: a binary payoff `θ_K(x) := 𝟙_{x ≥ K}` and a continuous
  payoff `g(x)` (e.g. `g(x) = x` or `max(x − K, 0)`) generate
  *different statistical objects* — they cannot be substituted for each
  other.  Concretely, the conflation
        I_1 := ∫_K^∞ g(x) · f(x) dx       (expected payoff)
        I_2 := g(K) · ∫_K^∞ f(x) dx       (binary substitution)
  is an identity for constant payoffs above `K`. A smooth nonnegative
  counterexample refutes Definition 5's fixed-density pointwise converse.
  A one-sided bound gives a corrected a.e. converse and a strict gap;
  see REVIEW.md, BF-09. For `g(x) = x` and a strong-Pareto density:
        I_1 / I_2 = α / (α − 1) > 1                    (Eq. 7)
  i.e., the binary substitution *systematically underestimates* the
  tail payoff by the multiplicative factor `α/(α − 1)`.

  Umbrella module — the formalisation is split into submodules:

  * `Stats.BinaryForecasts.CharacteristicScale` — Definition 4's actual
    Pareto conditional means, normalization, L1 and scale limit.
  * `Stats.BinaryForecasts.Conflation` — paper Definitions 5–6
    (`I_1`/`I_2`, Gaussian closed form, corrected probability `p*`).
  * `Stats.BinaryForecasts.ParetoSensitivity` — paper Eq. 9 and
    Remarks 1, 5 (Pareto sensitivity and inseparability).
  * `Stats.BinaryForecasts.Brier` — paper Theorem 2
    (measurable Brier averages and integrability of every nonnegative moment).
  * `Stats.BinaryForecasts.Bernoulli` — paper Appendix A
    (Bernoulli cumulants κ_3/κ_4 via cumulant-generating function).
  * `Stats.BinaryForecasts.Exponential` — paper Definition 4
    borderline case (exponential as borderline class).
  * `Stats.BinaryForecasts.ExponentialLaw` — Definition 4's actual
    conditional means, integrability, normalization and scale limits.
  * `Stats.BinaryForecasts.SigmaSensitivity` — paper Eq. 8 σ-derivation
    (polynomial positivity + full derivation).
  * `Stats.BinaryForecasts.SigmaClosures` — Eq. 8 integral closures
    via `stdNormalCdf` and Gaussian PDF.
  * `Stats.Probability.IntegralTransform` — Appendix B's probability
    integral transform, proved for the actual continuous-CDF law.
  * `Stats.BinaryForecasts.PayoffGap` and `ConflationCounterexample` —
    Definition 5's corrected a.e. converse, strict gap and counterexample.
-/
public import Stats.BinaryForecasts.CharacteristicScale
public import Stats.BinaryForecasts.Conflation
public import Stats.BinaryForecasts.ParetoSensitivity
public import Stats.BinaryForecasts.Brier
public import Stats.BinaryForecasts.Bernoulli
public import Stats.BinaryForecasts.Exponential
public import Stats.BinaryForecasts.ExponentialLaw
public import Stats.BinaryForecasts.SigmaSensitivity
public import Stats.BinaryForecasts.SigmaClosures
public import Stats.Probability.IntegralTransform
public import Stats.BinaryForecasts.PayoffGap
public import Stats.BinaryForecasts.ConflationCounterexample
public import Stats.BinaryForecasts.ConflationCounterexampleExamples

@[expose] public section
