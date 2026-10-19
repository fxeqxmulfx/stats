# TODO — Pareto-native statistical inference (Taleb fat-tails project)

Current coverage is assessed in [REVIEW.md](REVIEW.md); declarations and
compiled-proof markers are listed in [INDEX.md](INDEX.md). The planning
items below include historical completion claims. A checked formula does
not establish its probability-law interpretation, and none of the six
papers is fully formalized under the current review criteria.

A Lean 4 / Mathlib formalisation of several papers from Taleb's
fat-tails / statistical-consequences-of-fat-tails project, with a
unified Pareto-native infrastructure for option pricing, calibration,
risk measures, and tail-sensitive statistical inference.

## Status

- The default `lake build` and exhaustive transitive `./run.py audit`
  pass with only `propext`, `Classical.choice` and `Quot.sound`.
- See the generated index for current module/theorem counts and compiled
  sorry, vacuous and placeholder markers.
- These checks validate the written Lean statements; the claim registry
  in `REVIEW.md` records remaining probability and paper-coverage gaps.

## Paper coverage

| Paper | Lean module(s) | Status |
|---|---|---|
| **1908.02347v3** — Tail Option Pricing Under Power Laws | `Pareto`, `Calculus`, `Arbitrage`, `Theorem1`, `LayerCake`, `BlackScholes/*`, `CarrMadan` | Corrected analytic core and returns-tail smile bound; full paper coverage incomplete |
| **1802.05495v3** — A pre-asymptotic metric for fat-tailedness (κ) | `Kappa` | Abstract algebra and actual Loulakis limit; several MAD/sum-law bridges incomplete |
| **1907.11162v3** — Binary forecasts vs real-world payoffs | `BinaryForecasts` | Integral/derivative identities and actual Theorem 2; general Theorem 1 and CLTs incomplete |
| **1912.00277v2** — Branching epistemic uncertainty | `EpistemicUncertainty` | Weighted scale-moment algebra; outcome-mixture law and limiting results incomplete |
| **2004.05894v1** — Hidden moments of a probability distribution | `HiddenMoments` | Tail-moment integral and candidate Beta function identities; maximum/pushforward laws incomplete |
| **2007.16096v1** — Single-point forecasts for fat-tailed variables | `SinglePointForecasts` | Actual exponential-growth law and empirical-survival MSE/RMSE; general limits and risk models incomplete |

## Paper typos found and corrected

All from arXiv:1908.02347v3:

- **Eq. (7)** — two errors. `(K − S₀)^(1−α)` for puts (`K < S₀`)
  is a negative base raised to a non-integer power (ill-defined); and
  `S₀^(1−α)` should be `S₀^(−α)`.  Corrected form verified numerically
  (`S₀ = 2, α = 2, l = 0.1, K = 1`: paper gives `−2.5`, corrected gives
  `0.01`).  Encoded in `putRaw_eq`.
- **Eq. (9)** — wrong direction.  Paper writes `∂BSC/∂K ≥ ∂C/∂K`;
  Eq. (8) actually implies `∂C/∂K ≥ ∂BSC/∂K`.  Encoded in
  `callPrice_dominates_BSC_deriv`.
- **Section III λ-formula** — `1/((−1)^(α+1)(l^α − 1))` for non-integer
  `α` is ill-defined; the rigorous form is `1/(1 − l^α)` (via
  `densityMass_eq`).

## Beyond-paper extensions

- **Within-density put–call parity** (`putShadow`,
  `putCallParity_Pareto`, `putCallParity_Pareto_returns`,
  `putCallParity_Pareto_riskNeutral`).
- **Breeden–Litzenberger for the shadow put** (`putShadow_hasDerivAt`,
  `_secondOrder`, `_deriv_eq_one_sub_survival`).
- **VaR / CVaR / tail expectation** (`paretoVaR`, `paretoCVaR`,
  `paretoTailExpectation`, `paretoCVaR_eq_conditional`).
- **Abstract pricing functional + Pareto envelope**
  (`callPrice_F`, `callPrice_envelope_upper`).
- **Pareto Greeks** (`callPrice_hasDerivAt_{l,alpha}`,
  `putShadow_hasDerivAt_{l,alpha}`).
- **Multi-anchor calibration** (`alphaFromTwoAnchors`,
  `lFromTwoAnchors`, `callPrice_param_inj`).
- **Term structure under stable scaling**
  (`callPriceReturns_T_eq`, `_hasDerivAt`, `_calendarSpread`).
- **Risk measures & portfolio theory** (`Stats/RiskMeasures.lean`):
  spectral risk measures, moment-finiteness biconditional,
  Markowitz/Mean-CVaR degeneracy under comonotone factors,
  drawdown / Kelly / MLE-CI for tail index.
- **Hedging under fat tails** (`Stats/Hedging.lean`): squared-return
  Pareto-survival identity, gamma-P&L moment biconditional,
  Pareto-priced Carr–Madan static replication, Pareto Vega
  divergence vs BS-Vega super-exponential decay.

## Open / deferred items

### Tier A — Tractable (no Mathlib gaps)

- **Bernoulli κ_3, κ_4** higher cumulants — chained quotient-rule
  `HasDerivAt`s on `bernoulliCGF`.  κ_3 done in `BinaryForecasts`;
  κ_4 (`p(1−p)(1−6p(1−p))`) is ~80 lines of mechanical derivative
  algebra.
- **Eq. 4 exceedance probability** for `EpistemicUncertainty`
  (paper 1912.00277v2):  closed-form sum of erfc terms; requires
  binomial-coefficient sum manipulation but no measure theory.
- **Eq. 8 Gaussian σ-sensitivity derivation** (paper 1907.11162v3):
  full σ-derivative of `∫_K^∞ x·φ_σ(x) dx − K·∫_K^∞ φ_σ(x) dx`.
  Polynomial-positivity (sign of result) is formalised
  (`gaussian_eq8_polynomial_pos`); the *derivation* from σ-parametric
  Gaussian tail integrals is research-scale.
- **Tier 1–9 research agenda** below — items still feasible without
  new Mathlib infrastructure.

### Tier B — Research-scale (require new Mathlib infrastructure)

- **CLT machinery** — needed for:
  - Lyapunov / Lindeberg CLT in `Kappa.lean` (paper 1802.05495).
  - CLT step Eq. 11–13 in `EpistemicUncertainty.lean`
    (`log λ → N(0, S²)`, paper 1912.00277v2).
  - Generalised CLT for α-stable limits (paper 1908.02347 tier 6).
- **α-stable distributions** — characteristic-function definition,
  scaling, sum-stability.  Currently absent from Mathlib.
- **Domain of attraction characterisation** — bridges
  `Stats/RegularVariation` to α-stable limit laws.
- **Hill estimator** — non-parametric tail-index estimator.
  Consistency and asymptotic normality require α-stable + Hill-process
  machinery.
- **Multivariate regular variation** — `RV(α, μ)` class with limit
  measure `μ` on the unit sphere.  Foundation for tail-dependence,
  basket options, diversification-breakdown.
- **Stable Lévy processes** — for barrier / Asian / American options
  under α-stable underlying.  Depends on α-stable + Lévy–Khintchine.

### Specific deferred theorems

- **Section VI Student-t emergence** (paper 1912.00277v2 Eq. 14–15):
  Normal-Gamma compound `∫_0^∞ φ(x|λ)·Gamma(α, β)(λ) dλ
   = Γ(α+½)/(Γ(α)√(2πβ)) · (1 + x²/(2β))^(−α−½)`.
  Requires the scaled Gamma integral `∫_0^∞ λ^(s−1) e^(−cλ) dλ
   = Γ(s)/c^s` (substitution `u = cλ` on `Real.Gamma_eq_integral`).
- **Mills' lower bound** for Gaussian asymptotic: `(1 − Φ(K)) ≥
  φ(K)·K/(K² + 1)` (or similar), needed for the thin-tailed
  `E[X|X>K]/K → 1` limit (paper 1907.11162 Def. 4 D_1 case).
- **Jensen-strict inseparability for non-affine `g`** (paper
  1907.11162 Remark 5):  requires a concrete probability-measure
  structure on the density `f`, not currently in our abstract
  framework.
- **Theorem 1 cubic-Student asymptotic `log(n)·κ → π²/4`** (paper
  1802.05495 Appendix A):  requires Stirling-style asymptotic
  analysis of the incomplete-Gamma evaluation `Γ(n+1, n)` as
  `n → ∞`.  Algebraic but tedious.
- **Exponential asymptotic `log(n)·κ → 4 − 2 log(2π)`** (paper
  1802.05495 Section III.C): Stirling on `Γ(n)`.

## Pareto-native research agenda (Tiers 1–9)

Beyond direct paper coverage, the following structural tiers extend
the Pareto-native infrastructure to a complete fat-tail-aware
mathematical-finance library.  Each tier ordered by closeness to
current code; within tiers, by value/effort.

### Tier 1 — Closure of current call/put development

Mostly done:

- [x] **BL for `putShadowReturns`** — `putShadowReturns_hasDerivAt{,_secondOrder}`.
- [x] **Strict convexity of `putShadow{,Returns}`** —
  `putShadow_strictConvexOn`, `putShadowReturns_strictConvexOn`.
- [x] **Boundary continuity** — `putShadow_continuousOn_Ici`.
- [x] **Pareto Greeks** — `callPrice_hasDerivAt_{l,alpha}`,
  `putShadow_hasDerivAt_{l,alpha}`.

### Tier 2 — Pricing & calibration extensions

Mostly done:

- [x] **Multi-anchor calibration** with sensitivity bounds.
- [x] **Mispricing signal** — `BSC − callPrice` decays only relatively
  (formalised via Mills + Pareto envelope).
- [x] **Pareto envelope** (upper & lower bounds).
- [x] **Term structure** under `α`-stable scaling.
- [x] **Variance-swap breakdown** (`variance_layerCake_not_integrable`).
- [x] **Static-replication identity (Carr–Madan)** — `Stats/CarrMadan.lean`.
- [x] **No-arb bounds across strikes** — vertical, butterfly,
  Lipschitz slope.

### Tier 3 — Risk measures & portfolio theory (`Stats/RiskMeasures.lean`)

Done:

- [x] **CVaR risk-measure properties** (monotonicity, scaling,
  CVaR ≥ VaR).
- [x] **Spectral risk measures** — `M_φ` family.
- [x] **Moment-finiteness biconditional** `E[S^k] < ∞ ⟺ α > k`.
- [x] **Markowitz failure / Mean-CVaR frontier** (degeneracy under
  comonotone Pareto).
- [x] **Drawdown / sample-max distribution** under iid Pareto returns.
- [x] **Kelly criterion** — pointwise concavity ingredients.
- [x] **Confidence intervals for `α̂`** — MLE asymptotic variance
  `α²/n`.

### Tier 4 — Hedging under fat tails (`Stats/Hedging.lean`)

Done:

- [x] **Dynamic-hedging P&L distribution** — squared-return Pareto
  survival; gamma-P&L moment biconditional.
- [x] **Static replication of `g(S_T)`** under Pareto pricing.
- [x] **K-decay rates of Greeks** — Pareto Vega vs BS Vega divergence.

### Tier 5 — Multi-asset / dependence

Open (research-scale, depends on Tier B):

- [ ] **Multivariate regular variation** — `RV(α, μ)` class.
- [ ] **Tail dependence coefficient** `λ_U` with closed forms under
  common copulas.
- [ ] **Diversification-breakdown theorem** under asymptotic tail
  dependence.
- [ ] **Basket option pricing** — multivariate Pareto.
- [ ] **Spread option** — bivariate Pareto.

### Tier 6 — Distributional infrastructure (Mathlib-adjacent)

Open (research-scale):

- [ ] **α-stable distributions** — characteristic-function definition,
  scaling, sum-stability.
- [ ] **Generalised CLT** for iid sums in α-stable basins.
- [ ] **Domain of attraction characterisation** — bridges
  `RegularVariation` to limit theorems.
- [ ] **Hill estimator** — consistency, asymptotic normality.
- [ ] **Subexponential class** — closure of survival sums.

### Tier 7 — Path-dependent options & stable Lévy processes

Open (research-scale, depends on Tier 6):

- [ ] **Stable Lévy process** — increments are α-stable; constructed
  via Lévy–Khintchine.
- [ ] **Reflection principle** for symmetric stable Lévy (Spitzer /
  Baxter identities).
- [ ] **Barrier / Asian / American options** under stable Lévy.

### Tier 8 — Decision theory / ergodicity

Open:

- [ ] **Time-average vs ensemble** — Birkhoff for stationary Pareto;
  counterexample for non-stationary.
- [ ] **Non-ergodic Kelly** — `f*` differs between time / ensemble
  formulations.
- [ ] **Survivability constraint** — `ℙ(min_{t ≤ T} W_t > 0) ≥ 1 − ε`
  as hard constraint.
- [ ] **Bayesian update of `(α, l)`** — posterior; conjugate priors.
- [ ] **Sharpe-ratio unreliability theorem** — sample Sharpe →
  degenerate 0 a.s. for `1 < α < 2`.

### Tier 9 — Tooling / maintenance

- [x] **`#print axioms` for all paper-derived theorems**
  (208 entries in `Stats/Verify.lean`).
- [ ] **Docstring cross-references** — link each theorem to its paper
  equation / page where applicable.
- [ ] **CI workflow** — `lake build` + `lake env lean Stats/Verify.lean`,
  with `grep sorryAx` as gate.
- [ ] **README** — file structure and equation ↔ theorem map.
- [ ] **Bump Mathlib** (currently `v4.29.0`).

## Out of scope (paper content not formalisable as theorems)

- **Figures** — illustrative or empirical S&P 500 fits, simulation
  plots.
- **Remarks** — informal commentary.
- **Numerical examples** — Table I–III empirical comparisons.
- **`IsSlowlyVarying.comp_translation`** without measurability — not a
  theorem (pathological non-measurable counterexamples exist).
- **Verbal/policy commentary** — paper Sections labelled "Comments",
  "Conclusion", etc.

## Future work (other Taleb papers)

- *Statistical Consequences of Fat Tails* (book) — multiple chapters
  formalisable: PSR (Probabilistic Sharpe Ratio), median-mean
  divergence, "Twitter problem" for sample-based inference,
  alpha-stable composition.
