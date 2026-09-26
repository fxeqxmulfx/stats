# TODO2 — Action items after strict review

Follow-up to `todo.md`.  This file lists *concrete next-step items*
ordered by effort/value, after the strict reviews of all six papers
revealed specific gaps and after the trading-framework discussion
clarified operational priorities.

## A. Quick wins (easy formalisation, paper-faithful)

### A.1. `Stats/Kappa.lean` — closing 1802.05495v3 gaps

Strict review revealed the following gaps; each is ~20-50 lines:

- [x] **`stableAlphaBar` (Eq. 5)** — piecewise definition
  `ᾱ := α·𝟙_{α<2} + 2·𝟙_{α≥2}`.  Trivially Lean.
- [x] **`cubicStudentDensity`** — definition `6√3/(π(x²+3)²)` (Eq. 8).
  Definitional; no theorem content.
- [x] **`gammaSumDensity`** — definition `λ^n·z^(n-1)·e^(-λz)/(n-1)!`
  (Eq. 14).  Connect to Mathlib's `gammaPDF`.
- [x] **`gaussianMixtureKurtosis` (Eq. 17)** — closed-form formula
  `Kurt = 3 − 2((μ₁-μ₂)^4 − 6(σ₁²-σ₂²)²) / ((μ₁-μ₂)² + 2(σ₁²+σ₂²))²`.
  Algebraic; ~30 lines.
- [x] **`gaussianMixtureKurtosis_ge_three_iff`** — condition
  `|μ₁-μ₂| ≤ ⁴√6·√(max(σ₁,σ₂)² − min(σ₁,σ₂)²)`.  Algebraic.
- [x] **P-class linkage** — formal `IsRegularlyVarying ↔ ParetoSurvival`
  to `Stats/RegularVariation/Application.lean` (mostly already in
  `survival_isRegularlyVarying`, just expose explicitly in
  `Kappa.lean` docstring / aux lemma).

### A.2. `Stats/BinaryForecasts.lean` — κ_3 done; add κ_4

- [x] **`bernoulli_kappa4`** — fourth cumulant `p(1−p)(1−6p(1−p))`.
  Mechanical chained `HasDerivAt` on ψ'''(t).  ~80 lines.
 
### A.3. `Stats/BlackScholes/Greeks.lean` (or new module) — Eq. 8 σ-derivation

- [x] **`gaussianEq8_sigmaSensitivity_eq`** — full σ-derivative
  derivation of `∂²(∫_K^∞ x·φ_σ(x)dx) − ∂²(∫_K^∞ φ_σ(x)dx))/∂σ²`
  yielding `e^(-K²/(2σ²))·((K-1)K³ - (K-2)Kσ²)/(√(2π)σ⁵)`.
  Both pieces formalised: (a) σ-derivative analytic content via
  closed forms `σ·φ(K/σ)` and `1 − Φ(K/σ)`
  (`gaussianEq8_sigmaSensitivity_eq` + `_phi` companion); (b)
  integral closures `∫_K^∞ x·φ_σ(x)dx = σ·φ(K/σ)` and
  `∫_K^∞ φ_σ(x)dx = 1−Φ(K/σ)` (`integral_x_gaussianPDF_σ`,
  `integral_gaussianPDF_σ`) via σ-parametric FTC.  ~300 lines total.

## B. Strategic additions (medium effort)

### B.1. Stirling-based asymptotic limits (1802.05495v3 Appendix A, C)

Both require `Real.Gamma` Stirling approximation from Mathlib:
`Real.log_gamma_asymp` or similar.

- [~] **`kappa_cubicStudent_asymptotic`**: paper claims
  `lim_{n→∞} log(n)·κ_{1,n} = π²/4`, but that has a missing `log`;
  the correct limit is `log(π²/4) = 2·log(π/2)`.

  Status: **algebraic derivation complete, Laplace asymptotic axiomatised.**
  * Final theorem `kappa_cubicStudent_asymptotic` proved (modulo axiom).
  * Stage 2 (`tendsto_log_incompleteGamma_minus_half_log`) + Stage 2b
    (with `−1` correction) fully proved from the Laplace asymptotic.
  * Stage 3 (algebraic κ-limit) fully proved.
  * `incompleteGamma_laplace_asymptotic` stated as an `axiom`:
    `Γ(n+1, n) / (n^n · e^{-n} · √n) → √(π/2)`.  Standard derivation
    (DCT on substitution `t = n + u·√n` with dominator `exp(1 − u/4)`),
    deferred — ~500-1000 lines of analytic Mathlib infrastructure.
    Surfaces in `#print axioms` as a dependency.
- [x] **`kappa_exponential_asymptotic`**: `lim_{n→∞} log(n)·κ_{1,n}
  = 4 − 2·log(2π)`.  Stirling-based, ~180 lines (Stages 1-4):
  * Stage 1 — `log n! − n·log n + n − ½·log n → ½·log(2π)`
    from `Stirling.tendsto_stirlingSeq_sqrt_pi`.
  * Stage 2 — translate to `log Γ(n)` via `Γ(n) = (n − 1)!`, with
    `m·log(1 + 1/m) → 1` correction.
  * Stage 3 — `(n·log n − n − log Γ(n) + 1) − ½·log n →
    1 − ½·log(2π)`.
  * Stage 4 — algebraic identity `log(n)·κ = 2c(n)·log(n)/D(n)` plus
    `log(n)/D(n) → 2` and `c(n) → 1 − log(2π)/2`.

### B.2. Hidden moment general-p mean (2004.05894v1)

- [ ] **`paretoHiddenMomentMean_exact`**: exact form
  `L^p · n · Γ(1-p/α) · Γ(n) / Γ(n+2-p/α)` via Beta(1,n) moment.
  Uses Mathlib `Real.Gamma`.  ~150 lines.
- [ ] **`paretoHiddenMomentMean_frechet_asymp`**: Fréchet asymptotic
  `L^p · n^(p/α−1) · Γ(1−p/α)` from above via Stirling.  Research-scale.

### B.3. Eq. 1 hidden-moment density (2004.05894v1)

- [ ] **`paretoHiddenMomentDensity_frechet`**: change-of-variable
  density of `μ_{K,p}(K_n)` under Fréchet K_n distribution.
  ~200 lines.

### B.4. Section VI Student-t emergence (1912.00277v2)

- [ ] **`normalGammaCompound_eq_studentT`**: closed-form integral
  `∫_0^∞ φ(x|λ)·Gamma(λ;α,β)dλ = Γ(α+½)/(Γ(α)√(2πβ))·(1 + x²/(2β))^(−α−½)`.
  Requires scaled-Gamma integral lemma `∫_0^∞ x^(s−1)·e^(−cx)dx = Γ(s)/c^s`
  via `MeasureTheory.integral_comp_mul_left_Ioi` substitution.  ~250 lines.

## C. Research-scale (deferred, no near-term action)

### C.1. Mathlib infrastructure prerequisites

- [ ] **α-stable distributions** in Mathlib — characteristic-function
  definition, scaling, sum-stability.  Currently absent.
  Foundation for: 1908.02347 Tier 6, 1912.00277 Eq. 13 (Lognormal
  precision), 1802.05495 Stable S-class.

- [ ] **Lyapunov / Lindeberg CLT** in `Stats/Kappa` or as Mathlib upstream.
  Needed for: 1912.00277 Eq. 11–13 (log λ → N(0, S²)).

- [ ] **Cumulant infrastructure** — `cumulant(X, k)` definition,
  cumulant generating function derivative chains.  Mathlib has MGF;
  no `cumulant`.  Needed for: 1802.05495 Appendix B (Lognormal κ_3, κ_4);
  1907.11162 Appendix A (Bernoulli κ_3, κ_4, kurtosis 3 − 6pq/Npq).

### C.2. Specific deferred items in each module

- **1908.02347**: Tier 5–8 of original research agenda (multivariate
  regular variation, stable Lévy, decision-theoretic survivability).
- **1802.05495**: Lognormal κ_{1,n}* with erf (Appendix B);
  Pearson IV closed form for `a_0, b_0, b_1, b_2`; polynomial
  expansions (Gram-Charlier, Lhermite).
- **1907.11162**: Eq. 4 exceedance probability with erfc (full
  measure-theoretic); Eq. 15 hypergeometric Brier characteristic
  function (`_2F_2`).
- **1912.00277**: Section VI Student-t emergence; Section V CLT step
  (`log λ → Lognormal`).
- **2004.05894**: Eq. 4 Gaussian hidden mean integral (requires
  erfc/Mills' ratio infrastructure).
- **2007.16096**: nothing further — paper is mostly policy.

## D. Project documentation & maintenance

- [ ] **Cross-reference paper equations** in theorem docstrings.
  Currently sporadic; should be systematic (e.g., every theorem
  starts with "Paper Eq. (X) / Theorem Y").
- [ ] **README.md** — top-level overview of module structure with
  paper ↔ module ↔ theorem-set mapping.
- [ ] **CI workflow** — GitHub Actions for `lake build` +
  `lake env lean Stats/Verify.lean`, with `grep sorryAx` gate.
- [ ] **Bump Mathlib** from `v4.29.0` to current.  Mathlib reorganises
  rapidly; v4.29 is several versions behind.  Mass-rewrite expected.
- [ ] **Generate doc-gen output** — `lake -K env=dev build Stats:docs`
  for HTML browsing of theorems.

## E. Trading-framework integration

Pattern documented in conversation; could be encoded as a `Strategies/`
module or appendix in `todo.md`.

### E.1. Class-A diagnostic functions (executable trading aids)

These are operationally useful as *functions to call from a trading
desk*, not just theorems.  All already formalised; just need an API
wrapper:

- [ ] **`market_implied_alpha (C_1, K_1, C_2, K_2)`** — wraps
  `alphaFromTwoAnchors` for immediate use on a vol surface.
- [ ] **`pareto_vs_bs_price_gap (K, α, σ_BS, S₀, T)`** — quantifies
  structural OTM mispricing.  Wraps
  `callPrice_eq` vs `callPriceBS_closed_form_riskNeutral`.
- [ ] **`binary_to_continuous_factor α`** — returns `α/(α−1)`.
  Wraps `pareto_I1_div_I2_eq` for prediction-market arbitrage sizing.
- [ ] **`sample_sufficiency (κ, n_g)`** — returns `n_g^(1/(1−κ))`.
  Wraps `n_nu` for backtest-validity assessment.
- [ ] **`pareto_cvar_multiplier α`** — returns `α/(α−1)`.
  Wraps `paretoCVaR_eq_conditional` for CVaR sizing.
- [ ] **`pareto_carrMadan_strip_cost (g'', a, b, l, α)`** — wraps
  `paretoCallStripCost_eq` and `paretoPutStripCost_eq` for static
  replication of bespoke payoffs.

### E.2. Class-B forbidden-operation guards

Decorator pattern: check distribution before running classical methods.

- [ ] **`assert_markowitz_valid (l, α)`** — requires `α > 2`; rejects
  via `markowitz_objective_ill_defined`.
- [ ] **`assert_dynamic_hedge_valid (l, α)`** — requires `α > 2` for
  gamma-P&L moment finiteness; rejects via
  `gammaPnL_constant_not_integrable`.
- [ ] **`assert_variance_swap_valid (l, α)`** — requires `α > 2`;
  rejects via `variance_layerCake_not_integrable`.
- [ ] **`assert_backtest_meaningful (κ, n)`** — rejects if
  `n^(1−κ) < threshold` (e.g., 30 Gaussian-equivalent).

### E.3. Strategy documentation (not formalisation per se)

- [ ] **`docs/barbell-strategy.md`** — concrete write-up linking
  formalised theorems to Universa-style tail-hedge strategy: long
  OTM puts, static replication, CVaR sizing.  Document *why* the
  theorems support this and *what* operational components remain
  user-discretion.
- [ ] **`docs/regime-detection.md`** — flowchart from
  market-implied-α to recommended sizing/hedging regime
  (Gaussian / borderline / fat-tail / extreme).

## F. Priority ranking

If we had to pick **5 items** for next sprint:

1. **A.1.x easy κ-paper closures** — get 1802.05495 to ~80% coverage.
2. **B.4 normal-Gamma → Student-t** — closes 1912.00277 last gap.
3. **E.1 trading-API wrappers** — translates theorems to usable functions.
4. **D.1 docstring cross-references** — improves maintainability.
5. **D.4 Mathlib bump** — keeps project alive long-term.

Items A.2 (κ_4 Bernoulli), B.1 (Stirling asymptotics), B.3 (hidden
moment density), and C (α-stable, CLT) are nice-to-have but high-effort
or research-scale.

## G. What we explicitly will NOT formalise

These are out-of-scope decisions (informal / qualitative / policy):

- All "Remarks", "Comments", "Discussion" sections in any paper.
- Empirical fits (Tables I-III of any paper, Zipf plots).
- Policy/qualitative arguments (1907.11162 Main Statements,
  2007.16096 most of the paper).
- Numerical examples beyond sanity-check spot values.
- Counterexample exhibitions (e.g., `IsSlowlyVarying.comp_translation`
  without measurability).
- Recipe-style "how to fit α to S&P 500" empirical methodology.

## Status snapshot (as of last build)

- **6/6 papers**: formal mathematical kernel covered.
- **222 theorems** verified axiom-clean.
- **~12k lines** across `Stats/`.
- **Build**: green (`lake build` 2850 jobs).
- **Verify**: no `sorryAx`; only `[propext, Classical.choice, Quot.sound]`.

After A.1–A.3 + B.4, would reach ~250 theorems and ~95% headline-claim
coverage across all six papers.
