# Review of the Taleb paper formalizations

Initial review: 2026-10-01. Review renewed: 2026-10-19.
Project: Stats, Lean 4 and mathlib.
The review uses the specific paper versions stored in `papers/`.

## Which papers are fully formalized?

**None of the six papers is fully formalized under a statement-by-statement,
probabilistic interpretation of completeness.**
The corrected mathematical core of **Tail Option Pricing Under Power Laws**
has the strongest coverage. Its call formulas, calibration, relative prices,
corrected put integral, convexity, and log-return theorem are proved.
The final returns-tail bound now follows from an actual differentiable
volatility smile, matching prices and the local butterfly condition.
Global consistency of an arbitrary central-model/tail splice remains separate.

| Paper and reviewed version | Complete? | Established coverage | Main remaining gap |
| --- | --- | --- | --- |
| [Tail Option Pricing Under Power Laws, 1908.02347v3](https://arxiv.org/abs/1908.02347v3) | **not ok** | Corrected analytic core, returns-tail smile bound, slowly varying log-return theorem and call asymptotics | General-tail versus exact-tail interpretation, literal source errors and empirical claims |
| [How Much Data Do You Need?, 1802.05495v3](https://arxiv.org/abs/1802.05495v3) | **not ok** | Abstract κ algebra, corrected minimum-size and finite-Beta expressions, special-function identities, genuine probabilistic Loulakis lognormal limit | Distributional MAD/sample-size bridges; finite-sum law identifications; proxy limits |
| [On the Statistical Differences between Binary Forecasts and Real World Payoffs, 1907.11162v3](https://arxiv.org/abs/1907.11162v3) | **not ok** | Pareto and exponential cases, Gaussian integrals and sensitivities, probabilistic Theorem 2, Bernoulli CGF derivatives | General Theorem 1, CLT and appendices |
| [Branching epistemic uncertainty and thickness of tails, 1912.00277v2](https://arxiv.org/abs/1912.00277v2) | **not ok** | Binomial scale-moment calculations and algebraic kurtosis inequalities | Gaussian-mixture moment bridge, infinite limits, CLT and Normal–Gamma mixture |
| [What You See and What You Don't See: The Hidden Moments of a Probability Distribution, 2004.05894v1](https://arxiv.org/abs/2004.05894v1) | **not ok** | Deterministic tail-moment integral and Beta(1,n) function identities | Main Proposition 1, actual iid maximum law, asymptotics and Gaussian comparison |
| [On Single Point Forecasts for Fat-Tailed Variables, 2007.16096v1](https://arxiv.org/abs/2007.16096v1) | **not ok** | Actual exponential-growth/Pareto law, exact empirical-survival variance and MSE, corrected RMSE bound and a heavy-tailed rate counterexample, strong-Pareto moment threshold | General moment boundary, LLN/CLT and formal risk or policy models |

## Meaning of ok and not ok

- **ok** means the claim identified in that entry is proved, with its mathematical
  scope and necessary hypotheses stated.
- **not ok** means the paper's claim is not completely established. This can mean
  an absent proof, a strict special case, a formula supplied by definition,
  an essential conclusion supplied as a hypothesis, or an error in the paper.

The status applies to the claim in the entry heading. A literal erroneous paper
claim and its corrected mathematical version receive separate assessments.
A paper-coverage failure is not a failure of Lean's kernel.

Successful compilation establishes the **written Lean statement**. It does not
establish that the statement faithfully represents the paper. In particular,
defining a function `M : ℕ → ℝ` by a closed expression does not prove

```text
M(n) = E|X₁ + … + Xₙ − E(X₁ + … + Xₙ)|.
```

Definitions are assessed for correspondence and for the bridges required by
later claims, rather than as propositions needing proofs.

Every active, explicitly named theorem, proposition and result in these six
LaTeX sources is assessed below. The review also covers definitions, mathematical
remarks, unnumbered equations, table claims and relevant asymptotics.
Commented-out LaTeX environments are excluded. Empirical and normative claims
are identified separately: absence of a Lean model does not establish their
falsehood.

## Renewed review: first batch (2026-10-19)

This starts a new pass using the Transformer review procedure: compare the
written statement and every substantive definition with the source, compile
the certificates, inspect their axioms, and record the remaining probability
bridges. This batch covers the seven existing diagnostics in
[Stats/ReviewChecks.lean](Stats/ReviewChecks.lean), the three reference-curve
theorems and the sample-size expression in
[Stats/Kappa/Basic.lean](Stats/Kappa/Basic.lean), and their descriptions in
`kappa.py`. It is not a new complete review of all 593 named theorems.

Reread `papers/arXiv-1802.05495v3/kappa-n-final.tex`: Table I's Pareto entry
and incomplete-Beta footnote (line 209), Definition 1 (lines 272–287),
**Equivalence for stable distributions** (lines 342–353), and **Practical
significance for sample sufficiency**, displays `md` and `simpleequiv`
(lines 389–397). These are the source locations for K07–K11 and K14 below.

| Checked claim | Assessment in this batch |
| --- | --- |
| Pareto Beta/ratio/κ diagnostics | **ok** as certificates about the historical definitions. Separate divergent Beta integrals gave zero ratio and κ = 2. Repair 2 below replaces that expression; the old certificates now explicitly target the isolated legacy model. They do not refute a correctly defined probabilistic κ. |
| Historical zero-size minimum | **ok** as a certificate of the old repository bug. The paper already requires positive size. The existing zero-MAD and unit-MAD regression theorems check the repaired definition on synthetic functions. |
| Power, square-root and linear reference curves | **Fixed descriptions:** all three theorems assume `hM_form`. Their parameters are satisfiable, but those witnesses do not establish an iid-sum law. The linear case is not a Cauchy finite-MAD theorem. The paper's finite-mean interpretation needs stable index greater than 1. |
| Proposed sample-size power formula | **Fixed descriptions:** `n_nu` is the supplied power expression from `simpleequiv`, not a proved minimum or a variance-matching theorem. **Issue remains:** identification with the integer criterion `md`, and an approximation-error bound. |
| Singular κ = 1 | **ok** as a boundary diagnostic: Lean's total `n_nu 30 1` is 1. Python returns infinity by convention at κ ≥ 1; its documentation now states this difference and restricts its round-trip interpretation to κ < 1. |
| Finite-grid layer-cake estimator | **Fixed descriptions:** the absolute-tail integral and the centered positive-tail Lean theorem are distinguished. Finite-grid quadrature need not have the direct empirical MAD's expected value. No numerical algorithm or tolerance was changed. |

Ten new Lean examples instantiate the hypotheses with `α = 2`, `z = 1/2`,
`y = 0`, a nonnegative unit-MAD baseline, and explicit square-root, linear
and power reference curves. They also check the κ = 0 sample-size identity
and the κ = 1 boundary value. Together with the two existing concrete
minimum-size certificates, these exercise the definitions without adding
distributional assumptions or asserting that synthetic curves are actual MADs.
The outstanding gaps in K07–K11 and K14 remain open.

Verification for this batch: `lake build Stats.ReviewChecks` compiled the ten
new examples and printed the axioms of all seven diagnostic theorems; only
`propext`, `Classical.choice` and `Quot.sound` occur. The default `lake build`
passed all 3892 jobs without warnings or errors. `./make.py audit` again
covered 1279 declarations (1096 theorem declarations), with zero non-core
axioms. `./make.py forbidden` passed, and `./make.py test` passed all 27 tests
without skips. Comparing Python syntax trees after removing docstrings
confirms that executable numerical code is unchanged.
`./make.py index` regenerated 105 modules and 593 named theorems with zero
sorry, vacuous or placeholder markers. After `dt refresh project`, all 670
previously indexed public names and their elaborated types are unchanged.

## Full review and repair loop (2026-10-19)

The renewed pass now follows the entire claim registry, repairs issues in
small commits, and rechecks the source and certificates after each repair.
Incomplete distributional bridges remain issues until proved; a supplied
formula is not accepted as the missing probability theorem.

### Repair 1: the actual returns-tail smile bound and a sign counterexample

Reread `papers/arXiv-1908.02347v3/OptionPricingPL2022.tex`, section
**Arbitrage Boundaries**, display `arbitrage`, its following derivative
inequality and the final unnumbered display. The printed `BSC' ≥ C'` is
incorrect. The new `exists_returns_smile_parameters` constructs matching
Pareto-returns and genuine Black--Scholes call curves with a nonconstant
smile. Their local mixed butterfly is nonnegative but `BSC' < C'`.
The strictness provides a counterexample to the printed direction under
the source's own matching and butterfly conditions.

[BlackScholes/ReturnsSmile.lean](Stats/BlackScholes/ReturnsSmile.lean)
now derives the negative smile derivative from `HasDerivAt σ σ' K`,
uses annual volatility times `sqrt t`, and proves the final index bound
with denominator `log (l * S₀ / (K - S₀))`. The paper's displayed Gaussian
term is kept as its normalized PDF; `bsSmileDigital_eq_erfc` proves the
equivalent `erfc` form. `bsSmileDigital` is explicitly a derivative
expression, without asserting a probability law for every arbitrary smile.
Positivity needed by the logarithm follows from domination of the strictly
positive Pareto tail.

The corrected domain is `α > 1`, `l > 0`, `S₀ > 0`, `t > 0`,
`σ K > 0`, and the strict interior strike `S₀ * (1 + l) < K`.
At the excluded endpoint the logarithmic denominator is zero.
The matching price and local butterfly are hypotheses, as in the paper;
the digital inequality is derived rather than supplied as a hypothesis.

[BlackScholes/ReturnsSmileExamples.lean](Stats/BlackScholes/ReturnsSmileExamples.lean)
constructs satisfying parameters with spot 1, strike 2, expiry 4 and annual
volatility `(3 - K) / 2` near the anchor. The annual derivative is `-1/2`;
the total-volatility derivative is `-1`. A positive Black--Scholes call
price and digital probability determine valid `α > 1` and `0 < l < 1`.
The construction proves its matching and butterfly conditions, and the
examples apply both the survival domination and final `erfc` bound.
The older conditional price-tail helper also receives a concrete example.

The focused example build and default `lake build` pass without warnings;
the latter checks 3895 jobs. The standalone transitive axiom audit covers
1304 declarations, including 1118 theorem declarations, with no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`. All 27 locked Python
tests and the forbidden-construct check pass. The audit explicitly imports
every one of the 107 other source modules.
The regenerated index contains 108 modules and 601 named theorems, with
zero sorry, vacuous or placeholder markers. `dt refresh project` retains
all 670 existing public names and types; the repair adds eight public
declarations. The new source files are at most 151 lines each.

### Repair 2: replace the divergent Pareto Beta difference

Reread `papers/arXiv-1802.05495v3/kappa-n-final.tex`, Table I's Pareto
row and incomplete-Beta footnote (line 209), Definition 1 and Table III's
`α = 2` row (line 254). The literal footnote integrals diverge separately.
The corrected statement uses their finite interior difference:

```text
Bcentered(z,a,b) = ∫_(1/2)^z t^(a-1) (1-t)^(b-1) dt
Bcentered(u,a,b) - Bcentered(v,a,b) = ∫_v^u t^(a-1) (1-t)^(b-1) dt,
    0 < u,v < 1.
```

The common base cancels, so this is an ordinary convergent integral, even
at the paper's negative parameters. It is an explicit correction of the
printed footnote, not subtraction of two separately zero-valued total
integrals. The endpoints, signs, outer factor, exponents and integration
limit in the Pareto row are otherwise preserved.

[Kappa/Pareto.lean](Stats/Kappa/Pareto.lean) exposes focused modules for
the definitions, proper Beta calculus, positivity, lower bounds and exact
regressions. `paretoIntegrand_intervalIntegrable` proves convergence of the
outer integral for every `α > 1`, and `paretoRatio_pos` proves positivity.
At `α = 2`, the Beta kernel is at least 27 on `(0,1)`. Integrating the
resulting rational lower bound gives

```text
paretoRatio 2 ≥ 207/160 > 1
paretoKappa 2 < 2.
```

The rational integral `23/7680` used in this bound is proved by the
fundamental theorem of calculus. These certificates exclude the old
degeneration without assuming the desired ratio or changing the κ formula.
The legacy zero certificates now use `StatsReview.legacyParetoIntegrand`,
`legacyParetoRatio` and `legacyParetoKappa` from
[Review/ParetoLegacy.lean](Stats/Review/ParetoLegacy.lean); they cannot be
applied to the corrected production definitions.

An independent numerical sanity check integrated the actual scale-one
Pareto density over the one-variable and two-variable shortfall regions.
At `α = 2`, it gives `M(1) = 1`, `M(2) = 1.637326536084`, and
`κ = 0.594206583413`. Integrating the corrected Beta expression agrees
within `5e-16` in this run, and the paper rounds κ to 0.594. This is a
floating-point cross-check, not a Lean probability-law identification or
a certified numerical error bound.

**Remaining:** prove the corrected expression equals the genuine iid-Pareto
sum MAD ratio. The new analytic certificates do not supply that missing
bridge by definition; K14 remains incomplete in its distributional reading.

**Verification:** the default `lake build` and standalone `./make.py audit`
pass without warnings. The transitive audit checks 1337 declarations,
including 1146 theorem declarations, and finds only `Quot.sound`,
`Classical.choice` and `propext`. All 27 Python tests, the forbidden-construct
check and `git diff --check` pass. The regenerated index contains 116 modules
and 620 named theorems, with zero sorry, vacuous or placeholder markers.
The axiom audit explicitly imports all 115 other modules.
`dt refresh project` indexes 699 declarations: all 678 previous public names
and types remain, with 21 additions. The three legacy regression theorem
names in the separate `StatsReview` namespace were deliberately changed to
identify their obsolete definitions. Public Pareto function types are
preserved, while their integrand now uses the documented finite difference.
Each new module is at most 103 lines.

### Repair 3: lognormal support and zero-variance prices

Reread `papers/arXiv-1908.02347v3/OptionPricingPL2022.tex`, section
**Arbitrage Boundaries** (lines 285–312), including the positive-strike,
positive-volatility Gaussian term in the final bound. The former
`survivalLN` unconditionally used the density tail above `log(s/S₀)`.
That is a valid lognormal survival representation only for positive spot,
positive threshold and nonzero variance. It returned `1/2` at
`S₀ = 1, μ = 0, v = 1, s = 0`, although an exponential Gaussian is
strictly positive. At zero variance it lost the Gaussian atom entirely,
and the old call integral was always zero, including in-the-money calls.

[BlackScholes/LognormalLaw.lean](Stats/BlackScholes/LognormalLaw.lean)
now constructs the actual Gaussian pushforward by `x ↦ S₀ * exp x` and
proves it is a probability measure. `survivalLN` is this law's real-valued
measure of `Ioi s`, so the primary API now has the correct support and
atoms. Its bounds and antitonicity hold without variance or spot hypotheses.
Positive spot gives survival one for nonpositive thresholds. At zero
variance the law is `dirac (S₀ * exp μ)`, and its strict survival step is
proved explicitly. The Gaussian-tail transformation requires positive
spot and threshold, but applies to zero variance too. The density, CDF
and erfc formulas additionally require nonzero variance.

The call payoff is proved integrable for every real scale, mean and strike
and every nonnegative variance. Layer cake proves that the existing
`callPriceBS` survival integral equals the actual-law payoff expectation;
Gaussian change of variables gives the driver expectation. The earlier
restrictions on `callPriceBS_eq_expectation` are removed. In particular,

```text
callPriceBS S₀ μ 0 K = max (S₀ * exp μ - K) 0
callPriceBS 2 0 0 1 = 1
callPriceBS 2 0 0 (-1) = 3.
```

Put–call parity is strengthened to every scale, strike, mean and variance
using actual integrable positive-part payoffs. The density-based call
and survival derivative theorems now require nonzero variance. The actual
zero-variance call is continuous, but the survival is discontinuous at its
atom; `survivalLN_zero_var_not_continuousAt` certifies this exclusion.
The 372-line call-price file is split into payoff, derivative, closed-form
and positivity modules, each at most 193 lines, with public names re-exported.

[BlackScholes/LognormalExamples.lean](Stats/BlackScholes/LognormalExamples.lean)
checks the boundaries and instantiates the corrected formula domains.
[BlackScholes/LognormalMatch.lean](Stats/BlackScholes/LognormalMatch.lean)
constructs matching genuine risk-neutral lognormal and Pareto call
integrals with a local nonnegative mixed butterfly, then applies the
corrected Gaussian-tail and erfc comparisons. It supplies all their
premises rather than assuming the matching or arbitrage conclusions.
[Review/LognormalLegacy.lean](Stats/Review/LognormalLegacy.lean) freezes the
old formulas and proves both failures independently of the repaired API.

Risk neutrality means `μ = -v/2`; the general-mean model is explicitly
described as a lognormal payoff model. The real-volatility wrapper
`callPriceBS_σ` remains a closed-form expression whose probability-law
identification has positive spot, strike and volatility hypotheses. Its
documentation now directs boundary cases to the actual-law `callPriceBS`.
No global probability-law assertion is made for an arbitrary smile.

**Verification:** the default build passes all 3902 jobs without warnings.
The standalone transitive axiom audit checks 1375 declarations, including
1181 theorem declarations, and finds only `Quot.sound`, `Classical.choice`
and `propext`. All 27 Python tests, the forbidden-construct check and
`git diff --check` pass. The index contains 124 modules and 639 named
theorems with zero sorry, vacuous or placeholder markers; the audit
explicitly imports all 123 other modules. `dt refresh project` indexes
717 public declarations. No prior name is removed: 687 of the 699 old
types are unchanged, twelve have the documented domain corrections or
strengthenings, and eighteen declarations are added. The changed interfaces
are the survival continuity/bounds/monotonicity, Gaussian/CDF/erfc bridges,
smooth survival/call derivatives, lognormal butterfly comparison, call
expectation and put–call parity. Their downstream uses compile.

### Repair 4: actual empirical-survival error and the exponential-growth law

Reread `papers/arXiv-2007.16096v1/coronaIJF_paperArXiv.tex`, the
survival-forecast paragraph at line 235, **Uncertainty goes one way**
(lines 250–260), and the regular-variation definition in the footnote at
line 181. The paper prints an estimation error of **`o(1/n)`**, without
specifying an error measure. The former Lean comments incorrectly called
this an `O(1/sqrt n)` claim and only bounded a scalar formula.

[SinglePointForecasts/ExponentialLaw.lean](Stats/SinglePointForecasts/ExponentialLaw.lean)
constructs the actual law of `X₀ * exp(t*r)` from Mathlib's supported
exponential rate law. For `X₀ > 0`, elapsed time `t > 0`, and rate parameter
`λ > 0`, its full survival is proved to be

```text
P(X > s) = 1                  if s < X₀,
           (X₀/s)^(λ/t)       if s ≥ X₀.
```

This proves the Pareto-law transformation, including support and
normalization; it does not just match two proposed densities. The general
claim about the variance of arbitrary growth-rate families remains
separate from this specified exponential family.

[SinglePointForecasts/EventAverage.lean](Stats/SinglePointForecasts/EventAverage.lean)
and [EmpiricalSurvival.lean](Stats/SinglePointForecasts/EmpiricalSurvival.lean)
define the actual observed average of threshold indicators on a probability
space. Measurable samples with a common marginal law give an unbiased
estimator. Pairwise independence suffices for the exact variance and MSE;
no moment assumptions on the underlying sampled values are needed.
The indicator average is square integrable, and its squared error is
proved integrable. For the strict-tail probability `p = ν(Ioi x)` and
positive sample size, the corrected claims are

```text
E[Ŝ_n(x)] = p
Var(Ŝ_n(x)) = E[(Ŝ_n(x) - p)^2] = p(1-p)/n ≤ 1/(4n)
RMSE(Ŝ_n(x)) ≤ 1/(2 sqrt n).
```

The source sometimes uses the non-strict convention. The same indicator
argument works for closed threshold events; at the counterexample's
threshold there is no atom, so the conventions agree. These are
fixed-threshold estimates, not uniform empirical-process bounds or CLTs.

[SinglePointForecasts/FairCoin.lean](Stats/SinglePointForecasts/FairCoin.lean)
first constructs a nondegenerate iid Bernoulli product law and calculates
its actual squared-error integral as `1/(4n)`.
[ParetoError.lean](Stats/SinglePointForecasts/ParetoError.lean) then proves
the same failure within the source's heavy-tailed setting: the actual law
of `exp(r)`, `r ~ Exp(1)`, has survival `1/s` above one, and its actual
survival is regularly varying with index `-1`. An independent product
sample estimates its survival at two, where `p = 1/2`. Its genuine MSE
is again exactly `1/(4n)`. Theorems `unitParetoMSE_not_littleO` and
`unitParetoRMSE_not_littleO` refute the printed `o(1/n)` under both MSE
and RMSE interpretations. They use sample size `n+1` to keep every sample
nonempty and compare with `1/(n+1)`. The estimator is not defined by its
desired error rate.

The old scalar inequalities are retained under their public names, with
their algebraic scope made explicit. Their unused probability-range
hypotheses are deleted: the polynomial upper bound holds for every real
`p`. The actual-estimator theorems have distinct names and genuinely
mention the variance or squared-error integral. Concrete examples check
all new hypothesis families, including independent product samples,
positive exponential parameters and both branches of the support formula.

**Verification:** all 3911 default-build jobs pass without warnings. The
standalone axiom audit checks 1441 declarations, including 1238 theorem
declarations, with only `Quot.sound`, `Classical.choice` and `propext`.
All 27 Python tests, the forbidden-construct check and `git diff --check`
pass. The regenerated index contains 131 modules and 669 named theorems,
with zero sorry, vacuous or placeholder markers; the exhaustive audit
imports all 130 other modules. `dt refresh project` indexes 760 public
declarations. All 717 previous names remain, with 714 unchanged types and
the three documented stronger scalar inequalities; 43 declarations are
added. Each new module has at most 138 lines.

## Lean upgrade and reproducible verification

### 2026-10-19: dependencies and module compatibility

Lean and Mathlib now use the stable `v4.35.0` releases. `lake update` refreshed
all nine packages in `lake-manifest.json`; the Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The Python checks and notebook now have a reproducible environment in
`python/pyproject.toml` and `python/uv.lock`, including NumPy 2.5.4,
SciPy 1.18.1 and Matplotlib 3.11.2. `./make.py setup` installs that lockfile,
and `./make.py test` runs the repository's existing `kappa.py` tests.
All 27 tests passed; all 11 notebook code cells also executed successfully.

The 105 Lean modules now use the module system, with public imports and
exposed public declarations preserving the previous unfolding behavior.
The global axiom audit explicitly imports every Stats module with
`import all`, so private declarations remain in scope. The compiled-sorry
scanner uses that same scope. Deprecated lemma names, moved imports and
proof-style warnings were repaired in this upgrade.

Three lemmas have deliberately stronger statements after unused hypotheses
were deleted:

- `gaussianCopula_zero_left` and `gaussianCopula_zero_right` hold for every
  real value of the other coordinate, directly from the boundary branch of
  `gaussianCopula`; the former unit-interval hypotheses did no work.
- `cubicStudentSumFourierHalf_eq_expIntegralNeg` is a substitution identity
  for total Bochner integrals, valid for all `n : ℕ` and `ψ : ℂ`. Its former
  assumptions `1 ≤ n` and `ψ.re < n * sqrt 3` were unused. Convergence of
  the paper's Fourier integral is still established separately where needed.

The unchanged definition `cubicKernelReal` is now public because it already
occurs in the public integrability theorem's statement. These are interface
changes, not new distributional claims.

Comparing the elaborated `dt` dumps before and after the module migration
retains all 669 previously indexed public declarations. Of their printed
types, 665 are identical; the three stronger lemmas above account for three
changes, and the integrability theorem now names the public kernel rather
than its private counterpart. The only added indexed declaration is
`cubicKernelReal` (670 project declarations in total). This comparison covers
the configured `TailOptionPricing` namespace; the independent axiom audit
and source index also cover the review and verification modules.

For the Fourier comments, reread `papers/arXiv-1802.05495v3/kappa-n-final.tex`,
section **Cubic Student T (Gaussian Basin)**, Proposition 1 and equations
`MDcubic` and `pdfcubicsum` (lines 553–599 in this version). The closed-form
identity matches the paper's cosine integral, including `n ≥ 1`, the factor
`1 / pi`, both complex arguments and the denominator `2 * sqrt 3 * pi`.
The old comments incorrectly called proved steps axioms and identified the
defined integral with an actual iid-sum density without a probability-law
bridge. The comments now distinguish these claims. The iid-sum density
identification and its genuine MAD remain open; K19–K22 retain their coverage
limitations. No paper is promoted to complete by this upgrade.

| Check on Lean/Mathlib 4.35.0 | Result |
| --- | --- |
| Default `lake build` | **ok**, 3892 jobs; no warnings or errors |
| `./make.py audit` | **ok**, 1279 declarations, 1096 theorem declarations, zero non-core axioms |
| Compiled-sorry scanner scope | 1279 declarations, including 534 private declarations |
| Audit imports versus the source tree | All 104 other modules explicitly imported |
| `./make.py index` | **ok**, 105 modules, 593 named theorems, zero sorry/vacuous/placeholder markers |
| `./make.py forbidden` | **ok** |
| `./make.py test` | **ok**, 27 tests, no skips |
| Notebook execution | **ok**, all 11 code cells |
| `dt refresh project` and `dt status` | **ok**, project/Mathlib/core current; 433152 indexed declarations |

### 2026-10-01: previous upgrade

At the start, `lean-toolchain` and `lakefile.toml` already requested 4.34.1,
while the lockfile and old compiled dependencies corresponded to 4.29.1.
The dependencies have now been synchronized with `lake update`, and the project
proofs have been adapted to Lean/mathlib 4.34.1.

| Check | Result |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.34.1` |
| mathlib release | `v4.34.1` |
| Locked mathlib revision | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Original main-root build after compatibility fixes | **ok**, 3256 Lake jobs |
| Expanded default build, including all project modules and audits | **ok**, 3844 Lake jobs |
| Transitive axiom audit | **ok**, 1279 declarations, including 1096 theorem declarations; zero non-core axioms |
| Axioms found | `propext`, `Classical.choice`, `Quot.sound` only |

These counts include private and generated declarations; they are not counts of
paper theorems. The semantic diagnostic and regression theorems are included.
Warnings about deprecated APIs and proof style remained at that stage; the
2026-10-19 upgrade above removes them.

The compatibility changes concern derivatives, function equalities, updated
lemma names, the `NNReal` constructor and `NullSingletonClass`.
In `Stats/Pareto/Measure.lean`, the probability-measure declaration with explicit
positivity proofs is now a theorem rather than an instance that typeclass
synthesis cannot infer. Its name, statement and explicit applications remain
available.

### The previously separate modules are now included

The exclusion of `Stats.RegularVariation` was an obsolete precaution from when
that development contained unfinished proofs. The proofs are now closed.
The old umbrella comment claiming remaining placeholders was inaccurate.

`Stats.TailOptionPricing` now imports:

- `Stats.RegularVariation`;
- `Stats.Pareto.Measure`;
- `Stats.Copula.Basic`.

The regular-variation umbrella also imports the previously standalone
`Stats.RegularVariation.Multivariate` module. Its projection definitions and
six elementary vector lemmas are now included in the library and global
audit; its old claim of an established spectral-measure equivalence was
removed because that equivalence is not proved there.

Consequently, `import Stats` exposes those results, including the full log-return
theorem. The library configuration now has `globs = ["Stats.*"]`, so plain
`lake build` builds every Stats source module, including both verification
modules and the new audits. The audits need not be imported into production
mathematical modules to participate in the default build.

To reproduce:

```bash
lake build
lake env lean Stats/ReviewChecks.lean
lake env lean Stats/AxiomAudit.lean
```

[Stats/ReviewChecks.lean](Stats/ReviewChecks.lean) contains proof certificates
for the historical minimum-size defect, its repair, and the Pareto defect
described in K-11 and K-14.
[Stats/AxiomAudit.lean](Stats/AxiomAudit.lean) checks transitive axiom dependencies
of all imported declarations originating in Stats modules, including private
declarations. A dependency other than the three core axioms causes an error.

The existing [Stats/Verify.lean](Stats/Verify.lean) has 354 `#print axioms`
commands; [Stats/RegularVariation/Verify.lean](Stats/RegularVariation/Verify.lean)
has another 35. The global audit is broader than these hand-selected lists.

## 1. Tail Option Pricing Under Power Laws

Source: [OptionPricingPL2022.tex](papers/arXiv-1908.02347v3/OptionPricingPL2022.tex).
Main modules: [Pareto](Stats/Pareto.lean), [Theorem1](Stats/Theorem1.lean),
[Arbitrage](Stats/Arbitrage.lean), [BlackScholes](Stats/BlackScholes.lean),
[RegularVariation](Stats/RegularVariation.lean).

### OP-01. Exact strong Pareto versus a general regularly varying tail — not ok as an exact identification

The paper starts from survival $L(s)s^{-α}$, then uses a constant tail factor.
[Basic.lean](Stats/Pareto/Basic.lean) defines the exact strong-Pareto survival
$(l/s)^α$. That is a legitimate exact model, but is not identical to every
slowly varying $L$ at finite strikes.

**Missing:** an explicit separation in the paper interpretation between exact
strong-Pareto prices and asymptotic general-tail prices. Exact finite-strike
identities cannot be inferred from slow variation alone.

### OP-01a. General slowly varying call asymptotics — ok

[FullSV.lean](Stats/RegularVariation/Abelian/FullSV.lean):
`callPriceSV_asymptotic` and `callPriceSV_ratio_asymptotic` prove

```text
C(K)/(L(K) K^(1−α)) → 1/(α−1),
C(cK)/C(K) → c^(1−α).
```

The assumptions are $α>1$, $c>0$, measurability, slow variation and eventual
positivity of $L$. Boundedness of $L$ is not required.

**Missing:** nothing for these asymptotic statements. They do not turn OP-01
into an exact finite-strike identity.

### OP-02. Call payoff expectation equals the survival integral — ok

[LayerCake.lean](Stats/LayerCake.lean):
`expectation_max_eq_integral_survival`, `callPrice_eq_expectation`.
This is a genuine layer-cake theorem for a random variable, with measurability,
integrability and the survival/probability relation supplied explicitly.

**Missing:** nothing for the stated identity under those hypotheses.

### OP-03. Strong-Pareto call formula — ok

For $l>0$, $α>1$, $K≥l$,

```text
C(K) = l^α K^(1−α)/(α−1).
```

[Pareto/Basic.lean](Stats/Pareto/Basic.lean): `callPrice_eq`.
The price is an integral, and its evaluation is proved.

**Missing:** nothing in the exact strong-Pareto model.

### OP-04. Scale calibration from an anchor call — ok

The formula is $l=((α-1)C_m K^{α-1})^{1/α}$.
[Pareto/Basic.lean](Stats/Pareto/Basic.lean): `callPrice_invert`.

**Missing:** nothing for inversion of a valid model price in the tail region.
Statistical uncertainty of a market calibration is a different claim.

### OP-05. Result 1: Relative Pricing under Distribution for S — ok

Source line 179:

```text
C(K₂) = (K₂/K₁)^(1−α) C(K₁).
```

[Pareto/Basic.lean](Stats/Pareto/Basic.lean): `callPrice_ratio`.
Positivity and both tail-strike conditions are explicit.

**Missing:** nothing for exact strong Pareto. For general slow variation,
the corresponding proved assertion is the asymptotic statement OP-01a.

### OP-06. Remark 1: the anchor contains all necessary information below l — not ok literally

Source line 173. The formulas establish sufficiency of tail parameters for
the specified tail prices. They do not reconstruct the distribution below $l$.

**Missing:** a precise statement of what “necessary information” means.
Identifiability of an entire distribution from one option is not established.
A scoped invariance of tail prices to changes below the strike would be a
different, valid assertion.

### OP-07. Remark 2, part 1: affine returns preserve the RV index — not ok completely

Source line 187. [Closure.lean](Stats/RegularVariation/Closure.lean) contains
functional closure results and translation under monotonicity.
[Pareto/Returns.lean](Stats/Pareto/Returns.lean) proves the particular
strong-Pareto return formulas.

**Missing:** a general theorem relating survival of $(S-S₀)/S₀$ to survival
of $S$ and preserving its RV index under the usual general-tail assumptions.

### OP-08. Theorem 1: Log returns — ok with explicit regularity assumptions

Source line 196.
[Application.lean](Stats/RegularVariation/Application.lean):
`survivalLogReturn_not_regularlyVarying_full` proves that

```text
x ↦ L(S₀ exp x) (S₀ exp x)^(−α)
```

is not regularly varying with **any real index**, for $α>0$, $S₀>0$ and
measurable, eventually positive, slowly varying $L$.
There is also `survivalLogReturn_not_regularlyVarying_full_of_monotone`.

The measurability and positivity conditions make the usual regularity of a
nonzero survival tail explicit. A theorem assuming `h_subexp` alone would
leave a structural gap; the full module derives that property.

**Missing:** nothing for the stated analytic theorem. It is now available
through `import Stats`. The paper's abbreviated printed proof is not
used as a trusted assumption.

### OP-09. Call formula under Pareto returns — ok

```text
C(K,S₀) = (l S₀)^α (K−S₀)^(1−α)/(α−1).
```

[Pareto/Returns.lean](Stats/Pareto/Returns.lean): `callPriceReturns_eq`.

**Missing:** nothing with positive spot, $α>1$ and a valid tail strike.

### OP-10. Calibration under Pareto returns — ok

[Pareto/Returns.lean](Stats/Pareto/Returns.lean):
`callPriceReturns_pow_eq`, `callPriceReturns_invert`.

**Missing:** nothing for the stated inversion on the valid parameter domain.

### OP-11. Result 2: Relative Pricing under Distribution for returns — ok

Source line 230:

```text
C(K₂) = ((K₂−S₀)/(K₁−S₀))^(1−α) C(K₁).
```

[Pareto/Returns.lean](Stats/Pareto/Returns.lean): `callPriceReturns_ratio`.

**Missing:** nothing for the exact model and the stated strike conditions.

### OP-12. Printed put density and normalization — not ok literally; corrected normalization ok

The printed density/normalization uses powers of $-1$ with arbitrary real $α$,
which does not give a suitable real probability density as written.

[Pareto/Put.lean](Stats/Pareto/Put.lean) instead uses positive $S₀-S$.
`densityMass_eq` proves that the unnormalized density has mass $1-l^α$
on $[0,(1-l)S₀]$. The normalization is $(1-l^α)^{-1}$ for $0<l<1$.

**Missing:** nothing for the corrected mass integral. The literal expression
needs correction. The claim that the correction is negligible whenever
$σ√t≤1/2$ also needs a quantitative bridge from that condition to $l^α$.

### OP-13. Result 3: Put Pricing, as printed — not ok

Source line 272. The printed expression uses $(K-S₀)^{1-α}$ and
$S₀^{1-α}$ multiplying a linear bracket. The valid put region has $K<S₀$.

**Missing:** a corrected original formula. The proved version uses $S₀-K$
and the factor $S₀^{-α}$. A theorem about that correction does not validate
the literal paper formula.

### OP-14. Corrected integral and relative-price core of Result 3 — ok

[Pareto/Put.lean](Stats/Pareto/Put.lean):
`putRaw_eq`, `putRaw_ratio`, `putPrice_eq`.
Define

```text
B(K) = (S₀−K)^(1−α) − S₀^(−α)((α−1)K+S₀).
```

The proved unnormalized price is $l^α S₀^α B(K)/(α-1)$, and the common
scale/normalization cancels in the relative-price identity.

**Missing:** nothing for the evaluated integral and the cross-multiplied
identity actually stated by `putRaw_ratio`.
A literal quotient additionally needs $B(K₁)≠0$; in particular, a zero-strike
anchor has zero put price and must be excluded.

### OP-15. Breeden–Litzenberger derivative and convexity — ok

[Calculus/Greeks.lean](Stats/Calculus/Greeks.lean) and the calculus modules
prove the strike derivatives and the positive second derivative
$αl^α K^{-α-1}$ in the open tail region.
[Arbitrage.lean](Stats/Arbitrage.lean) also proves spread/butterfly properties.

**Missing:** nothing for these tail statements. Global absence of arbitrage
for an arbitrary central-model/tail splice does not follow automatically.

### OP-16. Necessary derivative condition from matched butterflies — ok

[Arbitrage.lean](Stats/Arbitrage.lean):
`deriv_le_of_matched_butterfly`, `callPrice_dominates_BSC_deriv`.
Matched values and nonnegative small right-side butterflies imply
$g'(K₁)≤f'(K₁)$, with $f$ on the right and $g$ on the left.

**Missing:** nothing for that necessary condition.

### OP-17. Printed derivative direction — false; counterexample proved

The paper prints $BSC'(K₁)≥C'(K₁)$.
The first-order term of the stated butterfly is
$Δ(C'(K₁)-BSC'(K₁))$, so the necessary inequality has the opposite direction.

`exists_returns_smile_parameters` in
[BlackScholes/ReturnsSmileExamples.lean](Stats/BlackScholes/ReturnsSmileExamples.lean)
constructs matching integral-defined Pareto-returns and Black--Scholes
curves satisfying the local butterfly, with `BSC' < C'` strictly.
This refutes the printed direction within the actual option setup.

**Correction:** use `BSC' ≤ C'`. The necessary condition and a counterexample
to the printed direction are both proved.

### OP-18. Logarithmic lower bound on α for the S-tail model — ok

[Arbitrage.lean](Stats/Arbitrage.lean): `alpha_lower_bound`.
From $(l/K)^α≤Q$ with $0<l<K$ it proves $log(Q)/log(l/K)≤α$.
Positivity of $Q$ and the negative denominator are handled.
[BlackScholes/Greeks.lean](Stats/BlackScholes/Greeks.lean) gives Gaussian/erfc
specializations. Repair 3 constructs the actual Gaussian pushforward law,
corrects its survival support and zero-variance call prices, and restricts
the smooth Gaussian/CDF/erfc forms to positive spot, strike and variance.
`exists_lognormal_pareto_match` witnesses the matching and local-butterfly
premises with actual call integrals and applies both comparisons.

**Missing:** nothing for this conditional bound.

### OP-19. Final returns-tail bound with σ(K), σ′(K) and t — ok on the corrected interior domain

[BlackScholes/ReturnsSmile.lean](Stats/BlackScholes/ReturnsSmile.lean):
`callPriceReturns_hasDerivAt`, `returns_survival_le_bsSmileDigital`,
`alpha_lower_bound_returns_smile` and `alpha_lower_bound_returns_smile_erfc`.
The final theorem derives domination of the **returns** tail
$((lS₀)/(K-S₀))^α$ from price matching, the local mixed butterfly and the
actual derivative `HasDerivAt σ σ' K`. Annual volatility and its derivative
are both multiplied by $sqrt(t)$. The logarithmic denominator is
$log(lS₀/(K-S₀))$.

The strike must satisfy `S₀ * (1 + l) < K`; the paper's broader closed
tail domain includes an endpoint where this denominator vanishes.
The constructed nonconstant smile in `ReturnsSmileExamples` satisfies all
the hypotheses, including matching and the local butterfly, at positive
expiry 4. `bsSmileDigital_eq_erfc` supplies the equivalent `erfc` notation.
The older `alpha_lower_bound_smile_erfc` remains only a conditional
price-tail algebra helper and is now documented accordingly.

**Missing:** nothing for the corrected local necessary bound. It does not
prove global absence of arbitrage for arbitrary smile/tail splices.

### OP-20. Option prices can exist with infinite variance — ok for strong Pareto

For $1<α≤2$, the call integral is finite while the second-moment integrand
is not integrable.
[Pareto/Mispricing.lean](Stats/Pareto/Mispricing.lean) and
[RiskMeasures/Moments.lean](Stats/RiskMeasures/Moments.lean) establish the relevant
moment thresholds.

**Missing:** nothing for this example. Market-fit plots and conclusions about
observed overpricing are empirical claims, not consequences proved here.

## 2. How Much Data Do You Need? — κ

Source: [kappa-n-final.tex](papers/arXiv-1802.05495v3/kappa-n-final.tex).
Modules: [Kappa.lean](Stats/Kappa.lean) and its submodules.
This section has substantial differences between distribution-specific names
and the probability statements actually established.

### K-01. Definition 1: algebraic κ formula — ok as a MAD interface

Source line 272. [Kappa/Basic.lean](Stats/Kappa/Basic.lean):
`kappa`, `kappa_eq_ratio`.
The logarithmic formula and its ratio form are established for positive $M$.

**Missing:** nothing for the algebraic interface. Each distributional application
still needs a real MAD bridge and a nonzero logarithmic denominator.
Total division in Lean does not establish statistical nondegeneracy.

### K-02. Definition 2: regular-variation class — ok at the function level

Source line 306. RV/SV are defined in [Theorem1.lean](Stats/Theorem1.lean)
and [RegularVariation/Defs.lean](Stats/RegularVariation/Defs.lean).
`paretoSurvival_isRegularlyVarying` supplies the strong-Pareto example.

**Missing:** nothing for this functional definition. A limit law for sums is
a separate probability theorem.

### K-03. Definition 3: stable characteristic function — not ok as a complete probability class

Source line 318. [Kappa/Stable.lean](Stats/Kappa/Stable.lean):
`StableClass` describes a function $φ : ℝ → ℂ$ with the required formula,
including the $α=1$ branch.

**Missing:** identification with the characteristic function of an actual law
and the associated probability-model existence/identification.
The explicit function formulas themselves are encoded.

### K-04. Eq. 2: telescoping κ decomposition — ok on corrected positive indices

[Kappa/Basic.lean](Stats/Kappa/Basic.lean):
`kappa_decomposition`, `kappa_decomposition_local`.
The sum runs over positive indices from $n₀$ to $n-1$, with positivity and
nonzero-denominator conditions.

**Missing:** nothing for that version. A literal zero initial index in the
printed sum needs correction because it invokes $log(0)$.

### K-05. Eq. 5: ᾱ = min(α,2) — ok as a definition; not ok as a domain-of-attraction theorem

`stableAlphaBar` in [Kappa/Basic.lean](Stats/Kappa/Basic.lean) implements
the piecewise value.

**Missing:** for the probabilistic interpretation, convergence of normalized sums
to the appropriate stable law, including the normalizations and boundary $α=2$.
Defining the index does not establish a basin-of-attraction result.

### K-06. Stable-law summation — not ok completely

[Kappa/Stable.lean](Stats/Kappa/Stable.lean):
`stable_charfun_pow_alpha_ne_one`, `stable_charfun_pow_alpha_eq_one`
prove the function algebra.
`stable_sum_stable` assumes
`h_iid : ∀ t, Sn_charfun t = (φ t)^n`.

**Missing:** deriving that assumption from actual independence and identical
laws, then identifying the sum distribution. The $α=1$ location correction
also needs to be assembled into a probability theorem.

### K-07. Eq. 6: κ = 2 − ᾱ for stable laws — not ok completely

`kappa_stable_invariance` and `stable_class_kappa_invariance` assume
$M(k)=ck^{1/ᾱ}$ through `hM_form`.

**Missing:** proof of that scaling for the actual MAD of stable sums, with
integrability, positivity and the sum-law bridge.
The appropriate domain for the paper's ordinary finite-mean MAD is $α>1$.

### K-08. Gaussian reference κ = 0 — not ok as a random-variable theorem

`kappa_gaussian` proves the consequence of the assumed $M(k)=c√k$.

**Missing:** the bridge from Gaussian iid sums and their MAD to that function.
Existing Gaussian-measure infrastructure has not been composed here.

### K-09. Cauchy / α = 1 under Definition 1 — not ok

`kappa_cauchy` proves an abstract $M(k)=ck$ calculation.
A genuine Cauchy law lacks the finite mean and finite MAD required by Definition 1.

**Missing:** a separately defined extended or truncated metric and its justification.
The ordinary κ definition cannot be applied literally to Cauchy in this way.

### K-10. Eq. 7: sample-size power transformation — ok as algebra

[Kappa/Basic.lean](Stats/Kappa/Basic.lean):
`n_nu_gaussian`, `n_nu_gt_n_g`, `n_g_of_n_nu_n_nu`,
`n_nu_n_g_of_n_nu`, `n_nu_bidirectional`.
These prove properties of $n_ν=n_g^{1/(1-κ)}$ and its inverse.

**Missing:** nothing for these power identities.
For fixed $0<κ<1$, growth is a fixed power of $n_g$.

### K-11. Actual minimum sufficient sample size — not ok fully; zero-size defect fixed

The source is Section III.B, "Practical significance for sample sufficiency",
the display labeled `md` in `papers/arXiv-1802.05495v3/kappa-n-final.tex`
(lines 389–392). The paper requires $n_ν>0$. The former `n_min` admitted zero because Lean has
`sampleMeanMAD M 0 = M 0 / 0 = 0`. The candidate set now explicitly requires
`0 < n_ν`.

[ReviewChecks.lean](Stats/ReviewChecks.lean):
`StatsReview.legacy_n_min_eq_zero_of_nonneg` retains a certificate of the old
bug using a separate historical definition. Regression theorems prove that
a zero-MAD example now has minimum one and that a $1/n$ deviation first
reaches $1/3$ at sample size three.

**Missing:** genuine distributional MAD oracles, a positive baseline sample
size in the probabilistic application, and Eq. 7's approximation-error
justification. The positive-index minimum itself is repaired.

### K-11a. Positive-index minimum and empty-set sentinel — ok

`n_min_le_of_witness`, `n_min_mem`, `n_min_pos` and `n_min_eq_zero_iff`
prove that a positive admissible witness bounds the minimum, that a nonempty
candidate set has an attained positive minimum, and that the value zero occurs
exactly when no positive candidate exists.

**Missing:** nothing for the abstract minimum on supplied MAD functions.
The probability interpretation remains the separate task K-11.

### K-12. Table I: general Student T — not ok

[Kappa/TableI.lean](Stats/Kappa/TableI.lean): `kappa_studentT_general`.
It uses `tableIMAD R`, defined to be $1$ at index 1, $R$ at index 2
and $0$ elsewhere, then rewrites logarithms of $R$.

**Missing:** the Student law, actual one- and two-summand MAD integrals, and
their proved ratio. An oracle identity does not establish the distributional row.

### K-13. Table I: Exponential/Gamma — not ok as a distributional claim

[Kappa/Exponential.lean](Stats/Kappa/Exponential.lean):
`expSumMAD` is defined by a closed expression, and `kappa_exponential`
calculates κ of that expression.

**Missing:** an integral derivation of the actual sum MAD.
The scope of “Gamma” also needs clarification: the row is not proved for
arbitrary Gamma shape parameters.

### K-14. Table I: Pareto — finite-Beta defect repaired; MAD bridge still open

[Kappa/Pareto/Defs.lean](Stats/Kappa/Pareto/Defs.lean) retains the literal
footnote definition only for diagnostics:

```text
incompleteBeta(z,a,b) = ∫₀^z t^(a−1)(1−t)^(b−1) dt.
```

The Pareto row uses $a=-α$, $b=1-α$, $α>1$ and two $z$ values in $(0,1)$.
Both integrals diverge at zero because of $t^{-α-1}$.
Mathlib's total real integral assigns zero to a nonintegrable integrand.
Consequently the two Beta terms separately became zero in the old formula.

[ReviewChecks.lean](Stats/ReviewChecks.lean) proves, without non-core axioms:

- `incompleteBeta_pareto_eq_zero`;
- `legacy_paretoIntegrand_eq_zero`;
- `legacy_paretoRatio_eq_zero`;
- `legacy_paretoKappa_eq_two`: **the historical expression equals 2 for every $α>1$**.

This contradicts the intended positive MAD ratio and, for example, Table III's
approximately 0.594 entry at $α=2$.
The paper's integral-definition footnote omits this divergence issue.
The current `paretoIntegrand` instead uses a common interior Beta primitive.
`incompleteBetaCentered_sub` identifies its difference with a single
convergent integral between the positive endpoints. The corrected outer
integral converges for all `α > 1`, and its ratio is strictly positive.
`paretoRatio_two_lower_bound` proves `paretoRatio 2 ≥ 207/160`; consequently
`paretoKappa_two_lt_two` excludes the old constant-two defect.
`kappa_pareto_general` remains an algebraic identity on the supplied reference
function, rather than a proof of the missing probability theorem.

**Missing:** the actual iid-Pareto sum MAD derivation and its identification
with this corrected finite-integral expression. The analytic correction and
its nondegenerate regression certificates are now proved.

### K-15. Table I: Gaussian switching variance — not ok

`kappa_normal_switching_variance` again uses `tableIMAD`.
The printed radicand $ap/(p-1)+σ²$ can be negative for probability parameters;
$σ=1,a=2,p=1/2$ is an example.
A total real square root does not reject the formula on that domain.

**Missing:** a precise mixture parameterization, valid parameter restrictions,
a checked source formula and a real mixture-MAD derivation.

### K-16. Table I: Lognormal approximation — not ok as an approximation to genuine κ

`kappa_lognormal_explicit` is an oracle identity.
The paper's approximation symbol is not represented by an error estimate
or an asymptotic equivalence to the genuine sum MAD.

**Missing:** the actual metric and a theorem specifying the approximation regime
and its accuracy.

### K-17. Table II: explicit results, bounds and Pearson approximation — not ok

Some algebraic bounds and a genuine large-$σ$ limit are available, but the
whole table describes distributional κ values.

**Missing:** distributional MAD bridges, actual approximation bounds and a
defined Pearson approximation error. The Pareto entry is also affected by K-14.

### K-18. Table III and numerical sample-size comparisons — not ok

The table gives Pareto/Student values for $n=2,30,100$; the text compares
120/543 observations with a Gaussian sample of 30.

**Missing:** actual proved MAD calculations, numerical error certificates and
a correct minimum-size criterion. Transcribing numbers or proving `n_nu`
power algebra is insufficient.

### K-19. Single cubic Student density — not ok as a fully identified law

[Kappa/CubicStudent.lean](Stats/Kappa/CubicStudent.lean):
`cubicStudentDensity`, `cubicStudentDensity_pos`, `cubicStudentDensity_neg`.
The function $6√3/(π(x²+3)²)$ is positive and symmetric.

**Missing:** probability normalization, its actual Student-law identification,
mean and characteristic-function bridge.

### K-20. Proposition 1: κ of an iid cubic Student sum — not ok

Source line 562. The paper asserts

```text
κ(1,n) = 2 − log(n)/log(exp(n) n^(−n) Γ(n+1,n) − 1).
```

`kappa_cubicStudent` proves this for `cubicStudentSumMAD`,
which is **defined** by the corresponding closed expression.

**Missing:** proof that this expression equals the actual mean absolute
deviation of the iid sum. This prevents the paper's main Proposition
from being counted as fully formalized.

### K-21. Cubic Student MAD and its Loulakis finite-sum form — not ok as MAD; algebra ok

`cubicStudentSumMAD_one`, `cubicStudentSumMAD_succ`,
`cubicStudentSumMAD_loulakis_form` establish identities between expressions.
The incomplete-Gamma integral/finite-sum calculation is real proof work.

**Missing:** $∫|y|p_n(y)dy$, normalization of $p_n$ and its iid-sum law.

### K-22. Sum characteristic function and Fourier inversion — not ok completely

The paper uses $(1+√3|ω|)^n exp(-n√3|ω|)$.
[Kappa/CubicStudentExpIntegral.lean](Stats/Kappa/CubicStudentExpIntegral.lean)
contains the analytic Fourier-half integrals.

**Missing:** the original characteristic function derived from the density,
multiplicativity from iid and an inversion theorem identifying the actual
sum density.

### K-23. Exponential-integral representation of the defined Fourier integral — ok

`cubicStudentSumDensity_via_exponentialIntegral` and
`cubicStudentSumFourierHalf_eq_expIntegralNeg` prove the analytic special-function
identity, with the required integrability conditions.

**Missing:** nothing for that identity. Its interpretation as an actual iid-sum
density remains K-22.

### K-24. Incomplete-Gamma / half-sum asymptotic equivalent — ok

[Kappa/CubicStudentLaplace.lean](Stats/Kappa/CubicStudentLaplace.lean) and
[Kappa/CubicStudentAsymptotic.lean](Stats/Kappa/CubicStudentAsymptotic.lean)
prove the analytic limiting equivalent.

**Missing:** nothing for the proved limit. The comment describing
`incompleteGamma_laplace_asymptotic` as an axiom is obsolete;
the actual declaration and transitive audit show a closed proof.

### K-25. O(1/√n) remainder and Poisson/CLT explanation — not ok completely

The source gives $exp(-n)Σ_{m=0}^{n-1}n^m/m!=1/2+O(1/√n)$.
A limiting equivalent does not establish that remainder rate.

**Missing:** the stated quantitative remainder estimate and, if following the
paper's probability route, an actual Poisson CDF bridge and quantitative CLT.

### K-26. Printed limit log(n)κ → π²/4 — not ok

The source omits an outer logarithm. Its MAD expression instead yields
$log(π²/4)$.

**Missing:** correction of the paper's constant.

### K-27. Corrected limit log(n)κ → log(π²/4) — ok for the closed function

`kappa_cubicStudent_asymptotic` proves this limit analytically.

**Missing:** nothing for `kappa cubicStudentSumMAD`.
Calling it the actual Student-sum asymptotic still requires K-20.
Convergence of the whole distribution to Gaussian is a separate CLT claim.

### K-28. Lognormal iid-sum cumulants — not ok as a probability theorem

[Kappa/LognormalCumulants.lean](Stats/Kappa/LognormalCumulants.lean):
`lognormalMoment` is defined by an exponential formula;
cumulants are defined by moment polynomials;
sum cumulants are defined as $n$ times the single-variable expressions.

**Missing:** equality with actual lognormal-measure moments and actual iid-sum
cumulants. A genuine lognormal probability family already exists elsewhere,
but this bridge has not been assembled.

### K-29. Lognormal-sum skewness and kurtosis — not ok completely

The $C(σ)/√n$ and $3+C'(σ)/n$ formulas are verified for defined expressions.

**Missing:** K-28 and identification with normalized central moments of the
actual sum, with nonzero-variance conditions.

### K-30. Genuine lognormal κ tends to zero as σ → 0 — not ok

`lognormal_kappa_tendsto_zero_as_sigma_to_zero` proves a limit of
`lognormalKappaProxy`, an excess-kurtosis expression, not Definition 1's κ.

**Missing:** the actual MAD-ratio limit and its substitution into canonical κ.
The theorem name is broader than its type.

### K-31. Genuine lognormal κ tends to zero as n → ∞ — not ok

`lognormal_kappa_tendsto_zero_as_n_to_infty` proves a proxy limit,
essentially $C(σ)/n→0$.

**Missing:** convergence of actual normalized-sum MAD, sufficient control of
absolute moments, and the canonical κ bridge. Excess kurtosis is not κ.

### K-32. Moment-matched lognormal κ* — ok as a formula; not ok as a bound

[Kappa/TableI.lean](Stats/Kappa/TableI.lean):
`lognormal_kappa_star`, `kappa_lognormal_star`.
The erf expression, including its leading factor $n$, is faithfully encoded.

**Missing:** for the paper claim, actual proxy-law MAD derivation, $0≤κ*≤1$,
the moment-matching bridge and rigorous lower/upper-bound relationships
to the genuine sum metric.

### K-33. M(n) ≤ n M(1) and the conditional κ ≤ 1 bound — ok

[Kappa/IIdTriangle.lean](Stats/Kappa/IIdTriangle.lean):
`kappa_upper_bound_iid` and triangle-integral results use actual integrable
random variables with identical laws.
Turning the MAD bound into a κ bound requires the stated positive-logarithm
conditions.

**Missing:** nothing for this conditional probability result.

### K-34. Genuine MAD layer-cake identity — ok

[Kappa/MadLayerCake.lean](Stats/Kappa/MadLayerCake.lean) proves

```text
E|X−E X| = 2 ∫₀^∞ P(X>E X+t) dt
```

for integrable random variables on a probability space.

**Missing:** nothing. This is an actual expectation theorem.

### K-35. Loulakis large-σ limit: M(n)/M(1) → n and κ → 1 — ok

[Kappa/LognormalIIdSetup.lean](Stats/Kappa/LognormalIIdSetup.lean) constructs
a product Gaussian probability space and iid
$X_i=exp(σZ_i-σ²/2)$ with mean 1.
[Kappa/LoulakisLognormal.lean](Stats/Kappa/LoulakisLognormal.lean)
defines `Mn` and `M1` by actual absolute-deviation integrals, proves the
upper bound, the lower asymptotic bound and the squeeze limit.

`kappa_lognormal_tendsto_one_canonical` proves the canonical κ limit
for every fixed $n≥2$.

**Missing:** nothing for this result. Old TODO claims that this argument is
unfinished are obsolete.

### K-36. Source intermediate claim P(X₁>t) → 1 as σ → ∞ — not ok literally

For the normalized $X_i=exp(σZ_i-σ²/2)$ and fixed $t>0$, that probability
tends to **zero**. A relevant integrated tail tends to one.
The source also mismatches the sign of its stated lognormal $μ$ with this $X$.

**Missing:** correction of the intermediate source text. The actual K-35 proof
uses the correct relationships.

### K-37. Pearson ODE and the derivative of Qf — ok

[Kappa/PearsonIV.lean](Stats/Kappa/PearsonIV.lean):
`IsPearsonIV`, `pearsonIV_aux_deriv`.

**Missing:** nothing for the product-rule consequence of the stated
differentiability and ODE assumptions.

### K-38. Eq. 13: Pearson IV MAD — not ok completely

`pearsonIV_mad_eq` and `pearsonIV_mad_eq_paper` take a scalar
`intCentered` and assume the integration-by-parts result `h_ibp`:

```text
(a₁−2b₂) intCentered = Q(m) f(m).
```

The conclusion follows by division.

**Missing:** the actual integral, density normalization and integrability,
boundary decay of $Qf$, integration of the ODE on the half-line, mean
identification and the De Moivre MAD bridge.
The essential analytic step remains a hypothesis.

### K-39. Pearson IV parameters matched to lognormal cumulants — not ok completely

`pearsonIVLognormalMatch` defines explicit coefficients.
Some positivity facts and $a₁=1$ are proved.

**Missing:** existence of a normalized Pearson density on the valid domain,
its four actual matched cumulants and an approximation-error bound.

### K-40. Eq. 14: an iid exponential sum has Gamma(n,λ) law — not ok completely

`gammaSumDensity_eq_gammaPDFReal` proves equality of density expressions.

**Missing:** the convolution/iid-sum probability theorem establishing the
distribution of $X₁+…+Xₙ$.

### K-41. Eq. 15: exponential-sum MAD — not ok

$M(n)=2exp(-n)n^n/(λΓ(n))$ is used as the definition of `expSumMAD`.

**Missing:** evaluation of the actual integral
$∫₀^∞|z-n/λ|gammaPDFReal(n,λ,z)dz$, plus K-40.

### K-42. Eq. 16 and log(n)κ → 4 − 2log(2π) — ok for the closed function

`kappa_exponential`, `kappa_exponential_asymptotic` prove the algebraic
formula and its Gamma/Stirling limit.

**Missing:** nothing for `kappa (expSumMAD λ)`.
As a distributional statement this remains **not ok** until K-41 is established.

### K-43. Eq. 17: Gaussian-mixture kurtosis — not ok as a mixture moment theorem

[Kappa/GaussianMixture.lean](Stats/Kappa/GaussianMixture.lean):
`gaussianMixtureKurtosis` is defined by the closed expression.

**Missing:** the actual mixture measure, its second/fourth central moments
and their ratio equal to this expression.

### K-44. Kurtosis ≥ 3 threshold for the defined formula — ok

`gaussianMixtureKurtosis_ge_three_iff_poly` and
`gaussianMixtureKurtosis_ge_three_iff` prove the stated threshold under
a nondegenerate denominator.

**Missing:** nothing for the algebraic equivalence.
Its probability interpretation requires K-43.

### K-45. Eq. 18: κ for Gaussian switching means — not ok as a mixture metric

[Kappa/GaussianSwitchingMean.lean](Stats/Kappa/GaussianSwitchingMean.lean):
`gaussianSwitchingMean_kappa1` calculates κ on
`gaussianSwitchingMeanMAD`, whose values are supplied by definition.

**Missing:** actual one-/two-summand mixture MAD calculations and identification
of the source parameters and admissible domain.

### K-46. Negative κ and necessity of bimodality — not ok completely

`gaussianSwitchingMean_kappa_neg_iff` establishes an algebraic negative-value
criterion under its hypotheses.

**Missing:** an actual distributional negative-κ example and any general theorem
excluding negative κ for unimodal laws. A criterion for one supplied formula
does not establish that broad source assertion.

### K-47. Student/Pareto comparisons, CLT rates and confidence intervals — not ok

The text connects κ to data requirements and normal-approximation reliability.

**Missing:** quantitative theorems for sample-mean errors and confidence
intervals, extremes, and the claimed $√(n log n)$ crossover.
The source's heuristics and numerical observations are not formal error bounds.

## 3. Statistical Differences between Binary Forecasts and Real-World Payoffs

Source: [arXiv:1907.11162v3](https://arxiv.org/abs/1907.11162v3).
Main module: [BinaryForecasts.lean](Stats/BinaryForecasts.lean).

**Paper verdict: not ok.** Several integral and derivative calculations are
proved, including the exact strong-Pareto ratio and the displayed Gaussian
sensitivity expression. Neither named theorem has its complete stochastic
statement formalized. Some statements in the source also require correction:
Theorem 1 needs restrictions on the payoff, and Eq. 8 differentiates a different
quantity from the originally defined payoff gap.

### BF-01. Definition 1: events and measurable random variables — ok as infrastructure

The imported Mathlib probability and measure framework provides measurable
spaces, events and measurable random variables.

**Missing:** nothing for these standard definitions. This does not supply the
specific forecast experiment or joint law needed later in the paper.

### BF-02. Definition 2: binary forecast/payoff — not ok completely

`heaviside` in [Conflation.lean](Stats/BinaryForecasts/Conflation.lean) represents
the scalar indicator of a threshold. Its value on the upper tail is proved
constant.

**Missing:** an explicit measurable random variable on a probability space with
two arbitrary payoff values, and its connection to forecast outcomes. A scalar
step function supplies the payoff kernel, rather than the complete experiment.

### BF-03. Definition 3: open continuous payoff — not ok completely

`I1` accepts an arbitrary real-valued payoff function.

**Missing:** the source's stochastic model of an unbounded payoff, its
measurability and support conditions, and the integrability assumptions needed
when an expectation or conditional expectation is used.

### BF-04. Definition 4: characteristic scale and classes D₁/D₂ — not ok generally

[CharacteristicScale.lean](Stats/BinaryForecasts/CharacteristicScale.lean)
proves a particular Pareto ratio.

**Missing:** predicates for the distribution classes, a general conditional
expectation formulation, and the corresponding limit theorems. Assigning a
class in a comment is not a proof that an arbitrary law belongs to it.

### BF-05. Strong-Pareto characteristic-scale formula — ok

`characteristicScale_pareto` proves the ratio
$E[X;X>K]/(K P(X>K))=α/(α-1)$ for $α>1$, $l>0$, $K≥l$.
`characteristicScale_pareto_gt_one` proves that the factor exceeds one.

**Missing:** nothing for this exact Pareto integral statement. The tail
expectation and survival formulas are established by integration.

### BF-06. Exponential borderline case — ok for the integral formulas

[Exponential.lean](Stats/BinaryForecasts/Exponential.lean):
`exp_survival_eq`, `exp_tail_expectation_eq` and `exp_conditional_excess`
prove, for $λ>0$ and $K≥0$,
$P(X>K)=exp(-λK)$ and $E[X|X>K]-K=1/λ$ as density-integral identities.

**Missing:** nothing for these analytic formulas. There is no separately
assembled limit theorem placing the law in a formal D₁ predicate.

### BF-07. Definition 5: I₁ and I₂ — ok as integral definitions

`I1 g f K` is the integral of $g(x)f(x)$ over $(K,∞)$.
`I2 g f K` is $g(K)$ times the integral of $f(x)$ over that interval.

**Missing:** nothing in the definitions themselves. Using these values as
finite expectations requires integrability: Lean's real integral is total and
returns zero for a nonintegrable integrand.

### BF-08. Constant-payoff and Heaviside equality — ok

`I1_eq_I2_of_constantOn` proves equality when $g=g(K)$ almost everywhere
on the upper tail. `I1_eq_I2_heaviside` proves the threshold-indicator case.

**Missing:** nothing for the sufficient direction.

### BF-09. Definition 5's “if and only if” and general strict gap — not ok

The source states that equality occurs only for a constant payoff above $K$.
The Lean theorem proves only the sufficient direction.

**Missing:** a valid converse with hypotheses that rule out cancellation and
variation outside the density's support. Without these restrictions a payoff
can vary where $f=0$ while preserving equality. For unrestricted signed or
nonmonotone payoffs, integral cancellation is another obstruction. A strict
gap for an increasing payoff needs positivity of the density on a set where
$g(x)>g(K)$.

### BF-10. Theorem 1: general convergence of I₁/I₂ — not ok

The theorem is stated after the definition of an arbitrary payoff $g$, but its
limit is the characteristic scale defined for $g(x)=x$.

**Missing:** a corrected payoff hypothesis and a general distribution theorem.
The literal statement is false even for a strictly increasing, integrable
payoff: for an Exp(1) density and $g(x)=exp(x/2)$, at $K≥0$,
$I₁=2exp(-K/2)$ and $I₂=exp(-K/2)$, so their ratio is two.
The underlying law has characteristic scale one. This counterexample is an
analytic check in this review; it is not a new Lean theorem.

### BF-11. Theorem 1's strong-Pareto, linear-payoff specialization — ok

`pareto_I1_div_I2_eq` proves the exact ratio for $g(x)=x$.
`pareto_I1_div_I2_tendsto` proves the corresponding `Tendsto` statement.

**Missing:** nothing for this specialization. For a payoff $x^p$, the factor
instead depends on $p$; it cannot be assigned the linear-payoff factor without
an additional argument.

### BF-12. Theorem 1 for all regularly varying tails — not ok as assembled

The repository now has a full measurable slowly varying Karamata theorem and
call-price asymptotics in the regular-variation modules.

**Missing:** their application to the binary-forecast ratio with an identified
survival law, the appropriate first-moment tail identity, and the explicit
limit for the admissible payoff class. The ingredients are stronger than a
Pareto example, but the complete binary-forecast theorem is not stated.

### BF-13. Eq. 6: Gaussian truncated first moment — ok

`gaussian_I1_id_eq` proves
$∫_K^∞ xφ(x)dx=φ(K)$ for $K≥0$.
[SigmaClosures.lean](Stats/BinaryForecasts/SigmaClosures.lean) also proves
`integral_x_gaussianPDF_σ` and `integral_gaussianPDF_σ` for positive $σ$:
the tail first moment is $σφ(K/σ)$ and the tail probability is $1-Φ(K/σ)$.

**Missing:** nothing for the stated integral formulas.

### BF-14. Gaussian I₁/I₂ limit and characteristic scale — not ok

The normal tail and Mills bounds are available in the Black–Scholes modules.

**Missing:** the explicit Gaussian ratio limit for $g(x)=x$ and its use in a
formal D₁ classification. Computing numerator and denominator is not yet the
limit theorem.

### BF-15. Definition 6: Pareto payoff-equivalent probability — ok as a formula

`correctedProbability_pareto` proves
$p^*=E[X;X>K]/K=(α/(α-1))P(X>K)$.

**Missing:** nothing for this algebraic identity. It does not always define a
probability: at $K=l$ the value is $α/(α-1)>1$. The paper itself acknowledges
values exceeding one in its example table. A probability interpretation needs
an additional range condition.

### BF-16. Corrected-probability tables and inverse quantiles — not ok completely

The symbolic Pareto factor is proved.

**Missing:** the Gaussian inverse-tail/quantile calculation, formal numerical
bounds for the tabulated values, and explicit admissibility checks for entries
that are described as probabilities.

### BF-17. Mean-preserving lognormal uncertainty example — not ok completely

The source considers a lognormal family with mean $X₀$, decreasing probability
of exceeding $X₀$, and increasing truncated first moment. Related genuine
lognormal tail limits exist in
[LoulakisLognormal.lean](Stats/Kappa/LoulakisLognormal.lean).

**Missing:** the exact source example's two erf formulas, monotonicity in $σ$,
and the scaling from the mean-one family to $X₀$ as one connected theorem.
With the conventional log-location parameter, the family has location
$log(X₀)-σ²/2$; the source's printed parameter $X₀-1/σ²$ does not express that
mean constraint.

### BF-18. Remark 1: uncertainty increases the payoff gap — not ok generally

Positive second derivatives and a finite two-point Jensen example are proved
in narrower settings.

**Missing:** a probability model for the uncertain parameter, integrability,
convexity of the actual target quantity, and Jensen's inequality applied to
that parameter law. Higher kurtosis alone does not establish every asserted
comparison of payoff gaps.

### BF-19. Eq. 8: displayed Gaussian derivative expression — ok for A − B

Let $A(σ)=σφ(K/σ)$ and $B(σ)=1-Φ(K/σ)$.
[SigmaSensitivity.lean](Stats/BinaryForecasts/SigmaSensitivity.lean):
`gaussianEq8_sigmaSensitivity_eq_phi` and
`gaussianEq8_sigmaSensitivity_eq` prove the derivative calculation giving
$φ(K/σ)((K-1)K³-(K-2)Kσ²)/σ⁵$.

**Missing:** nothing for the derivative of the displayed $A-B$ expression.
The integral closures are proved separately in BF-13.

### BF-20. Eq. 8 as a proof about the originally defined I₁ − I₂ — not ok

For the linear payoff, the definition gives $I₂=K B$, whereas the proof in the
source and the existing Gaussian derivative module subtract $B$.

**Missing:** restore the factor $K$, identify the actual gap as $A-KB$, and
prove its second derivative and the stochastic-parameter comparison.
The corrected derivative simplifies analytically to
$K²φ(K/σ)/σ³$, which is positive for $K>0$, $σ>0$.
The existing derivative lemmas can support this repair; the complete corrected
gap theorem has not been assembled.

### BF-21. Eq. 8's asserted positivity for all σ > 0 — not ok

`gaussian_eq8_polynomial_pos` proves positivity at $σ=1$.

**Missing:** a valid general sign statement. The displayed expression is not
positive for all positive parameters: at $K=1/2$, $σ=1/10$, its numerator
$(K-1)K³-(K-2)Kσ²$ is $-11/200$.
The unit-variance factorization cannot establish the general claim.
This issue concerns the displayed $A-B$ expression; the corrected $A-KB$ gap
has the positive derivative described in BF-20.

### BF-22. Eq. 9: Pareto conditional-tail-mean sensitivity — ok

[ParetoSensitivity.lean](Stats/BinaryForecasts/ParetoSensitivity.lean):
`paretoTailMean_iteratedDeriv_two` proves the literal second derivative of
$αK/(α-1)$, and `paretoTailMean_secondDeriv_alpha_pos` proves positivity:
$2K/(α-1)^3>0$ when $α>1$ and $K>0$.

**Missing:** nothing for the conditional-mean derivative.
The ratio $I₁/I₂$ itself has second derivative $2/(α-1)^3$; the factor $K$
belongs to the conditional mean.

### BF-23. Remark 2: binary forecasts and Brier scores have thin tails — not ok fully

`brierTerm_bounded` proves bounds on $(f-y)^2$ for $f,y∈[0,1]$.
[Brier.lean](Stats/BinaryForecasts/Brier.lean) now constructs the measurable
score average, proves its bounds and all nonnegative-order moment
integrability, and proves that its upper tail beyond one has measure zero.

**Missing:** a stated interpretation of "thin tails" connecting bounded
support to the particular tail-class definition used elsewhere in the paper,
and the corresponding empirical binary-frequency construction. A bounded
distribution makes some tail-ratio denominators identically zero, so it
cannot be inserted into those definitions without checking their conventions.

### BF-24. Definition 7: M4 forecasting scores — not ok

There is no formal model of the two M4 score definitions in this project.

**Missing:** the normalized losses, admissible denominators, forecast/realized
random variables, and any claimed comparison of their moment requirements.
A zero denominator also requires a convention or a nonzero hypothesis.

### BF-25. Remark 3: binary empirical frequency is asymptotically normal — not ok

[SinglePointForecasts.lean](Stats/SinglePointForecasts.lean) contains scalar
variance bounds, and the Bernoulli module contains scalar CGF derivatives.

**Missing:** an iid Bernoulli sample, its actual empirical-mean variance, and
the central limit theorem. Without independence or an appropriate dependence
condition, the stated $1/n$ variance and normal limit need not hold.

### BF-26. Theorem 2: every finite-sample Brier-score moment is finite — ok

The source is the Brier-score definition at lines 585–595 and Theorem 2 at
lines 629–635 in
`papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`.
The underlying events may be any measurable events; in the paper they are
preimages of forecast ranges under the observed random variables.

[Brier.lean](Stats/BinaryForecasts/Brier.lean) defines `brierOutcome` and
`brierAverage` from measurable forecasts and event indicators on a probability
space. For $n>0$ and forecasts in $[0,1]$:

- `measurable_brierAverage` proves measurability;
- `brierAverage_mem_unit_interval` proves $0≤λ_n(ω)≤1$;
- `integrable_brierAverage_rpow` proves integrability of $λ_n^q$ for every
  real $q≥0$;
- `brierAverage_moment_mem_unit_interval` proves $0≤\mathbb{E}[λ_n^q]≤1$.

**Missing:** nothing for the usual nonnegative-order moment claim.
No independence assumption is used. Negative orders are excluded: a zero
score can have a divergent reciprocal moment, so those are not covered by
the paper's boundedness argument.

### BF-27. Remark 4: profit/loss conditional on survival follows the payoff law — not ok

No stopped trading process or survival-conditioned law is defined.

**Missing:** a process, absorbing boundary, survival event, and a precise
conditional-law statement. Conditioning generally changes a distribution;
equality with an unconditional payoff law needs explicit assumptions.

### BF-28. Remark 5: inseparability of probability and payoff — not ok literally

`inseparability_const` and `inseparability_affine_linearity` identify
equality cases. `inseparability_jensen_strict` supplies a strict two-point
convexity result.

**Missing:** a corrected, normalized general statement and the continuous or
general discrete integral theorem with integrability and strictness
conditions. A universal inequality for every measurable $g$ is false:
constant and affine payoffs supply equality cases. Jensen's inequality uses
the probability-weighted mean; it does not justify replacing that mean by an
unweighted average or by the interval's Lebesgue measure.

### BF-29. Appendix A: first four Bernoulli CGF derivatives — ok analytically

[Bernoulli.lean](Stats/BinaryForecasts/Bernoulli.lean):
`bernoulli_kappa1` through `bernoulli_kappa4` compute derivatives at zero
of $log(1-p+p exp(t))$, with the stated parameter assumptions.

**Missing:** nothing for these derivative identities.

### BF-30. Appendix A: cumulants and convergence rates of the sample tally — not ok

The source gives the cumulants of an average of $N$ Bernoulli observations and
draws LLN/CLT rate conclusions.

**Missing:** identify the defined scalar CGF with the actual Bernoulli law,
prove the iid-average CGF and its $N$ scaling, and establish a quantitative
normal approximation in a specified metric. A kurtosis correction of order
$1/N$ is not itself a theorem that the full distribution converges at that
rate.

### BF-31. Appendix B: probability integral transform — not ok in this formalization

The source invokes the uniform law of $F_X(X)$ for a continuous CDF.

**Missing:** a theorem applying the transform to the source's forecast model,
including continuity and an appropriate generalized inverse. The imported
probability framework alone does not make this paper-specific claim a proved
declaration.

### BF-32. Appendix B: Beta forecast probabilities and Brier-score distribution — not ok

The source derives characteristic-function expressions and distributional
special cases for the Brier score.

**Missing:** the forecast-probability law, the dependence between forecast
and outcome, the score pushforward, and the stated transforms/densities.
The scalar boundedness theorem does not derive these laws.

### BF-33. Nonlinear-payoff decompositions and examples — not ok completely

[CarrMadan.lean](Stats/CarrMadan.lean) proves a smooth static option-payoff
replication formula under its own analytic assumptions.

**Missing:** the source's softplus function and its claimed representation of
arbitrary nonlinear payoffs, an approximation topology and admissible class,
and the finite illustrated trading-payoff computations. General expectation
linearity also requires a justified finite sum or an interchange theorem.

### BF-34. General VaR/CVaR and calibration-to-performance claims — not ok

Pareto-specific VaR, CVaR and payoff calculations exist elsewhere in the
project.

**Missing:** a general VaR subadditivity counterexample, a general coherence
theorem for CVaR, and a decision model linking probability calibration to the
claimed realized or survival-conditioned performance. Distribution-specific
algebra does not prove those broader assertions.

## 4. Branching Epistemic Uncertainty and the Thickness of Tails

Source: [arXiv:1912.00277v2](https://arxiv.org/abs/1912.00277v2).
Main module: [EpistemicUncertainty.lean](Stats/EpistemicUncertainty.lean).

**Paper verdict: not ok.** The finite binomial moment algebra and several
inequalities are proved. The Gaussian mixture itself, its distributional
moments, the CLT argument and the Normal–Gamma compound law are not formalized.
This source has no active numbered Theorem or Proposition environment; both
numbered Remarks and the mathematical claims are audited below.

### EU-01. Remark 1: collapse the branching scenarios into one distribution — not ok

`epistemicSigmaMoment` defines a binomial-weighted finite sum.

**Missing:** the probability space of branches, its pushforward to a dispersion
law, the Gaussian mixture measure, and proof that the branching construction
and collapsed representation have the same law.

### EU-02. Remark 2: uncertainty around a zero probability implies a positive floor — not ok

No probability-estimation or posterior model is defined.

**Missing:** a precise model of estimation error and a justified lower bound.
A symmetric error of one percentage point around zero cannot itself be a
probability-valued error model with both signs. An uncertain estimate alone
does not imply a universal strictly positive lower bound on the true
probability.

### EU-03. Section II: repeated integration over parameter uncertainty — not ok

The source defines nested mixtures over uncertain positive scale parameters.

**Missing:** measurable probability kernels, the iterated mixture measure,
normalization, and interchange of the required integrals. The existing finite
polynomial expressions do not implement this general construction.

### EU-04. Section II: the 2ⁿ-component Gaussian density — not ok

The source's sign-vector construction and finite Gaussian density mixture are
described in comments.

**Missing:** the actual density/measure and an equality with the recursively
constructed model. For Gaussian standard deviations, require positive base
scale and positive multiplicative factors; the algebraic Lean identities alone
permit parameter values outside that density model.

### EU-05. Section III: constant-error collapse to binomial weights — not ok fully

The binomial weights and scale values are present in `epistemicSigmaMoment`.

**Missing:** the counting/pushforward theorem identifying those weights with
the equiprobable sign tree and the resulting Gaussian mixture density.
The weighted expression is defined directly.

### EU-06. Arbitrary natural-order dispersion moment — ok for the weighted sum

`epistemicSigmaMoment_eq` proves, for all natural $n,k$,
$epistemicSigmaMoment(n,k,σ,ε)=σ^k M_k(ε)^n$, where
$M_k(ε)=((1+ε)^k+(1-ε)^k)/2$.

**Missing:** nothing for this finite-sum identity. It is a binomial-theorem
calculation, not an integral against a constructed Gaussian mixture.

### EU-07. Second- and fourth-order layer factors — ok

`epistemicMomentFactor_two` and `epistemicMomentFactor_four` prove
$M₂=1+ε²$ and $M₄=1+6ε²+ε⁴$.

**Missing:** nothing for these polynomial identities.

### EU-08. Dispersion second and fourth moments — ok for the defined sum

`epistemicVariance_eq` and `epistemicSigmaFourthMoment_eq` prove
the weighted second/fourth powers of the scale.

**Missing:** nothing for the finite sums. Despite the first theorem's name,
its conclusion does not mention the variance of an outcome random variable
$X$.

### EU-09. First raw outcome moment and preservation of μ — not ok

The source states $E[X]=μ$ for the mixture.

**Missing:** a Gaussian mixture random variable, first-moment integrability,
and the expectation calculation.

### EU-10. Second raw outcome moment and variance — not ok as probability statements

The source gives $E[X²]=μ²+σ²(1+ε²)^n$ and
$Var(X)=σ²(1+ε²)^n$.

**Missing:** identify the weighted dispersion second moment with the mixture's
central second moment, then prove the raw-moment and variance equalities.
EU-08 proves only the weighted scale expression.

### EU-11. Third raw outcome moment and zero skewness — not ok

The source gives $E[X³]=μ³+3μσ²(1+ε²)^n$ and zero skewness.

**Missing:** the actual third-moment integral, symmetry/centering, and
nondegenerate variance for the skewness ratio.

### EU-12. Fourth raw outcome moment — not ok literally or distributionally

The source prints $3μ⁴$ as the leading term.

**Missing:** correct it to $μ⁴$, then establish the Gaussian-mixture moment
identity. For a mixture with common mean $μ$ and random standard deviation
$Σ$, the raw fourth moment is
$μ⁴+6μ²E[Σ²]+3E[Σ⁴]$. Even at zero uncertainty, the printed $3μ⁴$
does not give the noncentered Gaussian fourth moment.
The module proves the dispersion fourth moment, without this outcome-moment
bridge.

### EU-13. Symmetry of the outcome distribution — not ok

The source states that layering scale uncertainty preserves symmetry.

**Missing:** construct the common-center Gaussian mixture and prove invariance
of its law under reflection about $μ$.

### EU-14. Closed raw- and excess-kurtosis expressions — ok algebraically

`epistemicKurtosis_eq` and `epistemicExcessKurtosis_eq` prove
$3(1+6ε²+ε⁴)^n/(1+ε²)^{2n}$ and that quantity minus three, assuming $σ≠0$.

**Missing:** nothing for the defined expression. Its interpretation as the
kurtosis of $X$ remains **not ok** until EU-10 and EU-12 are proved.

### EU-15. Kurtosis at least three, and strictly greater with uncertainty — ok algebraically

`epistemicMomentFactor_four_ge_two_sq`,
`epistemicMomentFactor_four_strict`,
`epistemicKurtosis_ge_three`, `epistemicKurtosis_gt_three` and
`epistemicExcessKurtosis_nonneg` prove the inequalities.
Strictness requires $n≥1$, $σ≠0$ and $ε≠0$.

**Missing:** nothing for these scalar inequalities. A kurtosis inequality is
not a regularly varying tail theorem.

### EU-16. Geometric divergence of variance and kurtosis as n → ∞ — not ok

The exact scalar formulas and finite-depth inequalities are available.

**Missing:** explicit `Tendsto` divergence statements, with $σ≠0$ and
$ε≠0$ where required, and their outcome-law interpretation. At $ε=0$
the asserted explosions do not occur.

### EU-17. Finite-depth or infinite-depth power-law tail generation — not ok

The module proves growing moment expressions.

**Missing:** a precise tail-class claim, the distribution under study and, for
an infinite construction, a limit law. A finite mixture of nondegenerate
Gaussians has all moments and a moment generating function finite at every
real argument. Larger kurtosis by itself does not make that finite mixture
regularly varying. An infinite-depth distribution requires a separate
existence and tail analysis.

### EU-18. Constant-error exceedance formula and numerical tables — not ok

The source gives a weighted erfc sum and ratios to a baseline Gaussian.

**Missing:** the actual mixture survival integral, the weighted erfc identity,
and certified numerical values/error bounds. The displayed threshold must be
centered by $μ$, unless the calculation has explicitly set $μ=0$.

### EU-19. Section IV: decaying-error variance product — not ok as a variance derivation

`decayingErrorVariance` is defined as
$σ²∏_{i<n}(1+ε₁²κ^{2i})$.

**Missing:** derive this product from independent nonidentical sign errors
and identify it with the mixture's variance. The product formula is currently
the definition of the quantity being bounded.

### EU-20. Decaying-error product is above the base and increases with depth — ok

`decayingErrorVariance_ge_base` and `decayingErrorVariance_mono`
prove the finite-product inequalities.

**Missing:** nothing for the scalar function. Their hypotheses and conclusions
do not construct or compare outcome probability laws.

### EU-21. Decaying-error fourth central moment — not ok

The source gives
$3σ⁴∏_{i<n}(1+6ε₁²κ^{2i}+ε₁⁴κ^{4i})$.

**Missing:** the product-moment calculation and its identification with the
actual fourth central moment. The constant-error binomial theorem does not
prove this nonidentical-error result.

### EU-22. Capped moments and convergence for decaying errors — not ok

Only finite-product monotonicity is proved.

**Missing:** infinite-product convergence, quantitative bounds and the
limiting moment theorems. Require actual decay, such as $0≤κ<1$;
the source's interval $[0,1]$ includes $κ=1$, which reduces to the
nondecaying case. The example coefficients 1.23 and 9.88 are not certified.
A joint limit $κ→1$, $ε→0$ also requires control of their relative rates.

### EU-23. Section V: exact log-additivity — ok

`log_multiplicative_error` proves
$log(λ̂∏(1+ε_i))=log(λ̂)+Σlog(1+ε_i)$ for positive $λ̂$ and factors.

**Missing:** nothing for this finite algebraic identity.

### EU-24. Upper bound log(1 + ε) ≤ ε — ok

`log_one_add_le_self` proves the inequality for $ε>-1$.

**Missing:** nothing for the upper bound.

### EU-25. Log linearization and accumulated approximation error — not ok

The source replaces each log factor by its first-order error.

**Missing:** a valid two-sided remainder estimate on a specified parameter
range and control of the sum of remainders. A one-sided inequality does not
give an approximation theorem. The suggestion that
$ε-ε²/2≤log(1+ε)$ for arbitrary small signed errors has been removed
from the old code comment: that inequality fails for negative $ε$
sufficiently close to zero.

### EU-26. CLT for the errors and lognormal precision law — not ok

The source appeals to independent errors with finite variances bounded below.

**Missing:** a normalized convergence-in-distribution theorem, centering and
an appropriate Lindeberg/Lyapunov or iid hypothesis, as well as log-factor
moment assumptions and the approximation control in EU-25.
Finite variances and a positive lower bound alone do not guarantee a CLT for
nonidentically distributed independent variables. Nor does zero mean of
$ε_i$ imply zero mean of $log(1+ε_i)$. An unnormalized sum whose variance
grows with $n$ does not converge to a fixed normal law.

### EU-27. Normal–Lognormal precision mixture and its moments — not ok

There is no formal compound density or probability law for this section.

**Missing:** the mixture construction, integral interchange and its moments.
For centered Gaussian precision $Λ$ with $log(Λ)∼N(0,S²)$,
the raw kurtosis is $3exp(S²)$ and the excess is
$3(exp(S²)-1)$. The source's displayed “kurtosis” needs that excess
convention. This is distinct from the constant-error finite-sum model.

### EU-28. Gamma/Lognormal moment and coefficient-of-variation matching — not ok

The source matches Gamma shape/rate to a lognormal precision law.

**Missing:** the actual two distributions' moments and the matching formulas
as proved identities. Equality of the first two moments does not by itself
provide a distributional approximation error bound.

### EU-29. Gamma and Lognormal tail/hazard comparison — not ok

No hazard-rate or stochastic-order formalization is present.

**Missing:** precise definitions and valid tail limits. In the source's
density $β^α y^{α-1}exp(-βy)/Γ(α)$, $β$ is a rate, so the Gamma
hazard limit is $β$, not $1/β$. This Gamma law has a finite MGF for
positive arguments below $β$ and is not heavy-tailed under the standard
“no positive exponential moment” definition. The source's broad
slower-than-exponential characterization needs correction.

### EU-30. Gamma as a lower bound for Lognormal, then for the outcome mixture — not ok

The source uses a same-CV Gamma approximation to support conclusions about
the lognormal mixture.

**Missing:** specify the order or error metric, prove the precision-law
comparison and prove that the mixing operation preserves the desired outcome
comparison. Matching mean/CV or comparing right tails of precision is
insufficient: large outcome values also depend on behavior near zero
precision.

### EU-31. Section VI: evaluate the Normal–Gamma compound integral — not ok

The integral yields a scaled Student density in the source.

**Missing:** normalization of the Gamma precision law, integrability,
evaluation of the Gamma integral and equality of probability measures.
For the printed rate parameterization, the resulting Student law has
$2α$ degrees of freedom and scale $sqrt(β/α)$; calling $β$ its
standard Student scale requires correction or a declared alternative
parameterization. The repository's separate Student formulas do not establish
this compound-law theorem.

### EU-32. Increasing epistemic uncertainty decreases the Student tail index — not ok

The source sets $α=1/(exp(S²)-1)$ and draws a heavier-tail conclusion.

**Missing:** the parameter monotonicity theorem, the Student survival
asymptotic and their composition with EU-31. At $S²=0$ the parameter formula
also requires a limiting interpretation.

### EU-33. Exponential–Gamma, Gamma–Gamma and Poisson–Gamma extensions — not ok

The discussion mentions Lomax, beta-prime/compound-Gamma and negative-binomial
laws as further examples.

**Missing:** the corresponding probability kernels, mixing-law identities,
parameter conventions and relevant tail or moment statements. No project
module proves these discussion claims as a connected construction.

### EU-34. General out-of-sample risk and universal thickening claims — not ok

The formal module treats specific finite weighted expressions.

**Missing:** a quantified predictive/decision model and hypotheses linking
epistemic uncertainty to the specified future loss law. The broad
philosophical and empirical conclusions are not consequences of the
polynomial identities alone.

## 5. What You See and What You Don't See: The Hidden Moments of a Probability Distribution

Source: [arXiv:2004.05894v1](https://arxiv.org/abs/2004.05894v1).
Main module: [HiddenMoments.lean](Stats/HiddenMoments.lean).

**Paper verdict: not ok.** The strong-Pareto tail-moment integral and several
polynomial/Beta-kernel calculations are proved. Proposition 1, the actual
iid-maximum law and the pushforward law of the hidden moment are missing.
The source uses a Fréchet approximation where an exact finite-sample Pareto
calculation has a different law.

### HM-01. Visible-plus-hidden moment decomposition — not ok as assembled

The source splits the population moment at the random sample maximum.

**Missing:** an iid sample and its maximum, integrability of the population
moment, and the integral-splitting theorem applied at that random threshold.
The repository computes the hidden integral for a deterministic threshold.

### HM-02. Eq. 2: strong-Pareto p-th tail moment — ok

`paretoTailMoment_eq` proves
$∫_K^∞ x^p αl^αx^{-α-1}dx=αl^αK^{p-α}/(α-p)$
for $l>0$, $α>0$, $p<α$, $K≥l$.

**Missing:** nothing for this exact integral. It is not merely a rearrangement
of a supplied closed expression.

### HM-03. Zeroth and first tail-moment specializations — ok

`paretoTailMoment_at_zero` identifies the survival function.
`paretoTailMoment_at_one` identifies the first tail expectation.

**Missing:** nothing for these specializations. The source's introductory
$L^{-α}$ survival coefficient and later $L^α$ scale formulas need a
consistent scale convention before combining its displayed statements
literally.

### HM-04. Exact iid sample-maximum CDF — not ok as a probability theorem

`paretoSampleMaxCDF` in
[Drawdown.lean](Stats/RiskMeasures/Drawdown.lean) is defined by
$(1-(l/k)^α)^n$.

**Missing:** the iid Pareto random variables, the finite maximum, and proof
that its law has this CDF for $k≥l$. The function is not a globally defined
CDF below the support unless extended there appropriately; also require a
nonempty sample.

### HM-05. Replacing the finite maximum by a Fréchet law — not ok exactly

For a finite strong-Pareto sample, the exact CDF is
$(1-(l/k)^α)^n$ on $k≥l$.
The Fréchet expression is $exp(-n(l/k)^α)$.

**Missing:** a limit theorem or a quantified approximation in the intended
range. The two expressions are unequal at finite $n$. The proposition's
“satisfactorily approximated” assumption does not specify an error tolerance
or an asymptotic mode strong enough to give an exact density conclusion.

### HM-06. Proposition 1: density of the hidden p-th moment — not ok

There is no Lean probability-law theorem for the density printed in
Proposition 1.

**Missing:** HM-04 or a justified Fréchet approximation, definition of
$μ_{K_n,p}$ as a random variable, the monotone change of variables,
Jacobian, support, normalization and equality of laws. The current
deterministic tail-moment formula is an ingredient rather than this result.

### HM-07. Remark 1: sample survival ratio is exponential — not ok literally

For a finite continuous iid sample, the remaining survival mass at its
maximum is supported in $[0,1]$. An ordinary exponential distribution has
positive mass above one.

**Missing:** replace the exact assertion by the Beta(1,n) law, or state and
prove the scaled exponential asymptotic. The source's exponential expression
comes from the Fréchet approximation.

### HM-08. Candidate Beta CDF and its maximum-CDF substitution — ok algebraically

`paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF` proves the substitution
between the two defined real functions. The candidate ratio CDF is
$1-(1-y)^n$.

**Missing:** nothing for this algebraic equality. Its actual probability-law
interpretation remains **not ok** until the iid maximum and pushforward are
constructed. Outside $[0,1]$ the polynomial requires a support extension
before being called a CDF on the whole real line.

### HM-09. Derivative of the candidate CDF — ok

`paretoSampleSurvivalRatioPDF_eq_deriv` proves the derivative
$n(1-y)^{n-1}$.

**Missing:** nothing for the polynomial derivative. Normalization and
identification with the law of the actual sample ratio are separate steps.

### HM-10. Beta-kernel mean 1/(n+1) — ok as an integral

`paretoSampleSurvivalRatio_mean` proves
$∫₀¹ y n(1-y)^{n-1}dy=1/(n+1)$ for $n≥1$.

**Missing:** nothing for this integral. Calling it $E[(l/K_n)^α]$
requires the probability-law bridge in HM-08.

### HM-11. Difference between 1/n and 1/(n+1) — ok algebraically

`paretoSampleSurvivalRatio_mean_asymptotic_gap` proves
$1/n-1/(n+1)=1/(n(n+1))$.

**Missing:** nothing for the equality. An explicit big-O or distributional
limit statement is not present.

### HM-12. Scaled sample-survival ratio converges to Exp(1) — not ok

The candidate Beta CDF and the exact mean integral are available.

**Missing:** a convergence-in-distribution theorem for $n(1-F(K_n))$
and the identification of its limiting exponential law. A mean comparison
alone does not establish convergence of laws.

### HM-13. Expected general-p hidden moment and Gamma formula — not ok

The source gives the Fréchet-model expression
$l^p n^{p/α-1}Γ(1-p/α)$.

**Missing:** the hidden-moment pushforward, expectation integrability, the
Gamma calculation and a precise finite-sample/asymptotic distinction.
For the exact strong-Pareto model, writing $r=1-p/α>0$, the expected
hidden moment is analytically
$l^p Γ(r)Γ(n+1)/Γ(n+1+r)$, whose leading term is the printed
Fréchet expression. This exact formula and its Gamma-ratio asymptotic are
not proved in the project. This review's formula is a direct analytic check,
not a newly added Lean result.

### HM-14. Gaussian hidden moment in terms of incomplete Gamma — not ok

The project has Gaussian tail infrastructure and first-moment integrals.

**Missing:** the general $p$ incomplete-Gamma tail identity on the stated
threshold domain. The source's displayed integrand omits the $x^p$ factor
even though the right side depends on $p$; that factor must be restored.

### HM-15. Gaussian sample-maximum density — not ok

The normal CDF and PDF are available.

**Missing:** the iid normal sample, the maximum-law theorem and the density
$nφ(k)Φ(k)^{n-1}$, including its support and normalization.

### HM-16. Gaussian hidden-mass integral over positive maxima — not ok

The source prints $(1-2^{-n})/(n+1)$ for its integral over $K≥0$.

**Missing:** a correct evaluation. Substituting $u=Φ(K)$ into
$∫₀^∞(1-Φ(K))nφ(K)Φ(K)^{n-1}dK$ gives
$[1-(n+2)2^{-(n+1)}]/(n+1)$.
At $n=1$ this is $1/8$, whereas the source's expression gives $1/4$.
Integrating over the whole real line instead gives $1/(n+1)$.
These are analytic checks; neither Gaussian hidden-mass integral is a proved
project theorem.

### HM-17. Distribution independence of hidden probability mass — not ok generally

The source emphasizes that the $p=0$ result does not depend on tail thickness.

**Missing:** the probability integral transform for a continuous law,
independence, the maximum-order-statistic law and the Beta pushforward.
A Pareto-specific polynomial identity is not the distribution-free
probability theorem. Atomic laws require a different formulation.

### HM-18. Higher-moment numerical comparisons and convergence claims — not ok

The source plots hidden moments and compares Pareto and Gaussian behavior.

**Missing:** formal quantitative bounds for the compared expectations and
rates, or certified numerical integrations. The existing deterministic
Pareto formula does not validate all sample-size plots.

### HM-19. A one-sided sample mean necessarily underestimates the true mean — not ok

The conclusion's statement about the actual sample mean is too strong.

**Missing:** a corrected target and a proved bias/probability statement.
A finite iid sample mean is unbiased when the first moment exists and can
exceed the population mean; a single sufficiently large Pareto observation
already supplies such an example. The population integral truncated at the
sample maximum is a different quantity and omits positive tail mass.
The formalization must distinguish that truncated integral from the arithmetic
mean of the observed sample.

### HM-20. Confidence about the size of the unseen and risk applications — not ok

The module provides deterministic tail-moment expressions and a candidate
Beta-kernel mean.

**Missing:** the relevant estimator, its distribution, confidence/coverage
bounds and the decision or loss model for the stated applications.
A hidden population moment is not by itself an estimator guarantee.

## 6. On Single Point Forecasts for Fat-Tailed Variables

Source: [arXiv:2007.16096v1](https://arxiv.org/abs/2007.16096v1).
Main module: [SinglePointForecasts.lean](Stats/SinglePointForecasts.lean).

**Paper verdict: not ok.** The exponential-growth law, actual finite-sample
survival mean/variance/MSE, corrected RMSE bound and heavy-tailed rate
counterexample are proved, alongside scalar formulas and the strong-Pareto
moment threshold. The paper's empirical and normative claims, general
forecasting impossibility, LLN/CLT and general rate-family assertions
remain separate.
The source has no active named Theorem or Proposition; all nine numbered
Remarks and nine Main Statements are covered here.

### SP-01. Exponential-growth density expression equals Pareto expression — ok

`exp_growth_density_eq_pareto` proves
$λ/(tx)(X₀/x)^{λ/t}=paretoDensity(X₀,λ/t,x)$ for positive parameters
and $x>0$.

**Missing:** nothing for the pointwise algebraic identity.

### SP-02. Exponential growth of an exponential rate has a Pareto law — ok on the positive domain

The source considers $X=X₀ exp(tr)$ with $r∼Exp(λ)$.

[SinglePointForecasts/ExponentialLaw.lean](Stats/SinglePointForecasts/ExponentialLaw.lean)
constructs the actual pushforward of Mathlib's supported `expMeasure λ`.
For positive initial value, elapsed time and rate parameter, the full
survival is one below $X₀$ and $(X₀/s)^{λ/t}$ above it. The law is proved
normalized. This identifies an actual supported Pareto probability law,
independently of SP-01's candidate density identity.

**Missing:** nothing for this specified exponential-law transformation.
The source's broader phrase “or part of that family” needs a precise family
and is not established by this result.

### SP-03. Tail-index/variance scalar identity — ok

`exp_growth_tail_index_variance_relation` proves
$(λ/t)t sqrt(1/λ²)=1$ for $t,λ>0$.

**Missing:** nothing for this identity.

### SP-04. Higher rate variance implies a smaller outcome tail index — not ok fully

SP-03 supplies the proposed reciprocal relation.

**Missing:** identify $1/λ²$ with the actual rate variance and prove the
monotonic tail-index relation for the
specified family. Variance alone does not characterize the transformed tail
for an arbitrary rate distribution.

### SP-05. Bernoulli scalar variance and standard-error bounds — ok

`bernoulli_variance_bound`,
`empirical_survival_variance_bound` and
`empirical_survival_std_bound` prove
$p(1-p)≤1/4$, $p(1-p)/n≤1/(4n)$ and the corresponding square-root
bound for $n>0$. The range assumptions on $p$ were unused and are now
deleted: these scalar upper bounds hold for every real $p$.

**Missing:** nothing for these scalar inequalities.

### SP-06. Actual empirical-survival variance equals p(1−p)/n — ok

[SinglePointForecasts/EmpiricalSurvival.lean](Stats/SinglePointForecasts/EmpiricalSurvival.lean)
defines the actual observed indicator average. Common marginal law and
measurability give its expectation; pairwise independence gives the exact
variance. Square integrability of the estimator and integrability of its
squared error are proved without moment assumptions on the sample values.

`empiricalSurvival_variance` and `empiricalSurvival_mse` prove the actual-law
identities. `empiricalSurvival_variance_bound` and
`empiricalSurvival_rmse_bound` give the stated bounds. The older names
with underscores remain scalar lemmas with explicitly algebraic scope.
Independent Bernoulli and Pareto product samples witness the hypotheses.

**Missing:** nothing for these fixed-threshold iid or pairwise-independent
calculations. No uniform or dependent-sample rate is asserted.

### SP-07. Printed o(1/n) error rate — false for MSE and RMSE; corrected bounds proved

The source prints `o(1/n)` at line 235, without defining the error metric.
The actual estimator has MSE $p(1-p)/n$ and RMSE at most $1/(2\sqrt n)$.
For the actual scale-one/index-one Pareto law, independent samples at
threshold two have $p=1/2$, hence MSE exactly $1/(4n)$.
`unitParetoLaw_regularlyVarying` checks the source's heavy-tail hypothesis;
`unitParetoMSE_not_littleO` and `unitParetoRMSE_not_littleO` refute the
printed rate under both specified error interpretations.

**Correction:** use the proved MSE and RMSE formulas/bounds with explicit
common-law and independence assumptions. They are fixed-threshold results.
Concentration, CLT and uniform empirical-process guarantees remain separate.

### SP-08. Strong-Pareto first moment is nonintegrable for 0 < α ≤ 1 — ok

`paretoMean_not_integrable_when_alpha_le_one` and
`paretoMean_not_integrable_at_alpha_one` prove nonintegrability of the
actual first-moment density integrand for $l>0$.

**Missing:** nothing for this strong-Pareto statement. The conclusion is
nonintegrability, rather than an equality claiming Lean's real integral is an
infinite real number.

### SP-09. The general regularly varying moment “if and only if” — not ok literally

The source footnote states finiteness exactly when $α>p$ for general slowly
varying $L$.

**Missing:** correct the boundary case $α=p$. Away from that boundary the
usual threshold holds under the standard positive-tail hypotheses, but at the
boundary the slowly varying factor determines integrability.
For example, survival proportional to $1/(x(log(x))²)$ for large $x$
is regularly varying with index $-1$ and has a finite first moment.
The strong-Pareto theorem SP-08 does not justify the general boundary claim.
This is an analytic counterexample, not a new project theorem.

### SP-10. Remark 1: unstable sample moments coexist with stable informative tail properties — not ok

The project provides tail formulas and deterministic calculations.

**Missing:** a specified tail estimator, consistency or finite-sample bounds,
and a precise instability criterion for the sample moments. Stable properties
of a distribution and stable estimation of those properties are different
claims.

### SP-11. Remark 2: asymmetric evidence requirements for systemic survival risk — not ok as a formal model

This is a risk-management principle rather than an explicit mathematical
theorem.

**Missing:** a loss/utility model, policy alternatives, uncertainty assumptions
and a proved decision rule. The absent model prevents a Lean derivation; it
does not establish that the principle is false.

### SP-12. Remark 3: no forecastability/LLN at α ≤ 1 and very slow LLN at 1 < α ≤ 2 — not ok fully

The strong-Pareto nonintegrability kernel is proved in SP-08.

**Missing:** an iid sample and the applicable LLN/nonconvergence theorem, a
quantitative sample-size/error rate for finite-mean cases, and a definition of
forecastability. Absence of a finite mean does not rule out quantile, tail or
other forecasts. The general $α=1$ statement additionally needs the
boundary correction in SP-09.

### SP-13. Remark 4: uncertainty in growth rates thickens tails and increases expected fatalities — not ok fully

The algebraic growth and index formulas are available.

**Missing:** the transformed law, a specified uncertainty comparison, and a
convexity/Jensen expectation theorem with integrability or extended
expectations. Variance ordering by itself does not guarantee every asserted
tail ordering between arbitrary rate laws.

### SP-14. Remark 5: multiplicative collective risks do not scale from individual risks — not ok

No contagion network or collective-risk random variable is defined.

**Missing:** the interaction model and a precise comparison between individual
and aggregate risks. The scalar exponential/Pareto identity does not establish
the systemic assertion.

### SP-15. Remark 6: ruin and failure of ordinary cost-benefit analysis — not ok

No absorbing loss process or admissible policy model is constructed.

**Missing:** a ruin event, its probability or time horizon, the proposed
criterion and the theorem showing the failure of the alternative criterion.
An infinite mean alone does not supply all those decision conclusions.

### SP-16. Remark 7: economic and disease risks must be modeled jointly — not ok

The source rejects treating the two as independent.

**Missing:** a joint law or causal/feedback model and a demonstrated
consequence for the relevant policy comparison.

### SP-17. Remark 8: domain-dependent insurance and mitigation comparisons — not ok

The source compares pandemic mitigation with other safety expenditures.

**Missing:** comparable loss distributions, costs, uncertainty assumptions and
an explicit decision criterion. These economic comparisons are not represented
in the Lean statements.

### SP-18. Remark 9: economic fragility and interlocking collapses — not ok

No industry network or nonlinear cascade mechanism is formalized.

**Missing:** the proposed dependency structure, perturbation model and a
cascade/fragility theorem. The accompanying historical causal attribution also
requires external evidence, rather than a pure Lean proof.

### SP-19. Numerical figures and pandemic tail estimates — not ok as certified results

The source includes illustrative lognormal/Pareto plots and cites empirical
tail estimates.

**Missing:** the datasets and statistical estimation procedures, certified
calculations or explicit error bars for the plotted claims. A generic Pareto
theorem does not validate a fitted pandemic parameter.

### SP-20. Feedback makes forecasts affect their own accuracy — not ok

The source discusses reactions to forecasts and self-canceling predictions.

**Missing:** a dynamic or game-theoretic model distinguishing a counterfactual
forecast from an observed outcome after intervention, and a theorem connecting
the response to forecast evaluation.

### SP-21. Main Statements (i)–(ix) — not ok as formalized claims

These statements mix empirical, methodological and normative content.
They are included for coverage without treating every sentence as a pure
mathematical theorem.

**Missing:** the models, evidence and precise decision or inference statements
listed for each item below.

| Main Statement | Status | Missing |
| --- | --- | --- |
| (i) Broad objection to single-point forecasts under fat tails | **not ok** | Forecast target, loss, admissible method class and a precise impossibility or suboptimality theorem |
| (ii) Pandemic tail risk and model adequacy | **not ok** | Empirical tail model, its estimation uncertainty and a defined adequacy criterion |
| (iii) Scientific understanding versus individual predictions | **not ok** | A formal methodological criterion; this is not a distributional theorem |
| (iv) Tail-focused risk management | **not ok** | A decision model proving the optimality or robustness of the proposed criterion |
| (v) Limitations of raw evidentiary methods | **not ok** | A named inference procedure and a failure/coverage theorem under explicit tail assumptions |
| (vi) Feedback between forecasts and reactions | **not ok** | The dynamic response model and forecast-evaluation theorem in SP-20 |
| (vii) Individual versus systemic risk | **not ok** | The interaction/aggregate model in SP-14 |
| (viii) Joint mitigation/disease costs and limitations of naive cost-benefit analysis | **not ok** | Joint loss model, policies and the ruin or nonintegrability consequences in SP-15–SP-17 |
| (ix) Historical economic fragility and containment | **not ok** | Historical evidence and a stated causal model; it is not established by the scalar mathematics |

## Registry of every named theorem, proposition and result

This registry is based on the active LaTeX environments in the reviewed source
versions. It provides a direct answer for every item explicitly called a
Theorem, Proposition or Result. “Corrected core” and “literal printed claim”
are distinguished where necessary.

| Paper | Source item and source line | Status | Review entries and missing work |
| --- | --- | --- | --- |
| Tail Option Pricing | Result 1, line 179: relative pricing under a price-level Pareto tail | **ok** | OP-05; exact strong-Pareto relative price with admissible strikes |
| Tail Option Pricing | Theorem 1, line 196: log returns | **ok** | OP-08; full measurable, eventually positive slowly varying tail, positive tail index and starting level |
| Tail Option Pricing | Result 2, line 230: relative pricing under a return tail | **ok** | OP-11; exact affine-return Pareto parameterization |
| Tail Option Pricing | Result 3, line 272: put pricing | **not ok** literally | OP-12–OP-14; correct signed powers/dimensional terms, then use the proved integral/cross-multiplied core and state nonzero denominators for quotient pricing |
| How Much Data Do You Need? | Proposition 1, line 562: κ of an iid cubic Student sum | **not ok** | K-19–K-22; identify the supplied closed expression with the actual MAD of the iid sum |
| Binary Forecasts | Theorem 1, line 353: convergence of I₁/I₂ | **not ok** | BF-10–BF-14; payoff restrictions and general distributional limit; strong-Pareto linear-payoff specialization is proved |
| Binary Forecasts | Theorem 2, line 629: all finite-sample Brier-score moments | **ok** | BF-26; measurable score construction, average bound and actual moment integrability proved without independence |
| Hidden Moments | Proposition 1, line 189: hidden-moment density | **not ok** | HM-04–HM-06; iid maximum law, asymptotic qualification and hidden-moment pushforward density |
| Epistemic Uncertainty | No active named Theorem/Proposition/Result | — | EU-01–EU-34 cover both numbered Remarks and the mathematical claims |
| Single Point Forecasts | No active named Theorem/Proposition/Result | — | SP-01–SP-21 cover all nine numbered Remarks and Main Statements |

The registry contains eight named mathematical results: three Theorems, two
Propositions and three Results. Lean declaration counts should never be used
as a substitute for this source-to-statement mapping.

## What needs to be repaired first

1. **Repair definitions that produce certified wrong objects.**
   The Pareto Table I expression now uses a convergent interior Beta
   difference, with exact certificates excluding the zero/constant-two
   degeneration. Its genuine MAD identification remains open. The minimum
   sample-size definition also excludes zero; its distributional sufficiency
   interpretation needs the actual MAD functions and approximation proof.
2. **Add probability-law and MAD bridges.**
   Prioritize the exponential MAD integral, Student and stable sum laws,
   Gaussian mixtures and actual iid maxima. The measurable Brier average
   and its moment integrability are now proved.
   These are the most common missing links between proved algebra and paper
   theorems.
3. **Replace proxy asymptotics with results for the paper's quantities.**
   Keep the genuine lognormal Loulakis limit separate from the small-$σ$
   cumulant and large-$σ$ surrogate formulas. Derive limits for the same
   distributional object whose finite-$n$ behavior is being discussed.
4. **Correct literal source formulas before formalizing them.**
   The put ratio, general payoff-ratio theorem, Gaussian gap, noncentered
   fourth moment, finite-sample exponential law and Gaussian hidden-mass
   evaluation need the corrections described above. Impossible statements
   should be replaced by explicit corrected propositions, with their scope
   recorded.
5. **Finish distributional limits.**
   The corrected return-tail smile bound is now assembled (OP-19).
   Prove actual estimator convergence and the intended CLT, infinite-product
   or mixture-tail theorems under explicit hypotheses.
6. **Update completeness claims as these steps are completed.**
   Historical roadmap files and module summaries document implementation
   progress; this review should be the current statement-level completeness
   reference.

## What was fixed in this pass, and what remains

The Lean/mathlib version mismatch, compatibility failures and default-build
exclusions have been fixed. All project modules now participate in the default
build, and the previously excluded mathematical results are reachable through
`import Stats`.

Obsolete or overstated comments have also been corrected: the cubic-Student
Laplace result is a proved theorem, the lognormal proxy is distinguished from
the genuine MAD limits, the Pareto second-moment coefficient is corrected,
and the mixture, iid-maximum, growth-transform and Jensen comments now state
the scope of their actual Lean conclusions.

The notebook [pareto_log_estimation.ipynb](notebooks/pareto_log_estimation.ipynb)
has been translated to English, including its old Markdown explanations,
chart labels and printed messages. All eleven code cells passed Python syntax
checks and executed with a headless plotting backend. New project
documentation and comments are also in English.

The minimum-size definition is now repaired, with positivity, attainment and
empty-set characterization theorems plus regression certificates. The old
zero-collapse certificate is retained against a clearly named historical
definition. The Pareto zero-collapse diagnostic now also targets an isolated
historical model; the current finite-Beta expression is convergent and
nondegenerate, with its probability-law/MAD bridge still open.
The deeper probability bridges, false literal paper assertions and missing
asymptotic theorems remain explicitly marked **not ok**. Completing them is
substantive mathematical work, rather than a compiler-version adjustment.

This review establishes both that the existing written proofs pass the
upgraded kernel and that passing those proofs is insufficient to call any of
the six complete papers fully formalized.
