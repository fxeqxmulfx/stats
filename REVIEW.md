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
| [How Much Data Do You Need?, 1802.05495v3](https://arxiv.org/abs/1802.05495v3) | **not ok** | Abstract κ algebra, corrected minimum-size and finite-Beta expressions, special-function identities, genuine probabilistic Loulakis lognormal limit, actual switching-Gaussian kurtosis | Distributional MAD/sample-size bridges; finite-sum law identifications; proxy limits |
| [On the Statistical Differences between Binary Forecasts and Real World Payoffs, 1907.11162v3](https://arxiv.org/abs/1907.11162v3) | **not ok** | Both Theorem 1 operational class implications, actual general RV and Gaussian limits, Pareto and exponential cases, corrected payoff converse, probabilistic Brier bounds, Bernoulli CGF derivatives and PIT | Independent tail-class identifications, nonlinear/distributional claims, CLT and Brier-score distribution |
| [Branching epistemic uncertainty and thickness of tails, 1912.00277v2](https://arxiv.org/abs/1912.00277v2) | **not ok** | Actual Gaussian hierarchies, moments and bounds, weak limit, log remainders, corrected iid lognormal CLT, actual Normal–Lognormal compound density and kurtosis | Infinite-law and higher-moment questions, numerical claims, Gamma approximation |
| [What You See and What You Don't See: The Hidden Moments of a Probability Distribution, 2004.05894v1](https://arxiv.org/abs/2004.05894v1) | **not ok** | Actual finite iid Pareto maximum and Beta hidden-mass law; general-p hidden-moment pushforward, exact Gamma-ratio mean and asymptotic; distribution-free hidden-mass law for continuous CDFs; sample-mean refutation | Explicit general-p density and Gaussian comparison |
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
passed all 3892 jobs without warnings or errors. `./run.py audit` again
covered 1279 declarations (1096 theorem declarations), with zero non-core
axioms. `./run.py forbidden` passed, and `./run.py test` passed all 27 tests
without skips. Comparing Python syntax trees after removing docstrings
confirms that executable numerical code is unchanged.
`./run.py index` regenerated 105 modules and 593 named theorems with zero
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

**Verification:** the default `lake build` and standalone `./run.py audit`
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

### Repair 5: genuine assumptions, supported exponential tails and helper scope

Reread the κ definition and decomposition in
`papers/arXiv-1802.05495v3/kappa-n-final.tex` (lines 272–300), the
Loulakis argument (lines 689–699), and the Pearson ODE, mean convention,
Eq. 13 and candidate coefficients (lines 710–749). Also reread the
truncated Pareto moment in `papers/arXiv-2004.05894v1/MaxHiddenTail.tex`
(lines 203–213), and Definitions 4–5 and Theorem 2 in
`papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`
(lines 317–355 and 626–635).

The source's probability domains remain necessary for their probabilistic
interpretations. Several Lean helpers, however, are stronger identities
of total integrals or real expressions. Their unused hypotheses had been
hidden under names beginning with `_h`. Those hypotheses are now deleted,
with callers and the verification annotations updated. This includes the
κ telescoping identity, the sample-size formula and inverse, constant
gamma-PnL factoring, the Carr–Madan alias, a truncated-moment integral,
VaR/CVaR expression monotonicity, the MLE candidate-variance scaling and
the pointwise Kelly derivative. The abstract iid maximum and Loulakis
bounds also lose unused inputs; their actual probability statements and
the canonical lognormal specialization remain intact.

`pearsonIVMADClosed` loses its ignored `a₀` argument. The two conditional
MAD algebra lemmas lose that parameter and the unused mean constraint;
they still require the IBP equation as input. The normalized coefficient
`pearsonIV_a1_lognormal` is now a real constant, with no ignored sample-size
or volatility arguments. No actual Pearson density, mean, cumulant match
or MAD identity is manufactured by these changes. K-38 and K-39 remain
incomplete. The lognormal proxy's limit also holds at zero volatility;
its unused nonzero-volatility assumption is removed without identifying
the proxy with a sum's MAD.

[Probability/Exponential.lean](Stats/Probability/Exponential.lean) shares
the already proved full survival of Mathlib's exponential law:
`P(X>K)=exp(-λK)` for `K≥0`, and `P(X>K)=1` for `K<0`.
[BinaryForecasts/ExponentialLaw.lean](Stats/BinaryForecasts/ExponentialLaw.lean)
now connects the raw-kernel integral to that actual law on its correct
domain. The analytic integral itself holds for every real threshold;
the former unused `K≥0` premise is removed from `exp_survival_eq`.
A negative-threshold certificate proves the distinction: at rate one and
threshold minus one, the actual survival is one, while the raw-kernel
integral is `exp(1)>1`. The moved full-survival declaration retains its
name, type and public re-export.

[Review/Assumptions.lean](Stats/Review/Assumptions.lean) supplies concrete
examples, including zero parameters and negative values that demonstrate
the stronger algebraic domains, and a smooth affine Carr–Madan payoff.
[Review/ProbabilityAssumptions.lean](Stats/Review/ProbabilityAssumptions.lean)
uses an actual nondegenerate independent Gaussian product sample and its
lognormal transforms to verify the revised iid maximum and Loulakis APIs.
The new modules are at most 106 lines.

The Kelly and MLE comments now describe their proved scope: pointwise
derivatives, candidate scalar formulas and elementary identities. They
do not claim a justified derivative of an expectation, an optimal stake,
an estimator CLT, coverage or a finite-sample variance bound. The
binary-forecast overview likewise records Theorem 2's actual bounded-score
moment proof, while retaining the open general Theorem 1 and distributional
gaps. Rereading the sentence immediately before Theorem 1 also corrects
this review's earlier attribution: the source explicitly assumes `g(x)=x`
for that section. The nonlinear exponential-payoff example below obstructs
an extension of Theorem 1, rather than refuting its stated linear scope.

**Verification:** the default build passes all 3915 jobs without warnings.
The transitive audit checks 1449 declarations, including 1246 theorem
declarations, and reports only `Quot.sound`, `Classical.choice` and
`propext`; the standalone audit also passes. All 27 Python tests and the
forbidden-construct and whitespace checks pass. The generated index has
135 modules, 670 named theorems and zero sorry, vacuous or placeholder
markers. Its exhaustive audit imports all 134 other modules. The refreshed
`dt` index has 761 project declarations. All 760 prior public names remain:
737 types are unchanged and 23 have the documented stronger hypotheses or
simplified parameter lists. The supported exponential-survival bridge
adds one public theorem.

### Repair 6: consistent module summaries and historical status

The consistency pass found remaining descriptions that contradicted the
claim registry. `Stats.Kappa` still called the Cauchy reference curve a
finite-MAD result, called two completed analytic lemmas axioms and described
the completed lognormal Loulakis proof as conditional. Its overview now
separates supplied special-law formulas, genuine probability infrastructure,
the actual large-volatility result and the outstanding MAD bridges.

Reread `kappa-n-final.tex`, Definition 1 and Eq. 4 (lines 272–325),
the Loulakis argument (lines 689–699), and Pearson Eq. 13 (lines 710–749).
The stable-function descriptions now state the actual conclusions: a
formula predicate, a conditional power identity, and an assumed MAD power
curve. The former unproved alternative location-shift formula in the
index-one docstring is removed. Its theorem only multiplies an exponential
argument; no rescaled-law identity is inferred from that theorem.

Reread `FatTailsEpistemic2019.tex`, Section III's binomial mixture and
moment displays (lines 318–346), and Section IV's finite product
(lines 416–437). The inner epistemic-uncertainty docstrings now agree with
the module header: the proved quantities are weighted scale sums and
candidate kurtosis/variance expressions. A scalar lower bound neither
identifies outcome moments nor proves a tail comparison or an equality
criterion absent from the theorem.

Reread `MaxHiddenTail.tex`, the maximum/decomposition and Proposition 1
(lines 159–219), and Remark 1. The hidden-moment CDF/PDF polynomials are
explicitly restricted to their candidate role; their derivative and mean
integral are not described as a proved pushforward-law identification.
The risk-module summaries likewise distinguish actual integrability
thresholds from scalar portfolio, maximum-tail, drawdown, Kelly and MLE
expressions. In particular, a polynomial union bound does not itself prove
a path-drawdown scaling law, a maximum-law theorem or FDR control. Negative
homogeneity of a supplied portfolio formula is not negative homogeneity
of an actual CVaR functional. These risk-module extensions do not gain a
paper-law theorem by changing their descriptions.

The main overview now includes Repair 4's actual exponential-growth law
and empirical-survival estimates, with the paper's corrected error rate.
Historical TODO files point to this review for current scope; their old
checkmarks and former-axiom notes are not presented as current completeness
certificates. The summary table in `todo.md` no longer calls any paper
complete. The copied project instructions now use this repository's
`Stats/` modules, existing public namespaces and `master` branch.

All eleven touched Lean files have identical code after comments and
whitespace are removed. No definition, proof body, declaration type or
import changes in this pass, and no missing distributional bridge is
claimed to have been proved by these documentation corrections.

**Verification:** all 3915 default-build jobs pass without warnings. The
standalone transitive audit again checks 1449 declarations, including
1246 theorem declarations, with zero non-core axioms. The 27 Python tests,
forbidden-construct check and whitespace check pass. All 761 elaborated
public names and types are unchanged after `dt refresh project`. Index
regeneration reports 135 modules, 670 named theorems and zero sorry,
vacuous or placeholder markers.

## Gap-closing goal (2026-10-19)

The user requested **solve all gaps**. The full six-paper claim registry
remains the objective; the following completed group does not close the
remaining distributional, approximation, limit and modeling entries.

### Actual iid Pareto maximum and hidden probability mass

Reread `papers/arXiv-2004.05894v1/MaxHiddenTail.tex`, the maximum
construction and moment decomposition (lines 159–175), Proposition 1 and
its Fréchet substitution (lines 185–219), and Remark 1 (lines 230–237).
The exact finite-sample calculation is now proved for actual observations.

[Probability/SampleMaximum.lean](Stats/Probability/SampleMaximum.lean)
constructs a genuine finite product sample law and the maximum of its
observed coordinates. Independence, the common marginal and maximum
measurability are proved. For any real probability law, including atoms,
the strict and non-strict lower-tail probabilities are the corresponding
marginal probabilities raised to the sample size.
[HiddenMoments/Maximum.lean](Stats/HiddenMoments/Maximum.lean) specializes
this to the supported Pareto measure. Its full CDF is zero below the scale
and `(1-(l/k)^α)^n` above it, for positive scale/index and nonempty samples.
The maximum lies strictly above the support boundary almost surely.

[Probability/HiddenMass.lean](Stats/Probability/HiddenMass.lean) defines
the quantity of interest as the **actual population probability beyond
the observed maximum**, `ν.real (Ioi (sampleMaximum x))`. It is measurable,
bounded between zero and one, and integrable under the actual product law
without moment assumptions on the sampled values.
[HiddenMoments/SurvivalMass.lean](Stats/HiddenMoments/SurvivalMass.lean)
identifies it almost surely with `(l/K_n)^α` and proves its complete CDF:

```text
P(H_n ≤ y) = 0                  if y ≤ 0,
             1-(1-y)^n          if 0 < y < 1,
             1                  if y ≥ 1.
```

This is the supported Beta(1,n) CDF of the actual hidden mass and actual
sample-survival ratio. It is not assigned as either variable's definition.
[Mean.lean](Stats/HiddenMoments/Mean.lean) uses their proved integrability,
actual tail probabilities and layer cake to prove `E[H_n]=1/(n+1)`.
[Counterexample.lean](Stats/HiddenMoments/Counterexample.lean) proves that
the actual pushforward law differs from the printed Exp(n) law: the former
has no mass above one, while the latter has positive mass there.
This corrects the source's exact exponential/`1/n` assertions; no
Fréchet or exponential limit has been inferred without a limit proof.

Concrete nondegenerate witnesses use two independent Pareto(1,2)
observations: `P(K₂≤2)=9/16`, `P(H₂≤1/4)=7/16`, and `E[H₂]=1/3`.
They cover the support branches, remaining hypotheses and integrability.
The former large HiddenMoments module is split into focused files while
retaining its public names; the Pareto measure imports only the tail-moment
foundation to keep the new maximum-law imports acyclic.

**Verification:** all 3925 default-build jobs pass without warnings. The
standalone exhaustive audit checks 1518 declarations, including 1305
theorem declarations, with only `Quot.sound`, `Classical.choice` and
`propext`. The regenerated index contains 145 modules and 702 named
theorems, with zero sorry, vacuous or placeholder markers; the audit
explicitly imports all 144 other modules. All 27 Python tests, the
forbidden-construct check and `git diff --check` pass. `dt refresh project`
indexes 802 public declarations: all 761 previous names and types remain
unchanged, and 41 declarations are added. The focused example build checks
the four central theorem axioms and nondegenerate probability witnesses.
Every new Lean module has at most 193 lines.

### Actual population moments and decomposition at the observed maximum

Reread `MaxHiddenTail.tex`, the opening population-moment decomposition
(lines 159–175) and Eq. 2 (lines 203–213), and
`papers/arXiv-2007.16096v1/coronaIJF_paperArXiv.tex`, the moment footnote
(line 181) and Remark 3's finite-mean discussion (lines 214–217).

[Pareto/Integration.lean](Stats/Pareto/Integration.lean) now connects
integration against the genuine supported Pareto measure to the existing
density integrals. It proves both the integral identity and the exact
integrability equivalence, including restricted sets.
[Pareto/Moments.lean](Stats/Pareto/Moments.lean) then proves

```text
Integrable (x ↦ x^p) (paretoMeasure l α) ↔ p < α
E[X^p] = α l^p / (α-p)                 when p < α
E[X^p ; X>k] = α l^α k^(p-α)/(α-p)     when p < α and k ≥ l.
```

These are statements about the actual measure, with positive scale and
tail index. The first is the exact strong-Pareto moment threshold; it
does not extend the source's incorrect boundary assertion to arbitrary
slowly varying tails. Concrete examples prove finite mean two and a
nonintegrable second moment for Pareto(1,2).

[Probability/TruncatedMoments.lean](Stats/Probability/TruncatedMoments.lean)
defines the visible and hidden quantities as actual population integrals
below and above the observed coordinate maximum. Joint measurability of
the threshold kernels proves that both are measurable sample functions.
Integrability of the population power suffices for both quantities to be
integrable under the actual product sample law, using a bound by the
population absolute moment. Their pointwise and expected sums equal the
population moment; neither is an empirical arithmetic mean.

[HiddenMoments/Decomposition.lean](Stats/HiddenMoments/Decomposition.lean)
assembles the source's split at the actual maximum. It identifies the
visible density integral and the hidden tail integral, applies Eq. 2 at
the random threshold almost surely, and proves both sample quantities
integrable. The visible population integral is strictly below the finite
population moment almost surely. This is the valid population-truncation
target; the source's stronger statement about an arithmetic sample mean
is refuted separately in the following group and HM-19.

Nondegenerate Pareto(1,2) product examples check the true mean two,
the conditional density-integral bridges, measurability and L1 of both
sample quantities, their expected sum two, and the actual hidden first
moment `2/K_n` almost surely. No expectation, law or integrability
conclusion is supplied as a hypothesis without an actual witness.

**Verification:** all 3930 default-build jobs pass without warnings. The
standalone transitive audit checks 1563 declarations, including 1341
theorem declarations, with only the three permitted core axioms. The
generated index has 150 modules and 729 named theorems, with zero sorry,
vacuous or placeholder markers; all 149 other modules are explicitly
imported by the audit. All 27 Python tests and the forbidden/whitespace
checks pass. The refreshed project index has 830 distinct public names:
all 802 previous names and types remain unchanged, with 28 additions.
The new example instance is named explicitly so the declaration index
retains both example modules' instances without a name collision.
The five new modules are at most 103 lines each.

### Actual arithmetic sample mean: unbiasedness and an overshoot counterexample

Reread `MaxHiddenTail.tex`, **Applications and Conclusion** (lines 275–278).
The source says that a right-tailed one-sided distribution's **sample mean**
will necessarily underestimate the true mean. This statement concerns a
different quantity from the unrescaled population integral below its
observed maximum.

[Probability/SampleMean.lean](Stats/Probability/SampleMean.lean) defines
the arithmetic mean of the actual observed coordinates. It proves
measurability, integrability and unbiasedness whenever the population
first moment is integrable and the sample is nonempty. No second-moment
assumption is used, and the mean is not supplied as a desired scalar value.
[HiddenMoments/SampleMean.lean](Stats/HiddenMoments/SampleMean.lean)
specializes this to the genuine Pareto product law and its proved actual
population mean `m=α*l/(α-1)`, for `l>0` and `α>1`.

The same module proves, for **every positive finite sample size**,

```text
E[arithmetic sample mean] = m
P(arithmetic sample mean > m) ≥ (l/(n*m))^α > 0.
```

The lower bound comes from one observation exceeding `n*m`, while the
other observations are nonnegative almost surely. Both support and the
event probability follow from the actual marginal law. The theorem
`paretoSampleMean_not_always_below_mean` formally refutes the source's
literal necessary-underestimation claim, with a finite actual mean.
The corrected truncated-population-integral inequality from the preceding
group remains valid.

For Pareto(1,2), the actual two-observation mean has expectation two and
overshoot probability at least `1/16`. The one-observation example has
overshoot probability exactly `1/4`.
[SampleMeanExamples.lean](Stats/HiddenMoments/SampleMeanExamples.lean)
checks these numerical probabilities, all remaining parameter and
integrability conditions, and the three central theorem axioms.

**Verification:** all 3933 default-build jobs pass without warnings. The
standalone audit checks 1591 declarations, including 1362 theorem
declarations, with only the three permitted core axioms. The generated
index has 153 modules and 739 named theorems, with zero sorry, vacuous or
placeholder markers. All 27 Python tests and the forbidden/whitespace
checks pass. The refreshed declaration index has 842 distinct public
names: all 830 previous names and types remain unchanged, with 12
additions and no duplicate names. The three new modules have 57, 113 and
72 lines respectively.

### Exact hidden-moment law, Gamma expectation and asymptotic

Reread `papers/arXiv-2004.05894v1/MaxHiddenTail.tex`, section **The Invisible
Tail for a Power Law**, Proposition 1, its following mean display, Eq. 2
and Remark 1 (lines 159–239). The printed general-p density and mean use a
Fréchet replacement for the finite-sample maximum. For an exact Pareto
sample, the actual hidden mass has support `[0,1]` and the Beta(1,n) law.

[Probability/BetaMoments.lean](Stats/Probability/BetaMoments.lean) proves
normalization, power integrability and power expectations of the actual
Mathlib Beta measure. The proof multiplies its supported density by a
power and identifies the result with a multiple of another normalized
Beta density. No desired moment value is used as a definition.
[BetaKernel.lean](Stats/HiddenMoments/BetaKernel.lean) proves the supported
Beta(1,n) PDF and its full CDF, including both support branches.
[BetaLaw.lean](Stats/HiddenMoments/BetaLaw.lean) then proves equality of the
actual hidden-mass pushforward with this measure, using the already
proved CDF of the genuine product sample. It also proves integrability
and actual expectations of hidden-mass powers above -1.

For `l>0`, `α>0`, `p<α` and positive finite sample size, write
`r=(α-p)/α=1-p/α>0` and `c=α*l^p/(α-p)`. The actual population tail integral
at the actual maximum satisfies, almost surely,

```text
M_hidden,p = c * H^r,       H has the actual Beta(1,n) law,
E[M_hidden,p] = l^p * Gamma(r) * Gamma(n+1) / Gamma(n+1+r).
```

[MomentMean.lean](Stats/HiddenMoments/MomentMean.lean) proves both the
pushforward equality for the genuine hidden p-th moment and the exact
expectation. Its random variable and L1 property were established from
population integrals in the preceding group. The Gamma-ratio result is a
new finite-sample correction, not a literal formalization of the source's
Fréchet expectation.

[Probability/BetaAsymptotic.lean](Stats/Probability/BetaAsymptotic.lean)
connects Euler's real Gamma approximants to scaled Beta values.
[MomentAsymptotic.lean](Stats/HiddenMoments/MomentAsymptotic.lean) applies
Euler's limit to the actual expectation and proves

```text
n^r * E[M_hidden,p] -> l^p * Gamma(r),
E[M_hidden,p] / (l^p * n^(-r) * Gamma(r)) -> 1.
```

The Lean sequences use sample size `n+1`, covering every positive size
without an artificial empty maximum. Since `-r=p/α-1`, the denominator
is precisely the paper's expression, now justified as an asymptotic for
the exact strong-Pareto law. This result does not assert an approximation
for an arbitrary regularly varying population.

[MomentMeanExamples.lean](Stats/HiddenMoments/MomentMeanExamples.lean)
provides genuine Pareto(1,2) product samples and Beta(1,2) witnesses for
every hypothesis family. The expected hidden first moment is `4/3` for
one observation and `16/15` for two; the expected hidden moment of order
-2 is `1/12` for two observations. The examples also check the normalized
PDF, actual pushforwards, a negative hidden-mass power's integrability,
both asymptotic statements and the central transitive axioms.

**Verification:** all 3950 default-build jobs pass without warnings. The
standalone audit checks 1641 declarations, including 1406 theorem
declarations, with only the three permitted core axioms. The generated
index has 160 modules and 759 named theorems, with zero sorry, vacuous or
placeholder markers; the audit explicitly imports all 159 other modules.
All 27 Python tests and the forbidden/whitespace checks pass. The refreshed
declaration index has 863 distinct public names, with all 842 previous
names and types unchanged, 21 additions and no duplicates. The seven new
modules are at most 143 lines each.

### Probability integral transform and distribution-free hidden mass

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Appendix B, **Distribution of the probability** (lines 815–828), and
`papers/arXiv-2004.05894v1/MaxHiddenTail.tex`, Remark 1 (lines 229–239).
The first source states that `F_X(X)` is uniform when the actual law has
a continuous CDF. The second emphasizes independence of hidden probability
mass from the Pareto scale and tail index. The continuous-law hidden-mass
result below is an explicitly broader mathematical extension of that remark.

[Probability/CDFTransform.lean](Stats/Probability/CDFTransform.lean)
proves the actual CDF sublevel probabilities, including threshold zero.
It constructs the upper endpoint of each nonempty sublevel below one
using closedness, boundedness, monotonicity and the intermediate value
theorem. The proof allows flat CDF regions, so it does not impose an
everywhere strictly increasing inverse absent from the source assumptions.

[Probability/IntegralTransform.lean](Stats/Probability/IntegralTransform.lean)
proves the equality of the actual transformed measure with Beta(1,1),
and identifies that measure with Lebesgue measure restricted to `(0,1)`.
`probabilityIntegralTransform` applies to a measurable observation on any
probability space, using the CDF of its actual pushforward law. Thus the
uniform law is established as a measure equality, not introduced as a
hypothesis or a forecast-probability definition. The source's informal
inverse notation is implemented by the proved sublevel endpoint argument.

[ContinuousLaw.lean](Stats/HiddenMoments/ContinuousLaw.lean) proves for
every positive finite iid sample from a probability law with continuous
CDF:

```text
P(F(sample maximum) <= q) = q^n             for 0 <= q < 1,
P(actual hidden mass >= y) = (1-y)^n        for 0 < y <= 1,
law(actual hidden mass) = Beta(1,n),
E[actual hidden mass] = 1/(n+1).
```

The true product sample supplies independence. The hidden mass is the
actual population probability beyond its observed maximum, with its
boundedness, measurability and L1 property already proved. The equality
of laws includes the support branches and the endpoint at hidden mass
one. Atomic populations are outside the stated continuity hypothesis.
The unscaled exact exponential law printed in the second source remains
false; distribution independence does not repair that law.

[ContinuousLawExamples.lean](Stats/HiddenMoments/ContinuousLawExamples.lean)
proves continuity of the actual exponential CDF, including its flat
negative half-line and support boundary. This provides a genuine
non-Pareto witness: for Exp(1) and two observations, the actual hidden
mass has Beta(1,2) law, tail probability `9/16` at `1/4`, and expectation
`1/3`. The examples also instantiate the CDF sublevel endpoint, its zero
threshold, both uniform-measure formulations and a nonconstant coordinate
observation on an actual product probability space.

**Verification:** all 3954 default-build jobs pass without warnings. The
standalone audit checks 1665 declarations, including 1424 theorem
declarations, with only the three permitted core axioms. The generated
index has 164 modules and 770 named theorems, with zero sorry, vacuous or
placeholder markers; all 163 other modules are imported by the audit.
All 27 Python tests and the forbidden/whitespace checks pass. The refreshed
declaration index has 875 distinct public names: all 863 previous names
and types remain unchanged, with 12 additions and no duplicates. The
four new modules are at most 104 lines each.

### Actual scaled hidden-mass laws converge weakly to Exp(1)

Reread `papers/arXiv-2004.05894v1/MaxHiddenTail.tex`, Remark 1 (lines
229–235), together with the Fréchet substitution in the proof of
Proposition 1 (lines 209–219). The source prints an exact exponential
law with rate `n` for unscaled finite-sample hidden mass. That statement
remains false. The corrected asymptotic is `n*H_n` converging in law to
Exp(1), where `H_n` is the actual population tail probability beyond the
actual iid sample maximum.

[Probability/WeakCDF.lean](Stats/Probability/WeakCDF.lean) proves a
sufficient criterion turning pointwise convergence of actual real CDFs
into weak convergence of probability measures. Its proof converts CDF
differences into probabilities of bounded half-open intervals, then
applies the π-system neighborhood criterion for the weak topology.
Thus the resulting limit is a genuine weak-convergence theorem.

[ScaledLaw.lean](Stats/HiddenMoments/ScaledLaw.lean) defines the actual
pushforward probability measure of `(n+1)*H_(n+1)` from `n+1` observed
coordinates. The positive-size indexing avoids an empty maximum. Its
exact CDF is obtained from the already proved actual Beta(1,n+1) law
at the threshold `t/(n+1)`, with all real thresholds allowed. The target
`unitExponentialLaw` is Mathlib's normalized actual Exp(1) measure.

[ExponentialLimit.lean](Stats/HiddenMoments/ExponentialLimit.lean) proves
pointwise convergence at every real threshold, including zero and the
negative half-line, using Euler's exponential limit in the positive
interior branch. `scaledHiddenMassLaw_tendsto` then proves convergence in
the weak topology on probability measures for every population with
continuous CDF. `continuous_paretoMeasure_cdf` verifies that condition
for every positive strong-Pareto scale and tail index, and
`paretoScaledHiddenMassLaw_tendsto` supplies the source-specific corollary.
No population moment assumption is needed.

[ExponentialLimitExamples.lean](Stats/HiddenMoments/ExponentialLimitExamples.lean)
checks that index zero uses one observation and that index one scales a
two-observation hidden mass by two. For an Exp(1) population, the latter
actual CDF is `3/4` at one, zero at zero and negative one, and one at two.
The examples instantiate actual CDF convergence, the generic
CDF-to-weak-convergence criterion, and both exponential and Pareto weak
limits. Pareto(1,1/2) provides a concrete infinite-mean population: its
mean integrability fails while its scaled hidden-mass laws still converge.

**Verification:** all 3967 default-build jobs pass without warnings. The
standalone audit checks 1686 declarations, including 1437 theorem
declarations, with only the three permitted core axioms. The generated
index has 168 modules and 776 named theorems, with zero sorry, vacuous or
placeholder markers; all 167 other modules are explicitly audited.
All 27 Python tests and the forbidden/whitespace checks pass. The refreshed
declaration index has 886 distinct names, preserving all 875 previous
names and types without duplicates. The 11 additions include the
compiler-generated congruence lemma for the bundled scaled law. The
four new modules are at most 93 lines each.

### Fixed-density payoff equality: counterexample and corrected converse

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 5, **Substitution of integral** (lines 339–350). The source
fixes a density and a positive threshold, then says `I1=I2` holds if and
only if the payoff is constant above that threshold. Its following
sentence separately considers positive first derivatives. The fixed-density
converse is false for a general impact function, even if it is smooth,
nonnegative and genuinely integrable.

[Probability/ExponentialIntegration.lean](Stats/Probability/ExponentialIntegration.lean)
proves actual supported exponential-law integration and L1 bridges, and
normalization of its real PDF. This makes the counterexample use a true
density on the whole real line. The raw expression `exp(-x)` alone is
not a normalized real-line density; the supported exponential PDF agrees
with it on the positive tail used below.

[ConflationCounterexample.lean](Stats/BinaryForecasts/ConflationCounterexample.lean)
uses the actual Exp(1) PDF, the positive threshold `K=1`, and
`g(x)=(x-2)^2`. It proves

```text
I1(g, f, 1) = I2(g, f, 1) = exp(-1) > 0,
actual Exp(1) expectation of g above one = exp(-1),
g is differentiable, nonnegative, and L1 on that actual tail,
g(2)=0 and g(4)=4, so g is not constant above one.
```

The positive value is proved by an antiderivative and integrability of
polynomials times `exp(-x)`, not supplied by definition. Both points of
payoff variation have strictly positive density. Thus neither an empty
tail, a nonintegrable real integral, a signed payoff nor variation only
outside the support explains the equality. The excess `g(x)-g(1)` changes
sign and cancels in the integral.
`conflation_fixed_density_counterexample` packages the formal refutation
with its differentiability, nonnegativity, L1 and positive-payoff conditions.
An identity quantified over **every** possible density would be a
different assertion; this counterexample concerns the fixed-density
reading in Definition 5. It does not refute the following separate
positive-derivative claim.

[PayoffGap.lean](Stats/BinaryForecasts/PayoffGap.lean) proves a corrected
characterization for actual finite population measures. If the payoff
is L1 on the measured tail and `g(x)>=g(K)` almost everywhere there, then

```text
actual payoff expectation = g(K) * actual tail probability
    iff g(x)=g(K) almost everywhere under the restricted tail law.
```

The one-sided bound rules out cancellation. The almost-everywhere
conclusion concerns the actual measured support and does not assert
pointwise values outside that support. The same module proves the exact
strict-gap criterion: the gap is positive if and only if the restricted
tail law assigns positive probability to `g(x)>g(K)`. In particular,
strict excess almost everywhere and positive tail probability imply a
strict gap. The results apply to all real thresholds, including the
source's positive-threshold domain.

[ConflationCounterexampleExamples.lean](Stats/BinaryForecasts/ConflationCounterexampleExamples.lean)
checks a normalized PDF, positive density at both counterexample points,
the actual expected payoff and its L1 property, and the zero integral of
the excess. A constant payoff of two has actual tail expectation
`2*exp(-1)`, witnessing the corrected equality. The linear payoff under
the same actual law witnesses the L1, one-sided bound, positive tail
probability and strict-gap hypotheses. Five central theorem axiom prints
and the transitive audit check all new proof dependencies.

**Verification:** all 3971 default-build jobs pass without warnings. The
standalone audit checks 1714 declarations, including 1461 theorem
declarations, with only the three permitted core axioms. The generated
index has 172 modules and 796 named theorems, with zero sorry, vacuous or
placeholder markers; all 171 other modules are explicitly audited.
All 27 Python tests and the forbidden/whitespace checks pass. The refreshed
declaration index has 902 distinct public names, preserving all 886
previous names and types with 16 additions and no duplicates. The four
new modules are at most 141 lines each. The audit's import-list header
was shortened without changing its algorithm, keeping that aggregator
at 200 lines.

### Actual exponential conditional means and characteristic-scale limits

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 4, **Characteristic scale** (lines 317–327). The source's
quantities are conditional expectations under the physical population
law. Its dimensionless limit `lambda` is separate from the exponential
rate parameter; the Lean results use rate `r>0`.

[ExponentialLaw.lean](Stats/BinaryForecasts/ExponentialLaw.lean) now bridges
the density first-tail-moment formula to the actual supported Exp(r)
measure. It proves actual tail L1, positive probability of every finite
upper tail, and normalization of the actual conditional measure
`cond (expMeasure r) (Ioi K)`. This is the population restriction scaled
by the inverse of its own actual tail probability, rather than a law
introduced by a desired conditional-mean value.

For nonnegative thresholds, the module proves L1 of the conditional
observation and computes the actual expectations:

```text
actual first tail moment = (K+1/r)*exp(-r*K),
E[X | X>K] = K+1/r,
E[X-K | X>K] = 1/r.
```

The conditional integrability proof transfers a proved density-kernel
L1 bound through the actual law and its finite normalizing factor.
Linearity under the proved L1 and probability conditions identifies the
last integral with the source's `E[X|X>K]-K`. Neither an expected value
nor its integrability is assumed from the source's scalar formula.
The support restriction `K>=0` is explicit;
positivity and normalization of the conditional tail law hold at all
finite real thresholds.

`expMeasure_cond_mean_excess_tendsto` proves the actual conditional
mean excess tends to `1/r>0` as the threshold goes to infinity.
`expMeasure_cond_characteristicScale_tendsto` proves the actual
conditional mean divided by the threshold tends to one. These verify
the source's two operational limit properties for the actual exponential
population. They do not classify arbitrary populations as rapidly or
regularly varying, and do not assert a general finite-mean theorem from
an undefined thin-tail label.

Concrete witnesses use rate two and threshold three: the actual first
tail moment is `(7/2)*exp(-6)`, the actual conditional mean is `7/2`,
and the actual mean excess is `1/2`. The conditional observation lies
above three almost surely under a proved probability measure and is
integrable. Additional examples check positive tail probability below
the support and both actual-law limits. All nine new hypothesis families
have concrete satisfying instances, and five central axiom prints check
their transitive proof dependencies.

**Verification:** all 3971 default-build jobs pass without warnings. The
standalone audit checks 1723 declarations, including 1470 theorem
declarations, with only the three permitted core axioms. The generated
index has 172 modules and 805 named theorems, with zero sorry, vacuous or
placeholder markers. All 27 Python tests and the forbidden/whitespace
checks pass. The refreshed declaration index has 911 distinct public
names: all 902 previous names and types remain unchanged, with nine
additions and no duplicates. The expanded actual-law module is 169 lines.

### Cache module membership in repeated verification scans

Both the transitive axiom audit and the compiled-proof scanner used to
recompute their project-module predicate for every imported declaration.
They now compute the same predicate once per imported module and look up
the result by the declaration's module index. Each retains its original
predicate and exhaustive `import all` coverage, including private
declarations. The scanner constructs a source path only for an actual
finding; its type/value inspection, opaque-value handling and line lookup
are unchanged. The axiom audit still calls `Lean.collectAxioms` for every
selected declaration and rejects every axiom outside the existing three.

Separate Lean benchmarks compared the entire ordered declaration arrays
selected by the old and cached predicates. Both comparisons were exactly
equal at 1723 roots. On this machine, selection alone changed from
92341 ms to 330 ms for the axiom audit and from 90300 ms to 325 ms for
the compiled-proof scanner. These are selection timings, not full-build
timings. A separate optimized audit computation took 920 ms and reported
the same 1723 declarations, 1470 theorem declarations and three core
axioms. This changes verification cost without changing a mathematical
claim or its dependencies.

**Verification:** the default build passes all 3971 jobs without warnings;
the rebuilt audit module takes 3.3 seconds. The standalone audit retains
the same counts and zero non-core axioms. The generated index remains
172 modules and 805 named theorems with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check
pass. The refreshed declaration index retains all 911 public names and
their exact types, with no additions or duplicates.

### Actual Pareto conditional means and characteristic-scale limit

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 4 (lines 317–327), the explicit `g(x)=x` restriction and
Theorem 1 (lines 351–365), and the following **Fat tails** calculation
(lines 378–384). The new statements concern the exact supported Pareto
law, not every law with a regularly varying tail. They use the same
threshold in the conditional event and both tail integrals; the printed
fat-tail display mixes `K` and `K_p`.

[CharacteristicScale.lean](Stats/BinaryForecasts/CharacteristicScale.lean)
now proves positive actual tail probability and normalization of
`cond (paretoMeasure l alpha) (Ioi K)` for every finite threshold when
`l>0` and `alpha>0`. For `alpha>1`, the actual conditional observation
is L1 at every finite threshold. Above the support boundary `K>=l`,
supported density integration and the proved Pareto tail calculation give

```text
E[X | X>K] = alpha*K/(alpha-1),
E[X-K | X>K] = K/(alpha-1),
E[X | X>K]/K = alpha/(alpha-1).
```

The mean excess uses linearity under proved L1 and probability conditions.
The actual conditional-mean ratio tends to `alpha/(alpha-1)>1` at
infinity, verifying this population's operational limit in Definition 4.
The earlier analytic ratio declarations and their types are preserved.
The module now uses focused Pareto and conditional-probability imports.

Concrete Pareto(2,3) witnesses at threshold four have conditional mean
six, mean excess two and ratio `3/2`. They check actual normalization,
conditional support, L1, both ratio formulas, the limit, and positive
tail probability below the support. The same actual population has an
integrable second power with expectation twelve. This corrects the old
module description: a conditional-mean ratio above one is not a boundary
between finite and infinite variance. Every new hypothesis family has a
concrete witness; five central axiom prints check proof dependencies.

The general class predicates, general RV application and Gaussian
conditional limit remain recorded separately in BF-04, BF-12 and BF-14.

**Verification:** all 3971 default-build jobs pass without warnings.
The standalone audit covers 1740 declarations and 1487 theorem
declarations, with only the three core axioms. The regenerated index
has 172 modules and 812 named theorems, with zero sorry, vacuous or
placeholder markers. All 27 Python tests, the forbidden check and
whitespace check pass. The refreshed declaration index has 918 distinct
public names: all 911 previous names and types remain unchanged, with
seven additions and no duplicates. The actual-law module is 173 lines.
The Gaussian users now import their standard-normal dependencies directly.

### General RV survival laws: actual L1, conditional means and I1/I2

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 4 (lines 317–327), Definition 5 and the explicit `g(x)=x`
restriction (lines 341–351), Theorem 1 and its proof (lines 353–365),
and the **Fat tails** calculation (lines 378–384). This repair establishes
the general regularly varying branch for `alpha>1`, using the same
threshold `K` in both tail integrals. The printed fat-tail display mixes
`K` and `K_p`; it is not formalized with unrelated integration thresholds.

[LayerCake.lean](Stats/LayerCake.lean) now transfers integrability of the
actual survival function on an upper tail to L1 of the actual upper-tail
observation. This uses the nonnegative Lebesgue layer-cake theorem and
translation, rather than interpreting a total real integral as a finite
expectation. Its second bridge proves, under the actual tail L1 condition,

```text
integral_{X>K} X dnu = K*nu.real(X>K) + integral_K^infinity nu.real(X>s) ds.
```

A separate algebraic identity identifies the normalized conditional mean
divided by `K` with the actual first-tail-moment ratio. It is explicitly
an identity, not an assertion of L1 by itself.

[RegularVariation.lean](Stats/BinaryForecasts/RegularVariation.lean)
applies the full measurable slowly varying Karamata theorem to an
eventual representation of the actual survival as `L(s)*s^(-alpha)`.
The positive limiting normalized survival integral makes that integral
eventually nonzero, proving its L1 condition; the layer-cake converse
then gives the actual upper-tail L1 condition. No actual mean, conditional
mean, tail moment or integrability conclusion is supplied as a hypothesis.
The actual linear-payoff ratio and normalized conditional-mean ratio
both tend to `alpha/(alpha-1)`. The conditional laws are eventually
proved probability measures with integrable observations.

[RegularVariationLaw.lean](Stats/BinaryForecasts/RegularVariationLaw.lean)
starts directly from regular variation of the actual survival function
of a finite measure, with index `-alpha`. It derives eventual positive
tail probability from the ratio limit at scale one, measurability from
antitonicity of actual survival, and the slowly varying factor
`nu.real(Ioi s)/s^(-alpha)`. Thus the representation hypotheses are
discharged for the actual law. The results cover probability measures
and allow an uncontrolled lower tail, since only the upper tail is used.

`regularlyVarying_density_I1_div_I2_tendsto` also proves the source's
written `I1 id f K / I2 id f K` limit when a nonnegative measurable
real density `f` is explicitly identified with the actual finite law
via `withDensity`. Both density integrals are identified with the actual
tail quantities. This is not a theorem about an unrelated density kernel.
The existing Pareto factor inequality proves the limiting factor exceeds
one for `alpha>1`.

All new hypothesis families have genuine Pareto(2,3) witnesses: actual
survival regular variation, eventual tail L1, conditional normalization
and L1, both actual-law limits, and the written density ratio limit
`3/2`. The density witness is zero outside its support, measurable and
nonnegative, and is proved to produce the already normalized Pareto law.
The generic layer-cake converse also has a direct integrable-survival
witness. The two focused RV modules and every mathematical dependency
are included in the default umbrella and exhaustive private axiom audit.

BF-12 is now established for the stated general RV branch. The operational
thin-tail class interface in BF-04/BF-10 and the Gaussian limit in BF-14
are supplied by the following repairs. No arbitrary-payoff extension or
convergence rate is claimed.

**Verification:** all 3973 default-build jobs pass without warnings.
The standalone audit covers 1777 declarations, including 1523 theorem
declarations, and finds only the three permitted core axioms. Its explicit
imports cover all 173 other project modules, including private declarations.
The regenerated index has 174 modules and 834 named theorems with zero
sorry, vacuous or placeholder markers. All 27 Python tests, the forbidden
check and whitespace check pass. The refreshed declaration index has
930 distinct public names: all 918 previous names and types are unchanged,
with twelve additions and no duplicate names. The expanded layer-cake
module and new RV modules are 176, 149 and 189 lines respectively;
the exhaustive audit aggregator remains 200 lines.

### Separate the audit engine from its exhaustive import list

[StatsAuditSupport.lean](StatsAuditSupport.lean) now contains the operational
`audit_stats` command. The audit aggregator retains the same 173 explicit
`import all` statements, in the same order, and invokes that command.
The extracted scanner body is byte-for-byte identical to the preceding
version: declaration-origin selection, private coverage, per-root
`Lean.collectAxioms` traversal and non-core-axiom rejection are unchanged.
The tooling module is a Lake dependency of the aggregator, so changing the
engine invalidates its compiled audit. Mathematical modules and their
proof dependencies are unchanged. The import aggregator is now 178 lines,
leaving room for further explicit proof-module imports.

**Verification:** all 3974 default-build jobs pass without warnings.
The standalone audit retains 1777 declarations, 1523 theorem declarations
and only the three core axioms. The generated index retains 174 modules,
834 named theorems and zero sorry, vacuous or placeholder markers.
All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index retains the same 930 public names and
exact types, with no duplicate names.

### Actual Gaussian conditional mean and the Mills-ratio limit

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 4 (lines 317–327), the explicit linear-payoff restriction and
Theorem 1 (lines 351–365), and **Thin tails**, especially the centered
normalized Gaussian example and Eq. 6 (lines 367–376). This repair is
for the actual standard Gaussian population. It does not infer the same
limit for every law informally labeled thin-tailed.

[MillsLimit.lean](Stats/BlackScholes/MillsLimit.lean) proves the missing
asymptotic from the actual normal CDF and PDF. With `Q=1-Phi` and
`phi` the standard Gaussian PDF, L'Hopital's rule applies to
`Q(K)/(phi(K)/K)`. The derivatives are `-phi(K)` and
`-phi(K)*(1+K^(-2))`; their ratio tends to one. The proof verifies the
eventual derivative conditions, nonzero denominator derivative and both
vanishing functions. Taking the reciprocal gives

```text
phi(K)/(K*Q(K)) -> 1.
```

[GaussianLaw.lean](Stats/BinaryForecasts/GaussianLaw.lean) proves positive
actual upper-tail probability, normalization of the conditional measure
and genuine L1 of the conditional observation at every finite threshold.
Gaussian `L1` follows from the actual law's finite first absolute moment;
it is transferred to the density-weighted first moment before applying
the improper-integral fundamental theorem. Consequently the actual first
tail moment is `phi(K)` for every real `K`, extending the earlier analytic
lemma's nonnegative-threshold domain. The normalized conditional mean is
the actual integral `phi(K)/Q(K)`.

`stdNormal_tailMean_ratio_tendsto`, `stdNormal_condMean_ratio_tendsto`
and `stdNormal_I1_div_I2_tendsto` prove, respectively, the actual tail
ratio limit, actual conditional-mean ratio limit and the source's written
Gaussian density `I1/I2` limit. In the density statement both integrals
are explicitly identified with the actual law's tail quantities.
No finite moment or conditional expectation is supplied as a desired value.

Concrete instances check positive tail probability below zero, normalized
conditioning above one, almost-sure conditional support and L1. Additional
certificates check the actual first moment above minus one and the actual
conditional mean above zero, `2*phi(0)`, using the proved CDF symmetry.
Both focused modules are publicly exposed and explicitly included in the
private axiom audit. BF-13's actual first-moment bridge and BF-14's standard
Gaussian limits are now established. The following repair supplies the
source's general operational class interface in BF-04/BF-10.

**Verification:** all 3977 default-build jobs pass without warnings.
The standalone audit covers 1796 declarations and 1542 theorem declarations,
with only the three permitted core axioms. It explicitly imports all 175
other project modules, including private declarations. The regenerated
index has 176 modules and 845 named theorems, with zero sorry, vacuous or
placeholder markers. All 27 Python tests, the forbidden check and whitespace
check pass. The refreshed declaration index has 940 distinct public names:
all 930 previous names and types are unchanged, with ten additions and no
duplicate names. The two focused modules are 83 and 144 lines.

### Definition 4's actual operational classes and both Theorem 1 implications

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 4 and its three bullets (lines 317–327), Definition 5's two
density integrals (lines 342–346), the explicit `g(x)=x` restriction
(line 351), and Theorem 1's proof, **From Eq. chscale** (lines 353–366).
The class hypotheses in that named theorem refer back to the operational
conditional-mean limit in Definition 4.

[CharacteristicClasses.lean](Stats/BinaryForecasts/CharacteristicClasses.lean)
now defines `HasCharacteristicScale nu scale` by that literal limit of
the actual normalized conditional mean divided by the threshold. The
source's operational D1 and D2 classes mean limit one and existence of
a finite limit strictly above one, respectively. The borderline
exponential condition uses the actual conditional mean minus the
threshold and a positive finite limiting excess. These are predicates
of the supplied actual law and limit parameters; no mean is defined by
a desired closed expression.

`HasCharacteristicScale.wellDefined` proves that a nonzero limiting
scale forces actual conditional normalization, conditional L1 and
upper-tail L1 eventually. A ratio eventually separated from zero has
a nonzero actual integral, which proves its integrability. A zero tail
measure would give a zero conditional measure and contradict that
nonzero integral. Finiteness then gives actual probability normalization,
and the nonzero finite normalizing weight transfers L1 back to the
population's restricted tail. Thus the source's positive operational
classes cannot acquire their limits through totalized nonintegrable
zero integrals or empty tails.

`HasCharacteristicScale.densityRatio` identifies that actual conditional
quantity with the written `I1 id f K / I2 id f K` for a nonnegative
measurable density explicitly generating the same law. Both
`thinTail_I1_div_I2_tendsto` and `fatTail_I1_div_I2_tendsto` prove the
source's named implications, together with the eventual actual L1 and
normalization conditions. Their analytic premise is exactly the source's
Definition 4 class condition. This transfer is the proof given in the
paper; the preceding RV and Gaussian repairs independently establish
nontrivial actual-law instances of that premise.

The shared density integration bridge has moved, without changing its
proof, from the private RV helper to
[DensityIntegration.lean](Stats/Probability/DensityIntegration.lean).
That module also proves the density-weighted tail L1 equivalence and
checks both bridges with the actual supported Exp(2) law. All existing
public RV theorem types are preserved.

Class membership is proved for the actual standard Gaussian, every
positive-rate exponential, and every positive-scale Pareto with index
greater than one. The exponential law also meets the source's borderline
condition with limiting excess `1/r`; the operational classes therefore
overlap as their literal definitions permit. Exp(2) supplies concrete
well-definedness, density-transfer and D1 witnesses. A supported,
measurable, nonnegative PDF producing the actual normalized Pareto(2,3)
law supplies the full D2 implication's witness. Every new hypothesis
family has a concrete satisfying instance.

Theorem 1 is now established with its explicit linear-payoff restriction
and its literal operational class definitions. Identifications with
independent analytical tail classes are a separate remaining issue,
recorded explicitly in BF-04a. This repair does not settle the paper's
later nonlinear, distributional or CLT claims.

**Verification:** all 3979 default-build jobs pass without warnings.
The standalone audit covers 1811 declarations and 1553 theorem declarations,
with only the three permitted core axioms. Its explicit imports cover all
177 other project modules, including private declarations. The regenerated
index has 178 modules and 854 named theorems, with zero sorry, vacuous or
placeholder markers. All 27 Python tests, the forbidden check and whitespace
check pass. The refreshed declaration index has 954 distinct public names:
all 940 previous names and types are unchanged, with fourteen additions and
no duplicate names. The class and shared-density modules are 193 and
64 lines. The moved density integration proof is byte-for-byte unchanged.

### Refute Eq. 8's universal positivity assertion

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Remark 1 and the Gaussian proof (lines 463–475). The sentence following
Eq. 8 asserts positivity for all positive thresholds, using the
unit-scale polynomial as its reason. The printed expression also depends
on the positive scale; that polynomial does not determine its general sign.

[SigmaCounterexample.lean](Stats/BinaryForecasts/SigmaCounterexample.lean)
proves strict negativity of the exact printed right-hand side at `K=3`,
`sigma=5`: its numerator is `54-75=-21`, while the exponential and
denominator are strictly positive. It formally refutes the universal
positive-parameter assertion. A further certificate applies the existing
`gaussianEq8_sigmaSensitivity_eq` theorem and obtains a negative
`HasDerivAt` value for the same first-derivative expression that theorem
checks. Both constants satisfy the source's positive-parameter domain.

The old docstring claiming that general-scale positivity follows from
the unit-scale factorization has been corrected. The scalar derivative
theorems and their public types are preserved. This refutation concerns
the printed `A-B` expression; Definition 5's linear-payoff gap is `A-K*B`.
The following repair supplies its corrected actual sensitivity theorem in BF-20.

**Verification:** all 3980 default-build jobs pass without warnings.
The standalone audit covers 1814 declarations and 1556 theorem declarations,
with only the three core axioms. Its explicit imports cover all 178 other
project modules, including private declarations. The regenerated index has
179 modules and 857 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 957 distinct public names: all 954
previous names and types are unchanged, with three additions and no
duplicate names. The new counterexample module is 50 lines.

### Correct the actual Gaussian payoff gap and its scale sensitivity

Reread `papers/arXiv-1907.11162v3/forecastingsubmissionjournalV3ArXiv.tex`,
Definition 5 (lines 342–346), the `g(x)=x` restriction (line 351), and
Remark 1's Gaussian argument and Eq. 8 (lines 463–475). Definition 5
requires `I2=K*P(X>K)`. The subsequent Gaussian proof subtracts the
unweighted probability, so its `A-B` derivative is not the derivative
of the defined `A-K*B` gap. This repair proves the corrected claim and
keeps the printed-expression counterexample separate.

[GaussianScale.lean](Stats/BinaryForecasts/GaussianScale.lean) constructs
`gaussianScaleLaw sigma` by pushing the actual standard Gaussian through
`x -> sigma*x`. It is proved to be the actual centered Gaussian with
variance `sigma^2`, a probability measure with an L1 observation. On
positive scales its actual survival is `Q(K/sigma)` and its actual first
tail moment is `sigma*phi(K/sigma)`, for every finite real threshold.
These follow from measure-map integration and the actual standard
Gaussian moment, not from definitions assigning a desired moment value.

`gaussianPayoffGap` is defined by the two actual law quantities in
Definition 5. It equals the genuine restricted excess expectation
`integral_{X>K}(X-K) dnu`, is nonnegative, and has the proved closed form

```text
G(K,sigma) = sigma*phi(K/sigma) - K*Q(K/sigma).
```

The written density `I1-I2`, with its threshold factor retained, is
identified with this actual gap for `sigma>0`, `K>=0`. The source itself
uses positive thresholds. At positive scales the actual-law closed form
permits every real threshold; normalization and L1 hold for all real
scales, including the separate zero-scale degenerate Gaussian construction.

[GaussianGap.lean](Stats/BinaryForecasts/GaussianGap.lean) differentiates
the actual gap by transferring the proved closed form on a neighborhood
of each positive scale. It proves

```text
partial_sigma G = phi(K/sigma),
partial_sigma^2 G = K^2*phi(K/sigma)/sigma^3.
```

Both first and second derivatives of the original written density gap
are also proved on its stated domain. The actual gap is strictly
increasing on positive scales for every finite threshold. Its second
derivative is strictly positive for `K>0`, `sigma>0`, giving strict
convexity in positive scale. The two-scale Jensen inequality compares
the actual gap at the arithmetic mean scale with the average of the
two actual gaps, strictly when the positive scales differ.

Concrete certificates use `K=3`, `sigma=5`, variance 25 and scales
three and seven around their mean five. The actual second derivative
is `(9/125)*phi(3/5)>0`. A joint certificate checks the already refuted
printed sensitivity is negative at the same parameters. Further
examples identify the actual excess integral, density/law gap,
normalization, L1 and each derivative hypothesis family.

This establishes the corrected Gaussian linear-payoff sensitivity in
BF-20 and its two-scale functional Jensen consequence. The general
uncertain-parameter and higher-kurtosis assertions remain in BF-18; the
following result supplies the two-point mixture-law interpretation.

**Verification:** all 3982 default-build jobs pass without warnings.
The standalone audit covers 1857 declarations and 1597 theorem declarations,
with only the three core axioms. Its explicit imports cover all 179 other
Stats modules, including private declarations. The regenerated index has
181 modules and 877 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 976 distinct public names: all 957
previous names and types are unchanged, with nineteen additions and no
duplicate names. The scale-law and gap-sensitivity modules are 139 and
177 lines.

### Identify the actual two-point random-scale Gaussian population

Reread arXiv:1907.11162v3, Definition 5 and Remark 1, at the source
locations above. The scalar Jensen comparison needs an actual population
model before it implies a larger population payoff gap.

[EqualMixture.lean](Stats/Probability/EqualMixture.lean) constructs the
genuine sum of two half-weighted measures. It proves probability
normalization, real event averaging, an exact L1 criterion, actual
expectation and restricted-expectation averaging, and compatibility
with measurable maps and independent product sampling. The expectation
rule requires component L1, so the result does not use a totalized
nonintegrable integral as a purported moment. Dirac-scale witnesses
verify the proper uncertainty distribution and its actual mean.

[GaussianMixture.lean](Stats/BinaryForecasts/GaussianMixture.lean)
constructs the actual equal mixture of the scale-a and scale-b Gaussian
laws. It identifies this population with the pushforward of the product
of the actual two-point scale law and the standard Gaussian, under
`(scale,z) -> scale*z`. This explicitly makes the scale and Gaussian
innovation independent. The scale's actual expectation is `(a+b)/2`.
The mixture is a probability measure with an L1 observation, and its
actual survival and first tail moment are proved from the component
laws, rather than assigned closed forms.

The actual mixture payoff gap, defined by its actual first tail moment
minus `K` times its actual survival, equals its actual restricted excess
expectation. It is proved to equal the mean of the two component actual
gaps. Consequently, for `K>0` and distinct positive scales, it is
strictly larger than the actual gap of the Gaussian at the mean scale.
The source's omitted threshold factor is corrected throughout. Concrete
certificates use threshold three, scales three and seven, and mean scale
five, verifying the latent model, normalization, L1, survival, first tail
moment and strict inequality.

This closes the population-law bridge for the specified two-point
Gaussian uncertainty model in BF-18. Arbitrary mixing distributions,
other families and general higher-kurtosis comparisons still require
their own actual-law hypotheses and proofs. The next result computes
the actual kurtosis of this same two-point population.

**Verification:** all 3984 default-build jobs pass without warnings.
The standalone audit covers 1883 declarations and 1620 theorem declarations,
with only the three core axioms. Its explicit imports cover all 181 other
Stats modules, including private declarations. The regenerated index has
183 modules and 892 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 997 distinct public names: all 976
previous names and types are unchanged, with twenty-one additions and no
duplicate names. The generic mixture and Gaussian specialization modules
are 125 and 132 lines.

### Compute the same Gaussian mixture's actual moments and kurtosis

Reread arXiv:1907.11162v3, the distributional-uncertainty footnote and
Remark 1 (lines 461–466), and arXiv:1802.05495v3, the switching-Gaussian
model and Eq. 17 (`kappa-n-final.tex`, lines 805–814). A scalar kurtosis
formula alone does not identify a probability population's kurtosis.

[GaussianMoments.lean](Stats/Probability/GaussianMoments.lean) proves
L1 of every natural power of the genuine Gaussian observation. For
the actual centered Gaussian with variance `v`, differentiating the
actual MGF twice and four times gives the actual moments `v` and
`3*v^2`. Variance zero is allowed in these component facts; no desired
moment is supplied as a definition or as an unproved hypothesis.

[GaussianMixtureMoments.lean](Stats/BinaryForecasts/GaussianMixtureMoments.lean)
uses the genuine scale-law identification and the actual integration
rule for the already constructed independent two-point mixture. It
proves L1 of all natural mixture powers, mean zero, actual variance
`(a^2+b^2)/2` and actual fourth central moment `3*(a^4+b^4)/2`.
Pearson kurtosis is defined using those actual central moments and
variance, and its closed form is then proved under nondegeneracy:

```text
Kurt(a,b) = 6*(a^4+b^4)/(a^2+b^2)^2.
```

This ratio equals the earlier `gaussianMixtureKurtosis 0 0 a b`
expression, establishing the actual-law bridge for the centered case
of Eq. 17. Positive distinct scales give actual kurtosis strictly
above three. The baseline positive-scale Gaussian is separately
proved to have actual kurtosis three. A joint theorem certifies that
the same uncertain-scale population has both a larger actual payoff
gap than the Gaussian at mean scale and actual kurtosis above three.
It does not infer a payoff ordering from kurtosis alone.

The scales-three/seven model has actual variance 29, fourth central
moment 3723, and kurtosis `3723/841>3`. Its threshold-three gap still
exceeds the actual scale-five Gaussian gap. Concrete witnesses also
verify the actual fourth-power L1, Gaussian baseline kurtosis and
the Eq. 17 moment identification.

BF-18 now includes this actual higher-kurtosis certificate for the
specified two-point model. This is the centered part of K-43; the
following result supplies the general switching-mean Gaussian moments.

**Verification:** all 3986 default-build jobs pass without warnings.
The standalone audit covers 1915 declarations and 1651 theorem declarations,
with only the three core axioms. Its explicit imports cover all 183 other
Stats modules, including private declarations. The regenerated index has
185 modules and 914 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1016 distinct public names: all 997
previous names and types are unchanged, with nineteen additions and no
duplicate names. The Gaussian MGF-moment and actual mixture-moment modules
are 111 and 171 lines.

### Identify Eq. 17 with the full switching-Gaussian population

Reread `papers/arXiv-1802.05495v3/kappa-n-final.tex`, the model and
Eq. 17 (lines 805–811) and the equal-scale observation and threshold
(lines 814–816). The model chooses between two actual Gaussian laws
with equal probability; the component means can differ.

[GaussianShiftedMoments.lean](Stats/Probability/GaussianShiftedMoments.lean)
proves L1 of powers about arbitrary finite centers under the genuine
Gaussian law. Reflection of the actual centered Gaussian gives its
third moment zero. Pushing that law through addition of the actual
mean and integrating the polynomial expansions gives

```text
E[(X-c)^2] = v + (mu-c)^2,
E[(X-c)^4] = 3*v^2 + 6*v*(mu-c)^2 + (mu-c)^4.
```

All polynomial terms have independent actual-law L1 proofs; these
equalities are actual integrals, including degenerate variance cases.

[GaussianMixtureLaw.lean](Stats/Kappa/GaussianMixtureLaw.lean) constructs
the full equal mixture of `N(mu1,sigma1^2)` and `N(mu2,sigma2^2)` as
a normalized measure. Every natural power about every center is L1.
Its actual mean is `(mu1+mu2)/2`. Writing `d=mu1-mu2`, its actual
variance and fourth central moment are proved to be

```text
V = (d^2 + 2*(sigma1^2+sigma2^2))/4,
M4 = 3*(sigma1^4+sigma2^4)/2
     + 3*d^2*(sigma1^2+sigma2^2)/4 + d^4/16.
```

Under `d^2+2*(sigma1^2+sigma2^2)>0`, their actual Pearson ratio
`M4/V^2` equals the full four-parameter `gaussianMixtureKurtosis`
expression printed in Eq. 17. Both the polynomial and fourth-root
thresholds for actual kurtosis at least three follow. With equal
scales and distinct means, the actual kurtosis is strictly below
three, as the source states.

Concrete proper-law witnesses use means minus two and two and scales
one: actual mean zero, variance five, fourth central moment 43, and
kurtosis `43/25<3`. The common-center scales-three/seven model verifies
the other side of the threshold. L1, normalization, nondegeneracy and
the fourth-root threshold all have concrete certificates.

This closes K-43's actual mixture-moment identification and K-44's
probability interpretation. The actual MAD-based kappa, its sign and
the source's necessity-of-bimodality assertion remain separate in
K-45 and K-46. Kurtosis below three alone does not prove them.

**Verification:** all 3988 default-build jobs pass without warnings.
The standalone audit covers 1933 declarations and 1667 theorem declarations,
with only the three core axioms. Its explicit imports cover all 185 other
Stats modules, including private declarations. The regenerated index has
187 modules and 926 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1031 distinct public names: all 1016
previous names and types are unchanged, with fifteen additions and no
duplicate names. The shifted-Gaussian and full mixture-law modules are
123 and 159 lines.

### Construct the finite branching population and prove its outcome moments

Reread `papers/arXiv-1912.00277v2/FatTailsEpistemic2019.tex`, the
equiprobable scale branches and repeated Gaussian mixtures (lines
234–276), and Section III's constant-error moments, symmetry and
kurtosis (lines 318–346). The printed fourth raw moment starts with
`3*mu^4`; the actual coefficient is one. Its other terms are retained.

[BranchingLaw.lean](Stats/EpistemicUncertainty/BranchingLaw.lean)
constructs the actual finite recursive population. Depth zero is the
genuine Gaussian with mean `mu` and variance `sigma^2`; each additional
layer equally mixes the recursively constructed populations with base
scales `sigma*(1+epsilon)` and `sigma*(1-epsilon)`. Every finite depth
is a probability measure, with L1 powers of every natural order about
every finite center. The actual mean stays `mu`, and reflection about
`mu` preserves the whole actual measure. On the source's domain
`sigma>0`, `epsilon in [0,1)`, all branch standard deviations are
positive. The measure and moment identities also extend through
squared variances to the other real parameters in their Lean statements.

[BranchingMoments.lean](Stats/EpistemicUncertainty/BranchingMoments.lean)
integrates the actual recursive measure, using independently proved
component L1 at each induction step. For `A=1+epsilon^2` and
`B=1+6*epsilon^2+epsilon^4`, its actual raw moments are

```text
E[X]   = mu,
E[X^2] = mu^2 + sigma^2*A^n,
E[X^3] = mu^3 + 3*mu*sigma^2*A^n,
E[X^4] = mu^4 + 6*mu^2*sigma^2*A^n + 3*sigma^4*B^n.
```

The actual variance is `sigma^2*A^n`; the actual third central moment
is zero and the actual fourth central moment is `3*sigma^4*B^n`.
The formulas are proved about arbitrary centers before specializing
to raw or central moments. The supporting actual Gaussian third
moment about an arbitrary center is added in GaussianShiftedMoments.

[BranchingKurtosis.lean](Stats/EpistemicUncertainty/BranchingKurtosis.lean)
identifies the actual variance and fourth central moment with the
earlier weighted scale expressions. It proves positive actual variance
for nonzero base scale, zero standardized third moment, and equality
of the actual Pearson kurtosis with `epistemicKurtosis`. Consequently
the raw and excess closed expressions, the lower bound three, and
strictness at positive depth and nonzero uncertainty now concern
the actual probability population.

The proper one-layer example `mu=sigma=1`, `epsilon=1/2` has actual
second and third raw moments `9/4` and `19/4`, actual fourth raw
moment `259/16`, variance `5/4`, central fourth moment `123/16`,
Pearson kurtosis `123/25` and excess kurtosis `48/25`. The source's
printed fourth raw formula instead gives `291/16`; a formal actual-law
counterexample proves their inequality. A depth-two example verifies
normalization, L1, mean preservation and full reflection invariance.

This closes EU-09–EU-11 and EU-13–EU-15 for the constant-error
recursive population, and proves the corrected EU-12 theorem together
with a refutation of the literal source expression. The explicit sign
probability space, binomial count pushforward, finite density identity,
arbitrary nested kernels and infinite-depth law remain separate.

**Verification:** all 3991 default-build jobs pass without warnings.
The standalone audit covers 1972 declarations and 1700 theorem declarations,
with only the three core axioms. Its explicit imports cover all 188 other
Stats modules, including private declarations. The regenerated index has
190 modules and 950 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1058 distinct public names: all 1031
previous names and types are unchanged, with twenty-seven additions and no
duplicate names. The three branching modules are 95, 146 and 111 lines;
the extended shifted-Gaussian helper is 156 lines.

### Prove geometric divergence for the actual branching populations

Reread arXiv:1912.00277v2, Section III's actual moment formulas and
the divergence assertions in `FatTailsEpistemic2019.tex`, lines
329–346. Nonzero base scale and nonzero uncertainty are needed:
zero error leaves a constant variance and Gaussian kurtosis.

[BranchingLimits.lean](Stats/EpistemicUncertainty/BranchingLimits.lean)
proves the actual variance and fourth central moment tend to positive
infinity with depth when `sigma!=0` and `epsilon!=0`. These are the
actual moment sequences of the normalized finite laws constructed
above, with their finite-depth L1 already proved.

Writing `A=1+epsilon^2` and `B=1+6*epsilon^2+epsilon^4`, actual Pearson
kurtosis is proved to be the geometric sequence `3*(B/A^2)^n`.
The existing strict factor inequality gives `B/A^2>1` for nonzero
uncertainty. Actual Pearson kurtosis and the source's excess kurtosis
therefore both tend to positive infinity. The variance and central
fourth moment grow geometrically with bases `A` and `B` respectively.

The half-error, unit-scale example verifies growth bases `5/4`,
`41/16` and `41/25` for actual variance, fourth central moment and
kurtosis. All four divergence claims have concrete proper-law
certificates. At zero error, actual variance is exactly `sigma^2`
at every finite depth, and actual Pearson kurtosis is three for a
nonzero base scale; a depth-ten certificate checks this boundary.

This closes EU-16 for these actual finite-population moment sequences
with the necessary nonzero hypotheses. No infinite-depth population,
weak convergence result, or regularly varying tail is asserted by
the divergence of moments.

**Verification:** all 3992 default-build jobs pass without warnings.
The standalone audit covers 1979 declarations and 1707 theorem declarations,
with only the three core axioms. Its explicit imports cover all 189 other
Stats modules, including private declarations. The regenerated index has
191 modules and 957 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1065 distinct public names: all 1058
previous names and types are unchanged, with seven additions and no
duplicate names. The new limits module is 110 lines.

### Identify the actual dispersion law and independent Gaussian model

Reread arXiv:1912.00277v2, Section II's positive random dispersion
with expected value `sigma` (lines 204–214), its equiprobable
multiplicative branches (lines 234–276), and Section III's natural
dispersion-moment formula (lines 318–332).

[ScaleLaw.lean](Stats/EpistemicUncertainty/ScaleLaw.lean) constructs the
actual finite dispersion distribution by starting from a Dirac mass at
`sigma` and recursively mixing the two perturbed base scales equally.
It is a probability measure at every finite depth. Every natural
dispersion power is independently proved L1 before its genuine integral
is evaluated. The actual moment is `sigma^k*M_k(epsilon)^n`, and hence
equals the existing `epistemicSigmaMoment` for every natural order.
The actual expected dispersion is `sigma`, as the source requires.
For positive base scale and `0<=epsilon<1`, the actual dispersion is
strictly positive almost everywhere.

The actual outcome population is identified with the pushforward of
the product of this dispersion law and the actual standard Gaussian
under `(s,z) -> mu+s*z`. Thus the dispersion and innovation are
independent, and this genuine random-scale construction equals the
previously built recursive Gaussian population at every finite depth.
The base case uses a proved affine Gaussian pushforward identity;
the recursion uses compatibility of actual mixture, product and map.
This identifies the whole outcome law, rather than only its moments.

A proper depth-two, base-scale-two, half-error model verifies actual
fourth-power L1, mean dispersion two, fourth dispersion moment `1681/16`,
positive actual standard deviation and the independent-product law
identity with the mean-one outcome population.

This closes EU-06's actual natural-order dispersion-moment bridge and
the constant-error random-scale interpretation in EU-01. The explicit
equiprobable sign-vector space, binomial count pushforward, density
identity and general nested uncertainty kernels remain separate.

**Verification:** all 3993 default-build jobs pass without warnings.
The standalone audit covers 1997 declarations and 1720 theorem declarations,
with only the three core axioms. Its explicit imports cover all 190 other
Stats modules, including private declarations. The regenerated index has
192 modules and 964 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1074 distinct public names: all 1065
previous names and types are unchanged, with nine additions and no
duplicate names. The scale-law module and extended Gaussian helper are
123 and 168 lines.

### Test the depth-limit tail claim using actual fractional moments

Reread arXiv:1912.00277v2, Section III's moment formulas and growth
discussion (lines 326–346) and its apparent power-law depth behavior
(line 358). Higher moment divergence does not identify a weak limit.
The actual dispersion law now permits a separate check using
fractional powers.

[FractionalMoments.lean](Stats/EpistemicUncertainty/FractionalMoments.lean)
extends the actual natural-order dispersion calculation to every real
order `p`, on the source's positive-scale domain `sigma>0` and
`0<=epsilon<1`. The genuine finite-law moment is

```text
E[Sigma_n^p] = sigma^p * (((1+epsilon)^p+(1-epsilon)^p)/2)^n.
```

The finite recursive atomic construction independently proves L1 of
every real-valued function of the dispersion; no moment value is
assumed. For `0<p<1` and `0<epsilon<1`, strict concavity of the real
power gives a strictly positive per-layer factor below one. The actual
fractional dispersion moments therefore tend to zero geometrically.
Positive base scale two, half error and order one-half supply concrete
L1, moment, strict-contraction and limit certificates.

This result concerns the same actual dispersion population whose mean
stays `sigma` and whose associated outcome variance diverges. It
provides additional evidence for analyzing EU-17; it does not by
itself assert a limiting outcome law or a tail-class theorem.

**Verification:** all 3995 default-build jobs pass without warnings.
The standalone audit covers 2001 declarations and 1724 theorem declarations,
with only the three core axioms. Its explicit imports cover all 191 other
Stats modules, including private declarations. The regenerated index has
193 modules and 968 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1078 distinct public names: all 1074
previous names and types are unchanged, with four additions and no
duplicate names. The fractional-moment module is 97 lines; the scale-law
module is 130 lines after extracting general finite-law L1.

### Identify the actual unscaled depth limit

Reread arXiv:1912.00277v2, Section III's divergence discussion and
apparent power-law behavior (`FatTailsEpistemic2019.tex`, lines
344–358). The depth limit must be distinguished from a moving-threshold
or rescaled tail claim. Here the base scale, error and common mean
are fixed as depth tends to infinity.

[ScaleConcentration.lean](Stats/EpistemicUncertainty/ScaleConcentration.lean)
applies Markov's inequality to the actual integrable fractional
dispersion power. Positivity of the actual dispersion identifies
the power event with the actual threshold event. For every fixed
positive threshold, the actual dispersion tail probability tends
to zero. The portmanteau closed-set criterion then proves that the
actual dispersion probability laws converge weakly to `Dirac(0)`.
The proof controls every closed set away from zero by one of those
actual tail probabilities.

[OutcomeLimit.lean](Stats/EpistemicUncertainty/OutcomeLimit.lean)
carries this genuine weak limit through the actual independent
Gaussian product model. Continuity of probability-measure products
and the map `(s,z) -> mu+s*z` gives

```text
actual outcome law at depth n  -> weakly Dirac(mu),
for sigma>0 and 0<epsilon<1, with mu, sigma, epsilon fixed.
```

The transformed limiting product law is computed explicitly: its
scale coordinate is zero, so its outcome is the constant `mu`.
Weak-limit uniqueness formally excludes any different probability
law as an unscaled weak limit of this population sequence. A joint
theorem proves that the same actual sequence has this point-mass
weak limit and divergent actual variance. Moment divergence is
therefore not a moment formula for a nondegenerate limiting law.

The positive base scale two, half error and common mean one model
verifies the actual Markov bound, vanishing dispersion tail at
threshold one, both weak limits, an actual weak-limit witness for
the uniqueness theorem, and the joint divergent-variance assertion.

This settles the fixed-parameter unscaled weak-limit question in
EU-17. A nondegenerate power-law weak-limit interpretation is
incompatible with these actual laws. The source's looser graphical
tail-shape discussion, a moving-threshold asymptotic, a rescaled
limit, and a finite-depth regular-variation theorem are different
claims and are not supplied by this result.

**Verification:** all 3999 default-build jobs pass without warnings.
The standalone audit covers 2014 declarations and 1735 theorem declarations,
with only the three core axioms. Its explicit imports cover all 193 other
Stats modules, including private declarations. The regenerated index has
195 modules and 974 named theorems, with zero sorry, vacuous or placeholder
markers. All 27 Python tests, the forbidden check and whitespace check pass.
The refreshed declaration index has 1086 distinct public names: all 1078
previous names and types are unchanged, with eight additions and no
duplicate names. The concentration and outcome-limit modules are 114 and
101 lines.

### Prove the actual binomial collapse of dispersion and Gaussian populations

Reread arXiv:1912.00277v2, the fair branching construction (lines
234–276) and Section III's binomial collapse (`FatTailsEpistemic2019.tex`,
lines 318–324). The claim concerns the actual distribution, beyond
the earlier equality of its natural moments.

[BinomialCollapse.lean](Stats/EpistemicUncertainty/BinomialCollapse.lean)
first integrates any real-valued test function against the actual
recursive dispersion law. Pascal's identity and the two actual branch
expectations yield the printed binomial-weighted finite sum. Component
L1 is supplied by the genuine finite atomic law. Comparing every bounded
continuous test function with Mathlib's actual Binomial(n,1/2) measure
then proves the whole measure identity

```text
actual dispersion law = Binomial(n,1/2).map
  (j -> sigma*(1+epsilon)^j*(1-epsilon)^(n-j)).
```

This is a whole-law proof using the actual recursive expectation;
it does not assume moment determinacy or define the dispersion law
by the desired binomial distribution.

The independent Gaussian product model carries this actual count
representation to the actual outcome population. Mapping the finite
Binomial Dirac expansion, multiplying by the standard Gaussian law,
and applying the proved affine Gaussian map gives

```text
actual outcome law = sum_{j=0}^n [choose(n,j)/2^n] *
  N(mu, (sigma*(1+epsilon)^j*(1-epsilon)^(n-j))^2).
```

The coefficients are explicitly reduced from the genuine Binomial
probabilities, and every intermediate weighted Dirac measure has
proved finiteness. All real means and scales are allowed in the measure
identity; the source's positive standard-deviation domain is included.
The density identity under positive scales remains separate.

For depth two, base scale two and error one-half, a concrete actual
probability calculation gives dispersion `3/2` with probability
exactly one-half. Further witnesses verify a natural test-function
expectation, the Binomial measure pushforward and the genuine Gaussian
mixture with mean one.

This closes EU-05's constant-error binomial collapse for the actual
recursive populations. General nonconstant-error sign constructions
and density formulas remain in EU-01 and EU-04.

Verification: the full build passes 4,070 jobs without warnings. The
axiom audit checks 2,034 declarations and 1,755 theorems with zero
non-core axioms. The regenerated index has 196 modules and 980 named
theorems, with zero `sorry`, vacuous or placeholder entries. All 27
Python tests, forbidden-pattern and whitespace checks pass. The refreshed
declaration index preserves all 1,086 previous names and types, adding
three without duplicates. The audit explicitly imports all 194 other
`Stats/` modules. The new module is 180 lines; its statements were checked
against the local Section III source and the finite fair-branch model.

### Identify the actual normalized binomial Gaussian density

Reread arXiv:1912.00277v2, Section III's binomial Gaussian formula
(`FatTailsEpistemic2019.tex`, lines 318–324), beside the finite actual
measure construction of Sections II–III. The source assumes positive
base dispersion and error in `[0,1)`.

[BinomialDensity.lean](Stats/EpistemicUncertainty/BinomialDensity.lean)
proves every displayed component standard deviation is positive, then
identifies the actual recursive population with Lebesgue measure weighted
by the printed finite density. The proof starts with the independently
constructed Gaussian mixture measure. Each genuine nondegenerate Gaussian
has its actual Gaussian density, and finite-sum and scalar linearity of
`withDensity` transport the proved probability weights to the real density.
The population is not defined by this density identity.

The density is independently proved nonnegative, measurable and L1.
Applying the actual law's total mass to its density bridge proves its
nonnegative integral is one; its real integral is one as well. Actual
probabilities of every measurable event equal restricted real density
integrals. A depth-two, mean-one, scale-two, error-one-half population
witnesses the density bridge, both normalizations, L1 and an actual
threshold-three exceedance integral.

This proves the constant-error density part of EU-04 and the genuine
survival-integral part of EU-18. General varying-layer sign densities,
the closed-form exceedance sum and certified numerical tables remain.

Verification: the full build passes 4,071 jobs without warnings; the
audit checks 2,046 declarations and 1,766 theorems with zero non-core
axioms. The index records 197 modules and 989 named theorems, with zero
`sorry`, vacuous or placeholder entries. All 27 Python tests and the
forbidden-pattern and whitespace checks pass. The declaration index
preserves all 1,089 old names and types and adds nine without duplicates.
The audit imports all 195 other `Stats/` modules. The density module
is 156 lines; its positive-scale statements match the local source.

### Prove the corrected actual exceedance formula and integral erfc bridge

Reread arXiv:1912.00277v2, Section III's exceedance formula and its erfc
integral definition (`FatTailsEpistemic2019.tex`, lines 366–374). For a
population with common mean `mu`, the threshold in the printed numerator
must be centered: `K-mu`. The source expression is valid as printed when
`mu=0`.

[Erfc.lean](Stats/BlackScholes/Erfc.lean) now proves that the project's
CDF definitions of erf and erfc equal their usual oriented integrals.
The proof starts with the actual Gaussian CDF derivative, proves the
Gaussian density's square-root-two rescaling, and applies the fundamental
theorem of calculus from zero to any real endpoint. Gaussian reflection
supplies `Phi(0)=1/2`. Thus the erfc notation has the exact source integral
meaning, beyond an algebraic wrapper around an unspecified special function.

[BinomialSurvival.lean](Stats/EpistemicUncertainty/BinomialSurvival.lean)
proves actual non-strict Gaussian exceedances by mapping a standard Gaussian
through `mu+sigma*z`. Positivity gives the correct preimage, and the true
standard Gaussian has no atoms. Applying the actual binomial Gaussian
measure identity to the event and converting its finite weights to real
probabilities yields the centered CDF sum. The proved erfc bridge converts
this to the corrected source formula, including the extra factor one-half.

The general-mean correction is checked by an actual N(1,1) counterexample:
at threshold one, the actual probability is one-half, while the printed
uncentered value is strictly smaller. Separate theorems prove the source's
zero-mean specialization and the actual half-probability above the common
mean at every finite depth. Positive scale-two, error-one-half, depth-two
populations witness the CDF, erfc, zero-mean and common-mean formulas.

EU-18's corrected analytic exceedance identity is proved. The numerical
tables and their error-parameter labels still require certified checks.

Verification: the full build passes 4,072 jobs without warnings. The
audit checks 2,058 declarations and 1,778 theorems with zero non-core
axioms. The regenerated index has 198 modules and 999 named theorems,
with zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,098 previous public
names and types are preserved; nine are added without duplicates. The
audit explicitly imports all 196 other `Stats/` modules. The survival
and error-function modules are 142 and 150 lines, respectively.

### Construct actual varying-error laws and derive the decaying moment products

Reread arXiv:1912.00277v2, Section II's varying fair branches (lines
234–276) and Section IV's variance and fourth central moment products
(`FatTailsEpistemic2019.tex`, lines 416–441).

[LayerLaw.lean](Stats/EpistemicUncertainty/LayerLaw.lean) constructs
actual finite dispersion and Gaussian populations for arbitrary real
layer errors. Both are independently normalized probability measures;
every real dispersion test and every natural outcome power about any
center are L1. The outcome mean stays `mu`. Sampling the actual dispersion
independently of a standard Gaussian under `mu+scale*z` generates exactly
the recursive outcome population. The actual dispersion is positive a.e.
for positive base scale and source errors in `[0,1)`. Constant errors
recover the previous whole-law populations.

[LayerMoments.lean](Stats/EpistemicUncertainty/LayerMoments.lean) integrates
the actual laws. Natural dispersion moments are products of the individual
layer factors. Outcome moments about every center give the true variance
and fourth central moment as the source's varying-error products. Geometric
errors `epsilon_1*kappa^i` identify the actual variance with the older
scalar `decayingErrorVariance`, and give the displayed actual fourth central
moment product. The earlier lower bound and monotonicity are transferred
to actual variances. A proper scale-two, mean-one, depth-two law with errors
one-half and one-quarter has variance `85/16` and fourth central moment
`43419/256`.

The zero-based model index represents the source's error `epsilon_(i+1)`.
Thus its prose `epsilon_n=kappa^n*epsilon_1` needs exponent `n-1`, while
the displayed product's zero-based powers are correct. The source's
negative q-Pochhammer argument also conflicts with its printed plus-sign
product definition. A genuine one-layer variance counterexample gives
`5/4` against that convention's `3/4`. The usual minus-sign convention
repairs the notation without changing the actual proved variance product.

EU-19's corrected actual variance product, EU-20's actual comparisons and
EU-21's actual fourth central moment are proved. Explicit sign-vector
densities, infinite-product limits and numerical coefficients remain separate.

Verification: the full build passes 4,074 jobs without warnings. The
audit checks 2,102 declarations and 1,812 theorems with zero non-core
axioms. The regenerated index has 200 modules and 1,018 named theorems,
with zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. The declaration index
preserves all 1,107 old names and types and adds 23 without duplicates.
The audit explicitly imports all 198 other `Stats/` modules. The law and
moment modules are 151 and 188 lines; the source statements, zero-based
indices and sign correction were checked against the local manuscript.

### Bound and converge the actual decaying-error moment sequences

Reread arXiv:1912.00277v2, Section IV's capped-moment claims, variance
product and fourth central moment (`FatTailsEpistemic2019.tex`, lines
416–441). The necessary geometric decay is `0<=kappa<1`.

[DecayingBounds.lean](Stats/EpistemicUncertainty/DecayingBounds.lean)
proves the source parameters keep the actual dispersion positive a.e.
at every finite depth. Starting from actual outcome moments, finite
products are bounded by exponentials of finite sums; convergent geometric
sums then give uniform bounds

```text
actual variance <= sigma^2 * exp(epsilon_1^2/(1-kappa^2))
actual central fourth moment <= 3*sigma^4 *
  exp(6*epsilon_1^2/(1-kappa^2)+epsilon_1^4/(1-kappa^4)).
```

[DecayingLimits.lean](Stats/EpistemicUncertainty/DecayingLimits.lean)
proves the actual fourth central moment increases with depth for arbitrary
varying errors. Together with the earlier actual variance monotonicity,
the uniform caps give finite real limits for both true moment sequences.
Each limit lies between its base Gaussian moment and its displayed cap.
No infinite-depth distribution or expectation/limit interchange is assumed.

For mean one, scale two, initial error one-half and decay one-half,
concrete witnesses place the actual variance limit in `[4,4*exp(1/3)]`
and the actual fourth central moment limit in `[48,48*exp(31/15)]`.
The nondecaying `kappa=1` endpoint is separately checked: the actual
varying-error population reduces to the proved constant-error law, and
its variance diverges for nonzero scale and error. Thus the source's
closed parameter interval cannot alone supply a capped-moment claim.

EU-22's actual second- and fourth-moment bounds and finite limits are
proved. All-orders bounds, identification of an infinite-depth law,
the displayed numerical coefficients and joint parameter limits remain.

Verification: the full build passes 4,077 jobs without warnings. The
audit checks 2,113 declarations and 1,823 theorems with zero non-core
axioms. The index records 202 modules and 1,027 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,130 previous public
names and types are preserved; seven are added without duplicates.
The audit explicitly imports all 200 other `Stats/` modules. The bounds
and limits modules are 107 and 114 lines. Their actual-law domains and
endpoint distinction were checked against the local Section IV source.

### Identify the explicit independent sign model and general finite density

Reread arXiv:1912.00277v2, Remark 1 and Section II's fair sign construction,
Eq. gn, matrix T and vector M (`FatTailsEpistemic2019.tex`, lines 169–181
and 234–315). This concerns the finite fair-branch model actually analyzed
in the source; general nested uncertainty kernels remain separate.

[SignLaw.lean](Stats/EpistemicUncertainty/SignLaw.lean) constructs the
actual official uniform measure on all `Fin n -> Bool` vectors. Its
singleton probabilities are `2^(-n)` from the true finite cardinality.
Comparing every singleton proves this whole measure equals the product
of the actual fair Boolean measures. Every coordinate is genuinely fair,
and the coordinates are mutually independent. The source scale product
is positive for every vector on its positive-scale, `[0,1)`-error domain.

[SignExpansion.lean](Stats/EpistemicUncertainty/SignExpansion.lean)
reindexes complete sign vectors by their last sign and preceding vector.
Induction on the actual recursive laws gives the exact finite Dirac
expansion of dispersion and Gaussian measure expansion of outcomes.
Mapping the actual sign space gives exactly the earlier varying-error
dispersion law. Sampling these actual signs independently of a standard
Gaussian and applying `mu+scale*z` gives exactly the actual outcome law.
The source's `2^n` mixture is thus a whole probability-law identity.

[SignDensity.lean](Stats/EpistemicUncertainty/SignDensity.lean) transfers
the proved component measures to Eq. gn's real Gaussian density. Its
nonnegativity, measurability and L1 are proved independently; the existing
actual law then supplies normalization of both density integrals and
actual probabilities as restricted real density integrals. Depth-two,
scale-two, mean-one populations with different errors one-half and
one-quarter witness the actual generation and normalized density.

The local source check also finds a row-order inconsistency: its displayed
T starts with all plus signs, whereas M^3 and M_1^3 start with all minus
signs. The declared `M_i=prod(1+epsilon_j*T_ij)` gives first multiplier
`27/8` when every error is one-half; the illustrated M_1^3 gives `1/8`.
A formal source counterexample records that discrepancy. The density sum
is unaffected by a consistent permutation of rows and is proved as stated.

EU-01's explicit finite fair-branch generation and EU-04's actual general
finite density are proved, with the source's row illustration corrected.
General continuous/dependent uncertainty kernels remain in EU-03.

Verification: the full build passes 4,088 jobs without warnings. The
audit checks 2,146 declarations and 1,852 theorems with zero non-core
axioms. The index records 205 modules and 1,049 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. The declaration index
preserves all 1,137 previous names and types, adding 27 without duplicates.
The audit imports all 203 other `Stats/` modules. The sign-space,
expansion and density modules have 145, 98 and 142 lines. Their source
correspondence includes the full Section II matrix/vector illustration.

### Construct the actual general-prior Gaussian kernel and marginal density

Reread arXiv:1912.00277v2, Section II, Eq. 1's positive-dispersion mixture
(`FatTailsEpistemic2019.tex`, lines 205–218). Its scale prior may be
continuous; the finite sign tree is no longer needed for this construction.

[GaussianKernel.lean](Stats/EpistemicUncertainty/GaussianKernel.lean)
constructs the actual measurable kernel `scale -> N(mu,scale^2)` and
proves every conditional measure is a probability law. Binding any
probability dispersion prior gives an independently normalized marginal.
Its whole law equals independent sampling of that prior and a standard
Gaussian under `mu+scale*z`. For the actual finite varying-error prior,
it exactly recovers the already proved recursive population.

The Gaussian density is jointly measurable in scale and outcome. For
every probability prior concentrated on positive scales, actual component
event probabilities are their genuine density integrals. Tonelli then
proves the actual marginal law is Lebesgue measure weighted by the prior
integral of those densities. The derived density is measurable, normalized
and finite Lebesgue-a.e. Its nonnegative scale integral allows exceptional
infinite point values, so no unjustified pointwise L1 assumption is hidden
in the source's displayed integral. Actual event probabilities are integrals
of this proved marginal density.

Concrete proper priors include dispersion fixed at two and the actual
depth-two varying-error law with base scale two and errors one-half and
one-quarter. Both satisfy the positive-support conditions independently.
This closes Eq. 1's general-prior kernel, normalization and density
interchange part of EU-03. The full nested conditional hierarchy remains.

Verification: the full build passes 4,089 jobs without warnings. The
audit checks 2,163 declarations and 1,866 theorems with zero non-core
axioms. The index records 206 modules and 1,058 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. The declaration index
preserves all 1,164 old names and types and adds 14 without duplicates.
The audit explicitly imports all 204 other `Stats/` modules. The new
kernel module is 183 lines and its conditional variance, positive prior
support and measure/density integrals match the local Eq. 1 source.

### Construct actual conditional hierarchies and their iterated marginal densities

Reread arXiv:1912.00277v2, Section II's nested-mixture discussion and
multi-layer display (`FatTailsEpistemic2019.tex`, lines 220–231). The
Gaussian must depend on the sampled observation scale, replacing the
fixed sigma printed in that display. Conditional scale laws must also
record their dependence on the parent parameter.

[HierarchyLaw.lean](Stats/EpistemicUncertainty/HierarchyLaw.lean)
constructs the actual finite scale population by binding successive
measurable conditional kernels to the previous law. A proper prior and
Markov transitions give a probability law at every depth. Positive
scale support is proved to propagate from the prior through each
positive conditional transition, so it is not assumed for the final
Gaussian mixture. An actual fair two-branch kernel depends on the incoming
scale and supplies independent proper witnesses for these assumptions.

[HierarchyDensity.lean](Stats/EpistemicUncertainty/HierarchyDensity.lean)
proves actual nonnegative integration under this population equals the
full repeated conditional integral. Kernel measurability propagates
measurability of each inner integral before the bind integration theorem
is applied. The final actual Gaussian mixture then has this iterated
Gaussian density, with the Gaussian using the last sampled dispersion.
Its density is measurable, normalized and finite Lebesgue-a.e.; actual
event probabilities are its restricted integrals.

An explicit two-transition example starts at scale two, uses actual
fair one-half error kernels at each stage, and writes the complete
prior/conditional/conditional Gaussian density integral. General-depth
examples verify normalized genuine outcome laws and density mass one;
separate examples verify nonnegative-moment integration and actual
threshold-three probabilities.

EU-03's normalized finite conditional Markov construction, positive-support
propagation and corrected iterated density are proved. Constructing its
kernels from arbitrary conditional Lebesgue-density inputs and rewriting
the integrals to the source's literal products of `f_i` remain separate.

Verification: the full build passes 4,091 jobs without warnings. The
audit checks 2,201 declarations and 1,891 theorems with zero non-core
axioms. The index records 208 modules and 1,068 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,178 previous public
names and types are preserved; 17 are added without duplicates. The audit
explicitly imports all 206 other `Stats/` modules. The hierarchy law and
density modules are 119 and 180 lines, with the conditional source
parameter correction recorded in their docstrings.

### Build the source's actual conditional density inputs and literal nested products

Reread arXiv:1912.00277v2, Section II's density inputs, Eq. 1 and the
multi-layer display (`FatTailsEpistemic2019.tex`, lines 205–232). The
corrected construction states joint measurability explicitly, normalizes
conditional densities on positive scales, records their parent dependence,
and replaces the displayed fixed Gaussian sigma by the sampled observation
scale. Transition order runs from outer uncertainty toward that scale.

[DensityKernel.lean](Stats/EpistemicUncertainty/DensityKernel.lean)
constructs actual positive priors and conditional kernels directly from
nonnegative Lebesgue-density inputs. The prescribed conditional integral
one gives a genuine Markov law; absolute continuity gives positive support.
Its actual nonnegative test-function integrals are exactly the source's
density-weighted positive-half-line integrals. A continuous conditional
density uniform on `(1+s^2,2+s^2]` is jointly measurable and normalized
by Lebesgue interval length, and explicitly depends on its parent scale.

[DensityInputs.lean](Stats/EpistemicUncertainty/DensityInputs.lean)
proves the actual kernel hierarchy equals the literal repeated integrals
weighted by every `f_i`. The two-layer result pulls the outer factor inside
the inner integral with justified measurability, giving exactly
`f_0*f_1*GaussianPDF`. The actual Gaussian outcome law has this density,
whose normalization comes from the independently constructed probability
population. No desired marginal formula is assumed as an input condition.

[PositiveDensityInputs.lean](Stats/EpistemicUncertainty/PositiveDensityInputs.lean)
requires the conditional densities to normalize only at positive parents.
A global extension at invalid nonpositive parent parameters makes the kernels
well-defined Markov laws. A positive-domain congruence theorem then proves
that extension changes none of the original repeated density integrals.
The final actual density uses the original `f_i`, is measurable, has total
mass one and is finite Lebesgue-a.e. Its continuous witness is deliberately
zero at nonpositive parents, where it has mass zero rather than one;
thus the theorem's positive-parent assumptions are independently exercised.
Both fixed positive and continuous positive hyperpriors are checked.

EU-03's corrected finite nested-density construction is proved, including
actual kernels, normalization, support and the density-product interchanges.
This does not identify an infinite-depth law or supply the separate CLT,
compound-law approximation, or additional moment and tail claims.

Verification: the full build passes 4,095 jobs without warnings. The
audit checks 2,258 declarations and 1,935 theorems with zero non-core
axioms. The index records 211 modules and 1,095 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. The declaration index
preserves all 1,195 old names and types and adds 38 without duplicates.
The audit imports all 209 other `Stats/` modules. The density-kernel,
input-integral and positive-input modules have 164, 190 and 195 lines;
their source normalization domain and conditional parameter correction
were checked against the local Section II manuscript.

### 2026-10-19: actual iid counterexample to the uncentered lognormal approximation

Section V replaces `log(1+epsilon_i)` by `epsilon_i` and proposes
`log(lambda_n) ~ N(0,S_n^2)` as depth grows. The omitted log-factor
centering changes the claimed asymptotic behavior even for genuinely iid,
bounded, mean-zero errors of arbitrarily small fixed magnitude.

[PrecisionErrors.lean](Stats/EpistemicUncertainty/PrecisionErrors.lean)
constructs one infinite product probability space of independent fair signs.
The actual signed errors have the same two-point law, actual mean zero,
finite second moment and variance `epsilon^2`. The first n coordinates
have precisely the finite uniform sign-vector law. Thus this is one iid
process, with all of the paper's error assumptions independently proved.

[PrecisionLaw.lean](Stats/EpistemicUncertainty/PrecisionLaw.lean)
pushes that process through the literal finite product
`lambda_hat * product(1+epsilon_i)`. Its whole law equals the previously
proved recursive multiplicative scale law. Positive initial precision and
errors in `[0,1)` give an actual positive probability law. The precision's
mean stays `lambda_hat`; its logarithm is an actual measurable pushforward.
For initial precision one and every fixed `0<epsilon<1`,
`P(log(lambda_n)>=0)=P(lambda_n>=1)` tends to zero by the proved
fractional-moment bound on the actual multiplicative population.

[PrecisionCounterexample.lean](Stats/EpistemicUncertainty/PrecisionCounterexample.lean)
constructs the proposed centered Gaussian with variance `n*epsilon^2`.
This sums all n actual error variances, correcting the printed summation
upper index 2 to n. At every positive depth this Gaussian assigns
probability one half to nonnegative values. The absolute difference from
the actual log-precision upper-tail probability tends to one half and
provably does not tend to zero. The concrete signed error `epsilon=1/100`
has actual variance `1/10000`, is bounded in magnitude by `1/100`, and
satisfies all independence and mean assumptions on the same process.

This refutes the printed uncentered asymptotic approximation. A CLT for
the actual centered and normalized log factors remains a separate claim;
so do uniform remainder bounds and the compound-law approximation.

Verification: all 4,099 default-build jobs pass without warnings. The
audit checks 2,302 declarations and 1,970 theorems with zero non-core
axioms. The regenerated index has 214 modules and 1,117 named theorems,
with zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,233 previous indexed
names and types are preserved; 36 declarations are added without
duplicates. The audit imports all 212 other `Stats/` modules. The three
precision modules have 141, 126 and 100 lines; their source assumptions
and the exact scope of the counterexample were checked against local
Section V, Eqs. errorn through lerrornapprox.

### 2026-10-19: signed log remainders and an accumulated-error condition

[LogRemainder.lean](Stats/EpistemicUncertainty/LogRemainder.lean)
replaces Section V's informal first-order log approximation by an explicit
bound valid for either sign of the error. If `|epsilon|<=r<1`, then
`0<=epsilon-log(1+epsilon)<=epsilon^2/(1-r)`. The proof combines both
logarithmic inequalities on the positive domain; it does not use the
incorrect signed quadratic lower bound noted in EU-25.

For any finite family of such errors and positive initial precision,
the difference between `log(lambda_hat)+sum(epsilon_i)` and the actual
product's logarithm lies between zero and
`sum(epsilon_i^2)/(1-r)`. Its absolute error has the same upper bound.
Thus signed cancellation in the errors does not cancel the log remainder.
Negative errors and arbitrary three-coordinate fair-sign configurations
with error magnitude `1/100` satisfy concrete checked examples.

For a triangular array and any positive normalization `a_n`,
`log_multiplicative_error_normalized_remainder_tendsto_zero` proves
that the normalized absolute discrepancy tends to zero if
`sum(epsilon_ni^2)/a_n` tends to zero. A nonzero example with each
depth-n error `1/(2*(n+1))` has vanishing total discrepancy even for
normalization one. These are explicit sufficient rate conditions;
fixed small errors do not automatically satisfy them at a CLT scale,
as the actual iid counterexample already demonstrates.

Verification: all 4,100 default-build jobs pass without warnings. The
audit checks 2,306 declarations and 1,974 theorems with zero non-core
axioms. The regenerated index records 215 modules and 1,121 named
theorems with zero `sorry`, vacuous or placeholder entries. All 27 Python
tests, forbidden-pattern and whitespace checks pass. All 1,269 previous
indexed names and types are preserved, with four additions and no
duplicates; the audit imports all 213 other `Stats/` modules.
The new 151-line module's domain, signed remainder and accumulated rate
condition were reread beside the local Section V approximation.

### 2026-10-19: corrected iid CLT for actual log precision

[LogErrorMoments.lean](Stats/EpistemicUncertainty/LogErrorMoments.lean)
computes the actual expectation and variance of `log(1+epsilon_i)`
under the signed error law, then transfers those integrals to the
infinite iid process. For `0<epsilon<1`, the mean is exactly
`m=log(1-epsilon^2)/2<0`, and the actual variance is
`v=((log(1+epsilon)-log(1-epsilon))/2)^2>0`. These are probability-law
moments, including independently justified integrability, rather than
parameters declared to equal desired formulas.

[PrecisionCLT.lean](Stats/EpistemicUncertainty/PrecisionCLT.lean)
proves a corrected theorem for general iid errors on any probability
space with a uniform a.e. radius `|epsilon_i|<=r<1`. Monotonicity of
the logarithm supplies an actual bound on every log factor, hence L2.
Measurable composition preserves independence and identical distribution.
The iid CLT therefore applies with the actual log-factor mean and
variance. The exact finite log-product identity gives convergence in
distribution of
`(log(lambda_n)-log(lambda_hat)-n*E[log(1+epsilon_0)])/sqrt(n)`
to the genuine centered Gaussian with that log-factor variance.
The proof uses no first-order log approximation and assumes no desired
limit or moment identity.

For the same signed iid product used in the counterexample,
`epistemic_signed_log_precision_CLT` substitutes the proved exact
negative mean `m` and positive variance `v`. Continuous mapping also
proves that the exponential of this centered, normalized log product
converges to the exponential of the Gaussian, an actual lognormal
limit. Initial precision two and errors of magnitude `1/100` witness
all corrected assumptions. The original uncentered approximation remains
false; this corrected limit concerns the explicitly normalized product.

Verification: all 4,147 default-build jobs pass without warnings. The
audit checks 2,320 declarations and 1,988 theorems with zero non-core
axioms. The index has 217 modules and 1,133 named theorems, with zero
`sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,273 previous indexed
names and types are preserved, with 12 additions and no duplicates.
The audit explicitly imports all 215 other `Stats/` modules. The log-moment
and CLT modules have 110 and 179 lines; their actual centering, variance,
normalization and added iid/radius hypotheses were checked against the
local Section V argument.

### 2026-10-19: actual lognormal prior, density and real-order moments

[Lognormal.lean](Stats/Probability/Lognormal.lean) extends the existing
`LognormalMeasure.lognormalReal`, the exponential pushforward of `N(m,v)`.
It is an
independently normalized probability law, supported on positive values,
and applying the logarithm recovers the entire Gaussian measure.
All real powers, including negative ones, are proved L1 using Gaussian
exponential integrability before evaluating their integrals. The actual
moment is `E[X^p]=exp(p*m+v*p^2/2)` for every real p. Natural moments
follow, supplying a probability interpretation of Appendix B's lognormal
raw-moment formula in the kappa paper as well as Section V's inverse
precision moments.

The actual prior has mean `exp(m+v/2)`, inverse mean `exp(-m+v/2)`,
variance `(exp(v)-1)*exp(2*m+v)` and squared coefficient of variation
`exp(v)-1`. L2 is supplied independently before applying the variance
identity. These formulas hold at zero log variance too, where the law
is a point mass.

[LognormalDensity.lean](Stats/Probability/LognormalDensity.lean)
identifies the actual positive-variance prior's Lebesgue density as
`GaussianPDF(m,v,log(x))/x` on `x>0`, and zero elsewhere. The
one-dimensional change-of-variables theorem for `x=exp(z)` proves
Jacobian cancellation inside nonnegative integrals. Applying that
identity to measurable events proves equality of whole measures with
the prescribed density. Its total mass one and a.e. finiteness follow
from the actual probability population. A nonzero variance hypothesis
is explicit for the density theorem, distinguishing the point-mass
boundary. The standard prior `m=0,v=1` supplies concrete witnesses.

Verification: all 4,149 default-build jobs pass without warnings. The
audit checks 2,339 declarations and 2,006 theorems with zero non-core
axioms. The index records 219 modules and 1,149 named theorems with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,285 previous
indexed names and types are preserved, with 17 additions and no
duplicates. The audit explicitly imports all 217 other `Stats/` modules.
The moment and density modules have 131 and 111 lines. Their parameters,
inverse moments, coefficient of variation and positive-variance density
domain were checked against the local Sections V–VI and Appendix B.

### 2026-10-19: actual Normal–Lognormal compound, density and kurtosis

[GaussianMixtureMoments.lean](Stats/Probability/GaussianMixtureMoments.lean)
supplies the general probability bridge for Section V. An independently
integrable scale power and a Gaussian innovation power give L1 of the
actual compound centered power. Their independent product representation
then justifies Fubini and factors the actual moment into the two actual
input moments. The actual mean is the common Gaussian location, the
variance is the actual second scale moment, and the fourth moment about
that location is three times the fourth scale moment. The first moment
needed for variance is derived from L2, not assumed of the output.

[CompoundLaw.lean](Stats/EpistemicUncertainty/CompoundLaw.lean)
constructs an actual lognormal precision draw and maps it to standard
deviation `lambda^(-1/2)`. Positive precision gives conditional variance
`1/lambda`. The prior is independently proper and positive, with every
natural scale power L1 by the proved inverse lognormal moments. An
independent precision draw and standard Gaussian innovation generate
the entire compound law. All actual centered natural powers are L1.

[CompoundDensity.lean](Stats/EpistemicUncertainty/CompoundDensity.lean)
proves the actual law has the prior-averaged Gaussian density, with
total mass one and a.e. finite values. For nonzero log variance it is
exactly the positive Lebesgue integral of the actual lognormal precision
density times `GaussianPDF(mu,1/lambda,x)`. This proves the literal
mixture integral in the first equality of Eq. compound, with the correct
precision-to-variance conversion. The representation against the actual
prior remains valid at zero log variance, when that prior is atomic.
The single combined exponential integrand printed after that equality
has not yet been formally simplified from the product of densities.

[CompoundMoments.lean](Stats/EpistemicUncertainty/CompoundMoments.lean)
computes actual mean `mu`, variance `exp(-m+v/2)` and fourth central
moment `3*exp(-2*m+2*v)`, where `m,v` are the Gaussian log-precision
parameters. Pearson kurtosis is defined from these actual population
moments and variance, then proved equal to `3*exp(v)`. Subtracting
three gives `3*(exp(v)-1)`, the source's displayed value under the
excess convention. A proper standard-log-precision compound formally
refutes that value if it is read as Pearson kurtosis.

Verification: all 4,153 default-build jobs pass without warnings. The
audit checks 2,375 declarations and 2,038 theorems with zero non-core
axioms. The regenerated index records 223 modules and 1,175 named
theorems, with zero `sorry`, vacuous or placeholder entries. All 27
Python tests, forbidden-pattern and whitespace checks pass. All 1,302
previous indexed names and types are preserved, with 32 additions and
no duplicates. The audit explicitly imports all 221 other `Stats/` modules.
The mixture-moment, compound-law, density and moment modules have
121, 123, 107 and 94 lines. Their actual precision law, variance
conversion and kurtosis convention were reread beside the local
Section V equation and its following moment claims.

### 2026-10-19: the source's explicit compound exponential integrand

[CompoundIntegrand.lean](Stats/EpistemicUncertainty/CompoundIntegrand.lean)
completes the second equality of Section V's Eq. compound. A positive
log-precision standard deviation `S` gives its actual Gaussian density
with variance `S^2`; positive precision gives its conditional Gaussian
density in the printed `sqrt(lambda)` parametrization. The product of
the actual lognormal precision density and conditional Gaussian density
is proved pointwise equal to
`exp(-((log(lambda))^2+lambda*S^2*x^2)/(2*S^2))/(2*pi*sqrt(lambda)*S)`.
The proof combines exponential factors, inverse-precision algebra and
the positive square-root identities, retaining both domain hypotheses.

`epistemicNormalLognormalDensity_eq_exp_integral` then proves that
this positive-half-line exponential integral is the density of the
actual compound probability law already constructed. The integration
variable lambda is bound; the resulting source density depends on
`x,S`. This completes the compound law, both density representations,
normalization and corrected moment claims in EU-27. The separate
approximation of this law by a Gamma-precision mixture remains open.

Verification: all 4,154 default-build jobs pass without warnings. The
audit checks 2,386 declarations and 2,049 theorems with zero non-core
axioms. The index records 224 modules and 1,179 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,334 previous
indexed names and types are preserved, with four additions and no
duplicates; the audit imports all 222 other `Stats/` modules.
The new 111-line module's square-root normalization, exponent and
positive parameter domain were checked against the local Eq. compound.

### 2026-10-19: actual Gamma moments and the lognormal precision match

[GammaMoments.lean](Stats/Probability/GammaMoments.lean) evaluates
moments of Mathlib's actual normalized Gamma distribution with shape
`alpha>0` and rate `beta>0`. For each real p with `alpha+p>0`, its
power is independently proved L1 using the positive Euler integral
kernel. The actual expectation is
`beta^(-p)*Gamma(alpha+p)/Gamma(alpha)`. A Lebesgue-a.e. density
identity handles the single boundary point zero before transferring
the integral to the actual Gamma measure. The negative-order example
`alpha=2,beta=3,p=-1` satisfies the genuine integrability hypotheses.

The actual Gamma mean, second moment and variance are
`alpha/beta`, `alpha*(alpha+1)/beta^2` and `alpha/beta^2`.
L2 is derived from the proved power L1 before using the variance
identity. Its actual squared CV is `1/alpha`, and its CV is
`1/sqrt(alpha)`, with positive parameters fixing the square-root sign.
The actual lognormal CV is explicitly proved `sqrt(exp(v)-1)` for every
log location and nonnegative log variance, including the atomic boundary.

[GammaMatch.lean](Stats/EpistemicUncertainty/GammaMatch.lean)
proves that Section VI's parameters
`alpha=1/(exp(v)-1)` and `beta=exp(-v/2)/(exp(v)-1)` are positive
for positive log variance v and define an actual Gamma probability
law. Its actual mean, variance and CV equal those of the actual
`Lognormal(0,v)` prior, using the independently proved moments of
both populations. The source's beta is consistently a rate here.
The checked `v=1` family witnesses all normalization and matching
conditions. No distributional approximation error or stochastic
ordering is inferred from these moment identities.

Verification: all 4,156 default-build jobs pass without warnings. The
audit checks 2,406 declarations and 2,067 theorems with zero non-core
axioms. The index records 226 modules and 1,195 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,338 previous
indexed names and types are preserved, with 18 additions and no
duplicates. The audit explicitly imports all 224 other `Stats/` modules.
The Gamma-moment and matching modules have 178 and 113 lines; the
lognormal moment module has 148. Their moment-order conditions, actual
CV signs and rate-parameter matching were checked against local Section VI.

### 2026-10-19: corrected actual Gamma hazard limit

[GammaTail.lean](Stats/Probability/GammaTail.lean) expresses the actual
Gamma survival as its density integral and proves that it tends to zero
from the actual probability CDF. The unit-shape population has the exact
survival `exp(-beta*x)` and constant hazard beta on `x>=0`. The proper
`Gamma(1,rate=2)` population formally refutes the printed hazard limit
`1/2` under the source's own rate parametrization.

[GammaCalculus.lean](Stats/Probability/GammaCalculus.lean) proves the
actual density derivative `((alpha-1)/x-beta)*density` on positive inputs.
Its L1 follows independently from the Euler kernel. The actual survival
therefore has derivative minus that density by the half-line FTC, and
its value is strictly positive throughout the positive domain.

[GammaHazard.lean](Stats/Probability/GammaHazard.lean) proves
`gammaHazard_tendsto_rate` for every positive shape and rate. The actual
density and actual survival both tend to zero; their derivative ratio
is `beta-(alpha-1)/x`, tending to beta. L'Hopital then gives the limit
of the actual density-to-survival ratio. The source's `1/beta` is the
scale-convention formula and is false with the rate in its printed
density and parameter match. A theorem excludes that reciprocal limit
for every positive rate other than one. Proper shape two, rate three
examples exercise the general result beyond the exponential special case.

Verification: all 4,159 default-build jobs pass without warnings. The
audit checks 2,424 declarations and 2,084 theorems with zero non-core
axioms. The index records 229 modules and 1,211 named theorems with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,356 previous
indexed names and types are preserved, with 17 additions and no
duplicates; the audit imports all 227 other `Stats/` modules.
The tail, calculus and hazard modules have 113, 113 and 84 lines.
Their source rate convention and the actual survival derivative were
checked beside the local Section VI density and hazard displays.

### 2026-10-19: actual lognormal hazard formula and zero limit

[LognormalHazard.lean](Stats/Probability/LognormalHazard.lean) defines
the hazard using the proved density of the actual lognormal measure
and its actual survival probability. Nonzero log variance and positive
input give strictly positive survival. Standardizing the Gaussian log
density and using the actual log-transform law identifies this hazard
with the standard Gaussian Mills ratio times
`z/(sqrt(v)*x)`, where `z=(log(x)-m)/sqrt(v)`.

`lognormalHazard_tendsto_zero` proves the source's zero asymptotic
failure rate for every log location m and nonzero log variance v.
The Gaussian threshold z tends to infinity, the previously proved
actual Gaussian Mills ratio tends to one, and the lognormal scaling
factor tends to zero by `log(x)/x -> 0` and `1/x -> 0`. The argument
uses the actual probability-law ratio throughout.

`lognormalHazard_eq_erfc` separately proves Section VI's literal
displayed formula, with the source's sigma equal to `sqrt(v)`.
Its numerator is `sqrt(2/pi)*exp(-(m-log(x))^2/(2*v))`; its denominator
is `sqrt(v)*x*erfc((log(x)-m)/(sqrt(2)*sqrt(v)))`. The square-root
normalization is proved algebraically, and the erfc denominator is
nonzero by the actual positive survival probability. Proper standard
lognormal populations at thresholds one and e witness the hypotheses.

Verification: all 4,160 default-build jobs pass without warnings. The
audit checks 2,450 declarations and 2,109 theorems with zero non-core
axioms. The index records 230 modules and 1,221 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,373 previous
indexed names and types are preserved, with ten additions and no
duplicates; the audit imports all 228 other `Stats/` modules. The
new module has 200 lines. Its actual survival, nonzero-variance domain,
erfc coefficient and parameter interpretation were checked against
the local Section VI display and limit claim.

### 2026-10-19: actual Gamma exponential moments and tail bound

[GammaMGF.lean](Stats/Probability/GammaMGF.lean) proves independently
that `exp(t*X)` is L1 under every actual Gamma population with positive
shape a and rate r whenever `t<r`. Weighting the genuine density shifts
its Euler kernel's rate to `r-t`; evaluating that integral gives the
actual MGF `(r/(r-t))^a`. A Chernoff bound then controls the actual
survival by `exp(-t*x)*(r/(r-t))^a` for `0<=t<r`.

Every proper Gamma law therefore has a finite strictly positive
exponential moment, taking `t=r/2`. This formally refutes Section VI's
heavy-tail classification under the no-positive-exponential-moment
criterion and supplies the corrected exponential upper bound.
A proper `Gamma(1,rate=2)` counterexample has `E[exp(X)]=2`.
The shape-two, rate-three examples also exercise the general formulas.

Verification: all 4,161 default-build jobs pass without warnings. The
audit checks 2,458 declarations and 2,117 theorems with zero non-core
axioms. The index records 231 modules and 1,229 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,383 previous
indexed names and types are preserved, with eight additions and no
duplicates; the audit imports all 229 other `Stats/` modules.
The new module has 156 lines. Its positive-parameter domain, rate
convention and classification correction were checked against the
local Section VI density and slower-than-exponential claim.

### 2026-10-19: actual incomplete-Gamma survival and rate/scale formulas

[GammaHazardFormula.lean](Stats/Probability/GammaHazardFormula.lean)
derives the genuine Gamma survival
`Gamma(a,r*x)/Gamma(a)` from its actual density by the change of
variables `t=r*x`. Here the numerator is the existing upper
incomplete-Gamma Euler integral. Its positivity follows from the
proved positive survival of a proper unit-rate Gamma population.

The actual hazard in rate parameters is
`r*(r*x)^(a-1)*exp(-r*x)/Gamma(a,r*x)`.
Substituting the explicit scale `b=1/r` proves the source's literal
finite display `exp(-x/b)*(x/b)^(a-1)/(b*Gamma(a,x/b))`.
The reciprocal limiting hazard is valid for this scale b, while the
limit in the source's earlier density convention is the rate r.
Positive shape two, rate three and scale three examples exercise
both actual laws and all parameter conditions.

Verification: all 4,162 default-build jobs pass without warnings. The
audit checks 2,466 declarations and 2,125 theorems with zero non-core
axioms. The index records 232 modules and 1,237 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,391 previous
indexed names and types are preserved, with eight additions and no
duplicates; the audit imports all 230 other `Stats/` modules.
The new module has 150 lines. Its Euler integral, threshold rescaling,
scale prefactor and explicit rate/scale distinction were reread beside
the local Section VI density and hazard displays.

### 2026-10-19: actual Gamma/lognormal survival ratio tends to zero

[GammaLognormalTail.lean](Stats/Probability/GammaLognormalTail.lean)
proves Section VI's tail domination for every proper Gamma law and
every nondegenerate lognormal law, without a moment or CV match.
The actual lognormal survival derivative is obtained from the existing
Black--Scholes pushforward with spot one, identified with the canonical
lognormal probability measure. Both actual tails are strictly positive
at positive thresholds.

The actual survival ratio q has derivative
`(lognormalHazard-gammaHazard)*q`. The proved hazard difference tends
to the positive Gamma rate r, so it eventually exceeds `r/2`.
Consequently `exp(r*x/2)*q(x)` is eventually decreasing, giving
`0<=q(x)<=C*exp(-r*x/2)` and hence `q(x)->0`. A corollary proves
an eventual strict inequality of the actual survival probabilities.
Proper shape-two, rate-three and standard-lognormal examples witness
all parameter and derivative conditions.

Verification: all 4,163 default-build jobs pass without warnings. The
audit checks 2,472 declarations and 2,131 theorems with zero non-core
axioms. The index records 233 modules and 1,242 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,399 previous
indexed names and types are preserved, with five additions and no
duplicates; the audit imports all 231 other `Stats/` modules.
The new module has 156 lines. The actual ratio, continuous-variance
domain, derivative signs and eventual comparison were checked beside
the local Section VI hazard-to-tail argument.

### 2026-10-19: exact actual lognormal exponential-moment domain

[LognormalMGF.lean](Stats/Probability/LognormalMGF.lean) proves that
`exp(-t*x)` divided by actual lognormal survival tends to zero for
every `t>0` and nonzero log variance. This follows by specializing the
proved actual Gamma/lognormal ratio to unit shape, whose actual Gamma
survival is exactly exponential.

A hypothetical L1 positive exponential moment would give a Chernoff
upper bound on the lognormal survival. Dividing that bound by the
positive actual survival would make one at most a quantity tending to
zero, a contradiction. Thus every positive exponential moment fails
for every nondegenerate lognormal population, despite its already
proved finite polynomial moments. Nonpositive arguments are independently
L1 by the bound `exp(t*x)<=1` on the actual positive support.

The zero-log-variance boundary is an actual Dirac measure at `exp(m)`;
all its exponential moments exist and its MGF is `exp(t*exp(m))`.
The exact general integrability criterion is `v=0 or t<=0`, and a
strictly positive exponential moment exists precisely when `v=0`.
Proper standard-lognormal and atomic examples check both domains.

Verification: all 4,164 default-build jobs pass without warnings. The
audit checks 2,481 declarations and 2,140 theorems with zero non-core
axioms. The index records 234 modules and 1,251 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,404 previous
indexed names and types are preserved, with nine additions and no
duplicates; the audit imports all 232 other `Stats/` modules.
The new module has 151 lines. The actual exponential tail comparison,
positive support and nondegenerate-domain correction were reread
beside the local Section VI heavy-tail and finite-moment claims.

### 2026-10-19: actual Normal--Gamma population and integrable moments

[GammaCompoundLaw.lean](Stats/EpistemicUncertainty/GammaCompoundLaw.lean)
constructs Section VI's actual Normal--Gamma mixture from the normalized
Gamma precision law. Gamma precision is strictly positive a.e.; its
inverse square root induces a proper positive dispersion prior.
The Gaussian Markov mixture is therefore a probability measure for
every positive Gamma shape and rate. An independent actual Gamma draw
and standard Gaussian innovation generate the same whole law.

For natural order k with `a>k/2`, the actual dispersion power is
independently L1, and its moment is
`r^(k/2)*Gamma(a-k/2)/Gamma(a)`. The actual compound centered power is
then L1 by the independent Gaussian model; its expectation factors into
that prior moment and the actual standard Gaussian k-th moment, with
Fubini justified by L1. Shape three, rate two and fourth-power examples
witness properness and all moment conditions.

Verification: all 4,165 default-build jobs pass without warnings. The
audit checks 2,495 declarations and 2,152 theorems with zero non-core
axioms. The index records 235 modules and 1,260 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,413 previous
indexed names and types are preserved, with eleven additions and no
duplicates; the audit imports all 233 other `Stats/` modules.
The new module has 168 lines. The independent precision model, inverse
variance transformation, rate convention and sufficient moment-order
condition were reread beside local Eq. compoundGamma. Sharp failure
outside that moment range and the Student density identification remain.

### 2026-10-19: actual normalized Normal--Gamma density integral

[GammaCompoundDensity.lean](Stats/EpistemicUncertainty/GammaCompoundDensity.lean)
identifies the whole actual compound law with its prior-averaged
Gaussian Lebesgue density. Changing from the induced dispersion prior
back to the genuine Gamma precision law gives Eq. compoundGamma's
positive-axis integral of Gamma density times Gaussian density with
variance `1/lambda`. The precision-zero boundary is Lebesgue-null;
all positive inputs have the proved reciprocal-variance interpretation.

The averaged density is measurable, integrates to one and is finite
Lebesgue-a.e., all from the independently proper population construction.
Actual measurable event probabilities are its density integrals, and
the actual compound is absolutely continuous with respect to volume.
The checked shape-one-quarter, rate-two examples show that normalization
requires no finite-outcome-moment condition.

Verification: all 4,166 default-build jobs pass without warnings. The
audit checks 2,505 declarations and 2,161 theorems with zero non-core
axioms. The index records 236 modules and 1,269 named theorems, with
zero `sorry`, vacuous or placeholder entries. All 27 Python tests,
forbidden-pattern and whitespace checks pass. All 1,424 previous
indexed names and types are preserved, with ten additions and no
duplicates; the audit imports all 234 other `Stats/` modules.
The new module has 153 lines. Its actual precision integral, null
boundary, normalized measure equality and positive parameter domain
were reread beside the local Eq. compoundGamma. The Euler evaluation
and identification of the corrected Student scale remain separate.

## Lean upgrade and reproducible verification

### 2026-10-19: dependencies and module compatibility

Lean and Mathlib now use the stable `v4.35.0` releases. `lake update` refreshed
all nine packages in `lake-manifest.json`; the Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The Python checks and notebook now have a reproducible environment in
`python/pyproject.toml` and `python/uv.lock`, including NumPy 2.5.4,
SciPy 1.18.1 and Matplotlib 3.11.2. `./run.py setup` installs that lockfile,
and `./run.py test` runs the repository's existing `kappa.py` tests.
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
| `./run.py audit` | **ok**, 1279 declarations, 1096 theorem declarations, zero non-core axioms |
| Compiled-sorry scanner scope | 1279 declarations, including 534 private declarations |
| Audit imports versus the source tree | All 104 other modules explicitly imported |
| `./run.py index` | **ok**, 105 modules, 593 named theorems, zero sorry/vacuous/placeholder markers |
| `./run.py forbidden` | **ok** |
| `./run.py test` | **ok**, 27 tests, no skips |
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
laws, then identifying the sum distribution. At $α=1$, the existing
theorem only proves an exponential-multiple identity; a rescaled function
identity and the associated sum-law theorem are not assembled.

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

The conclusion follows by division. The unused mean constraint and `a₀`
parameter have been removed; their presence did not establish the mean
or derive the assumed equation.

**Missing:** the actual integral, density normalization and integrability,
boundary decay of $Qf$, integration of the ODE on the half-line, mean
identification and the De Moivre MAD bridge.
The essential analytic step remains a hypothesis.

### K-39. Pearson IV parameters matched to lognormal cumulants — not ok completely

`pearsonIVLognormalMatch` defines explicit candidate coefficients.
Some positivity facts are proved. The $a₁=1$ normalization is a constant
definition with no sample-size or volatility arguments.

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

### K-43. Eq. 17: actual Gaussian-mixture kurtosis — ok

[Kappa/GaussianMixture.lean](Stats/Kappa/GaussianMixture.lean):
`gaussianMixtureKurtosis` is defined by the closed expression.

`gaussianMixtureLaw` constructs the full equal mixture of the actual
Gaussian laws, with arbitrary means and squared real scales. It is a
probability measure with L1 powers about every center. Its actual mean,
variance and fourth central moment are proved. Under nondegeneracy,
`gaussianMixtureLawKurtosis_eq_eq17` identifies their actual Pearson
ratio with the complete four-parameter Eq. 17 expression. Concrete
positive-scale witnesses cover higher and lower kurtosis than three.

**Missing:** nothing for this actual moment identity. It implies no
actual MAD-based kappa calculation, which remains K-45.

### K-44. Actual kurtosis ≥ 3 threshold — ok

`gaussianMixtureKurtosis_ge_three_iff_poly` and
`gaussianMixtureKurtosis_ge_three_iff` prove the stated threshold under
a nondegenerate denominator.

`gaussianMixtureLawKurtosis_ge_three_iff_poly` and
`gaussianMixtureLawKurtosis_ge_three_iff` transfer both thresholds to
actual central moments using K-43. Equal scales with distinct means
give actual kurtosis strictly below three; the means-minus-two/two,
unit-scale population has actual kurtosis `43/25`.

**Missing:** nothing for the actual moment equivalence under the stated
nondegeneracy condition.

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
sensitivity expression. Theorem 2's actual bounded-score moment statement
is proved, without independence. Theorem 1's general regularly varying,
linear-payoff branch is now proved for actual survival laws, including
tail L1 and conditional normalization. The actual standard Gaussian
conditional-mean and density-ratio limits are also proved. Both Theorem 1
implications now follow for the literal operational classes in Definition 4,
with actual density/law identification and L1 conditions. Independent
analytical class identifications and the later distributional and CLT claims
remain incomplete. Some statements in the
source also require correction: Definition 5's unrestricted converse needs
additional hypotheses, and Eq. 8 differentiates a different quantity from
the originally defined payoff gap. Theorem 1 is read with the source's
explicit preceding assumption `g(x)=x`.

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

### BF-04. Definition 4: operational characteristic scale and classes — ok

[CharacteristicScale.lean](Stats/BinaryForecasts/CharacteristicScale.lean)
proves actual Pareto conditional means and their ratio limit;
[ExponentialLaw.lean](Stats/BinaryForecasts/ExponentialLaw.lean) proves
the actual exponential conditional ratio and mean-excess limits.

The general regularly varying actual-survival limit, including its
L1 and probability conditions, is now proved in
[RegularVariationLaw.lean](Stats/BinaryForecasts/RegularVariationLaw.lean).

`HasCharacteristicScale`, `InThinTailClass`, `InFatTailClass` and
`InBorderlineExponentialClass` now encode the literal actual conditional
limits. A nonzero scale implies eventual actual conditional probability,
conditional L1 and population-tail L1. Gaussian, exponential and Pareto
membership theorems provide actual law instances, with concrete witnesses.

**Missing:** nothing for these operational definitions, their well-definedness
on the positive-scale domain and the specified law instances. The broader
analytical class identifications are recorded separately below.

### BF-04a. Identification with independent analytical tail classes — not ok completely

The source also calls D1 thin-tailed and D2 regularly varying, and its
Theorem 1 discussion refers to distributions outside the subexponential
class. A conditional-mean limit predicate does not itself establish all
such equivalences.

**Established:** actual regularly varying survival with index `-alpha`,
`alpha>1`, gives the specified conditional limit; Gaussian and exponential
membership is proved from their actual laws.

**Missing:** formal independent light-tail/subexponential definitions and
the asserted class-wide implications under precise assumptions, and the
converse from an operational D2 limit to survival regular variation.

### BF-05. Strong-Pareto characteristic-scale formula — ok

`characteristicScale_pareto` proves the ratio
$E[X;X>K]/(K P(X>K))=α/(α-1)$ for $α>1$, $l>0$, $K≥l$.
`characteristicScale_pareto_gt_one` proves that the factor exceeds one.
The actual-law theorems `paretoMeasure_cond_mean`,
`paretoMeasure_cond_mean_excess`,
`paretoMeasure_cond_characteristicScale` and its `tendsto` theorem now
establish the corresponding normalized conditional expectations and
limit, with tail positivity, probability normalization and L1 proved.
Pareto(2,3) examples also establish a finite actual second moment;
this conditional-mean classification is not a variance threshold.

**Missing:** nothing for these exact Pareto integral and actual
conditional-law statements on the specified support domain.

### BF-06. Exponential borderline case — actual conditional means and limits proved

`exp_survival_eq`, `exp_tail_expectation_eq` and `exp_conditional_excess`
prove the density-integral formulas for positive rate and nonnegative
threshold. The supported-survival bridge and its below-support
counterexample remain in
[ExponentialLaw.lean](Stats/BinaryForecasts/ExponentialLaw.lean).

`expMeasure_tail_mean` and `expMeasure_tail_integrable_id` now establish
the actual supported first tail moment and L1 condition.
`expMeasure_cond_probability`, `expMeasure_cond_integrable_id`,
`expMeasure_cond_mean` and `expMeasure_cond_mean_excess` establish the
normalized actual conditional law, its L1 observation, mean `K+1/r`
and mean excess `1/r`.

`expMeasure_cond_mean_excess_tendsto` proves the positive limiting mean
excess. `expMeasure_cond_characteristicScale_tendsto` proves the actual
conditional-mean ratio tends to one. Rate-two, threshold-three examples
satisfy all hypotheses under a genuine exponential population.

**Missing:** nothing for these exact exponential-law expectations and
operational limits. General distribution-class predicates and their
class-wide implications are separate claims in BF-04 and BF-10.

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

### BF-09. Fixed-density converse — refuted; corrected converse and strict gap proved

`conflation_fixed_density_counterexample` formally refutes the unrestricted
fixed-density only-if reading of Definition 5. A smooth nonnegative payoff,
`g(x)=(x-2)^2`, gives equal positive integrals under the actual supported
Exp(1) PDF at `K=1`, while varying at points of positive density. Its actual
tail expectation and L1 property are proved.

`tailPayoff_eq_binary_iff_ae_eq` proves the corrected actual-law converse:
under tail L1 and the one-sided bound `g>=g(K)` almost everywhere, equality
holds exactly for an almost-everywhere constant payoff under the measured
tail law. This explicitly replaces the unrestricted pointwise conclusion.

`tailPayoff_strict_gap_iff` proves that strict payoff excess on a set of
positive actual tail probability is exactly the criterion for a strict
gap under that bound. `tailPayoff_strict_gap` gives the strict-a.e.,
positive-tail special case. Actual Exp(1) constant and linear payoffs
instantiate all hypothesis families.

**Missing:** nothing for this fixed-density refutation and specified
corrected actual-law statements. A universal identity over all possible
densities has different quantifiers; pointwise constancy outside the
measured support is not claimed.

### BF-10. Theorem 1: linear-payoff convergence under Definition 4 — ok

The source explicitly assumes $g(x)=x$ immediately before Theorem 1
(line 351). Its limit is the characteristic scale of Definition 4.
The previous version of this review overlooked that sentence and
incorrectly treated the theorem as an unrestricted-payoff assertion.

The general RV branch is now assembled in BF-12, for the actual survival
and conditional laws as well as the density `I1/I2` expression.
The actual standard Gaussian limit is proved in BF-14.

`thinTail_I1_div_I2_tendsto` and `fatTail_I1_div_I2_tendsto` now prove
both named implications for the source's actual operational classes.
They identify the written nonnegative measurable density with its actual
finite law and derive eventual tail normalization, conditional L1 and
population-tail L1. The transfer from the actual conditional-mean ratio
to the written density ratio matches the source's **From Eq. chscale**
proof. Actual Exp(2) and supported Pareto(2,3) PDFs satisfy every hypothesis.

**Missing:** nothing for this named theorem with its stated operational
classes and linear payoff. Independent analytical class identifications
remain in BF-04a. An extension to arbitrary payoffs needs more hypotheses:
for an Exp(1) density and $g(x)=exp(x/2)$, at $K≥0$,
$I₁=2exp(-K/2)$ and $I₂=exp(-K/2)$, so their ratio is two.
The underlying law has characteristic scale one. This example is an
analytic check of that broader extension; it neither refutes the source's
linear-payoff theorem nor constitutes a new Lean theorem.

### BF-11. Theorem 1's strong-Pareto, linear-payoff specialization — ok

`pareto_I1_div_I2_eq` proves the exact ratio for $g(x)=x$.
`pareto_I1_div_I2_tendsto` proves the corresponding `Tendsto` statement.
The actual normalized-law ratio and limit are independently identified
by the `paretoMeasure_cond_characteristicScale` theorems in BF-05.

**Missing:** nothing for this specialization. For a payoff $x^p$, the factor
instead depends on $p$; it cannot be assigned the linear-payoff factor without
an additional argument.

### BF-12. Theorem 1's general RV, linear-payoff branch — ok

`regularlyVarying_survival_tailMean_ratio_tendsto` and
`regularlyVarying_survival_condMean_ratio_tendsto` start from regular
variation of the actual survival of a finite measure, with index
`-alpha` and `alpha>1`. They prove the limit `alpha/(alpha-1)>1`.
Eventual tail positivity, measurability, the slowly varying factor,
actual upper-tail L1, conditional normalization and conditional L1 are
derived. No full-law first moment is needed on the lower tail.

`regularlyVarying_density_I1_div_I2_tendsto` proves the printed density
ratio for a nonnegative measurable density explicitly identified with
that actual law. The generic layer-cake first-moment bridge supplies the
missing term `K*P(X>K)` before applying Karamata. All hypotheses have
actual Pareto(2,3) witnesses, including its supported normalized PDF.

**Missing:** nothing for this branch on the specified domain and linear
payoff. Both integration thresholds use the same `K`, correcting the
printed `K`/`K_p` mismatch. An arbitrary payoff or rate claim would
require further hypotheses.

### BF-13. Eq. 6: Gaussian truncated first moment — ok

`gaussian_I1_id_eq` proves
$∫_K^∞ xφ(x)dx=φ(K)$ for $K≥0$.
`stdNormal_tail_mean` now identifies the actual Gaussian-law first
tail moment with `phi(K)` for every finite real threshold, with its
actual L1 condition proved.
[SigmaClosures.lean](Stats/BinaryForecasts/SigmaClosures.lean) also proves
`integral_x_gaussianPDF_σ` and `integral_gaussianPDF_σ` for positive $σ$:
the tail first moment is $σφ(K/σ)$ and the tail probability is $1-Φ(K/σ)$.

**Missing:** nothing for the stated integral formulas.

### BF-14. Standard Gaussian I₁/I₂ limit and operational characteristic scale — ok

`stdNormal_survival_mills_tendsto` proves `Q(K)/(phi(K)/K)->1` using
L'Hopital's rule, and `stdNormal_characteristicScale_tendsto` proves
`phi(K)/(K*Q(K))->1`. Here `Q` is the actual standard Gaussian survival.

`stdNormal_cond_probability`, `stdNormal_cond_integrable_id`,
`stdNormal_tail_mean` and `stdNormal_cond_mean` identify the actual
normalized conditional law, L1 observation and mean `phi(K)/Q(K)`.
The actual tail-ratio, conditional-mean ratio and written density
`I1/I2` limits are then proved to equal one. The source explicitly uses
the centered normalized Gaussian in this example.

**Missing:** nothing for this population's linear-payoff limit and
operational characteristic-scale property. The general class-predicate
interface remains separately recorded in BF-04/BF-10.

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

For the corrected Gaussian linear-payoff gap, BF-20 proves actual
normalization, L1, both derivatives and strict convexity. The actual
two-point scale model is now proved as well: `gaussianScaleMixture` is
the actual law of an independent standard Gaussian multiplied by a
scale taking two values with equal probability. Its observation is L1,
its actual survival and first tail moment are computed, and its actual
payoff gap equals the mean of the component actual gaps. For distinct
positive scales and positive threshold, the actual mixture gap is
strictly greater than the Gaussian gap at the actual mean scale.
The same law now has proved actual variance, fourth central moment and
Pearson kurtosis strictly above three when its positive scales differ.
The baseline Gaussian's actual kurtosis is proved to be three.

**Missing:** arbitrary mixing distributions and other distribution
families, with integrability and the corresponding actual-law Jensen
bridge. General higher-kurtosis comparisons require their own actual
moment calculations, hypotheses and proofs beyond this two-point model.

### BF-19. Eq. 8: displayed Gaussian derivative expression — ok for A − B

Let $A(σ)=σφ(K/σ)$ and $B(σ)=1-Φ(K/σ)$.
[SigmaSensitivity.lean](Stats/BinaryForecasts/SigmaSensitivity.lean):
`gaussianEq8_sigmaSensitivity_eq_phi` and
`gaussianEq8_sigmaSensitivity_eq` prove the derivative calculation giving
$φ(K/σ)((K-1)K³-(K-2)Kσ²)/σ⁵$.

**Missing:** nothing for the derivative of the displayed $A-B$ expression.
The integral closures are proved separately in BF-13.

### BF-20. Corrected actual Gaussian I₁ − I₂ sensitivity — ok

For the linear payoff, the definition gives $I₂=K B$, whereas the proof in the
source and the existing Gaussian derivative module subtract $B$.

`gaussianScaleLaw` is now the actual normalized `N(0,sigma^2)` law,
constructed as a standard-Gaussian pushforward. Its L1 observation and
actual tail moments are proved. `gaussianPayoffGap` is the actual gap
`A-K*B`, also identified with the actual restricted excess expectation
and with the original density `I1-I2` on `sigma>0`, `K>=0`.

`gaussianPayoffGap_hasDerivAt` and
`gaussianPayoffGap_deriv_hasDerivAt` prove the corrected first and second
derivatives `phi(K/sigma)` and `K^2*phi(K/sigma)/sigma^3`.
Corresponding derivatives of the written density gap are proved as well.
The second derivative is positive for positive threshold and scale;
strict convexity and a strict two-scale Jensen inequality follow.
Actual scale-five, threshold-three certificates and the scales-three/seven
comparison satisfy all hypotheses.

**Missing:** nothing for this corrected Gaussian sensitivity and specified
functional comparison. It is not a literal formalization of the printed
`A-B` expression. The arbitrary stochastic-parameter and mixture-law
claims remain in BF-18.

### BF-21. Eq. 8's universal positivity — false; formal counterexample proved

`gaussian_eq8_polynomial_pos` proves positivity at $σ=1$.

`gaussianEq8_negative_at_three_five` proves the exact printed expression
is strictly negative at `K=3`, `sigma=5`, where its numerator is `-21`.
`gaussianEq8_not_always_positive` formally refutes universal positivity
over positive thresholds and scales. The existing derivative certificate
also supplies an actual negative derivative value of its checked
first-derivative expression at those parameters.

**Missing:** nothing for this literal refutation. The unit-scale
polynomial result remains valid. The corrected `A-K*B` payoff-gap
sensitivity is a separate statement in BF-20.

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

### BF-31. Appendix B: probability integral transform — ok for a continuous actual CDF

`probabilityIntegralTransform` now proves that a measurable observation's
actual CDF transform has the uniform law, represented by Lebesgue measure
restricted to `(0,1)`. The theorem uses the CDF of the observation's actual
pushforward law and requires its continuity, as the source does.

`exists_cdf_sublevel_boundary` implements the generalized-inverse step
without assuming strict monotonicity; `cdfTransform_probability_le`
proves the actual unit-interval sublevel probabilities, including zero.
Actual exponential-law and nonconstant product-coordinate examples
satisfy the hypotheses.

**Missing:** nothing for this continuous-CDF transform. An arbitrary Beta
forecast model and its joint law with outcomes are separate claims in BF-32.

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

**Paper verdict: not ok.** The actual finite recursive constant-error
Gaussian mixture, its whole-law binomial collapse, normalized density and
corrected exceedance formula, first four outcome moments, symmetry and
kurtosis are proved.
The explicit independent fair sign-vector construction, its general
varying-error Gaussian mixture and normalized density are also proved.
Finite conditional Markov hierarchies and their actual iterated Gaussian
densities are proved, including construction from normalized positive-parent
conditional density inputs and their literal repeated density products.
Infinite constructions and higher-moment limits, the CLT
argument and the Normal–Gamma compound law remain open. Actual
finite-population variance, fourth central moment and kurtosis divergence
are proved. The actual constant-error laws have the proved unscaled
point-mass weak limit at their common mean.
This source has no active numbered Theorem or Proposition environment; both
numbered Remarks and the mathematical claims are audited below.

### EU-01. Remark 1: collapse the branching scenarios — ok for the finite fair model

`epistemicSignLaw` is the actual uniform measure on all `Fin n -> Bool`
sign vectors. Every vector has probability `2^(-n)`; the whole space equals
the product of genuine fair Boolean laws, every coordinate has the fair
marginal, and the coordinates are mutually independent.
`epistemicSignScale` is the source's multiplicative dispersion function.

`epistemicLayerScaleLaw_eq_sign_map` identifies the actual recursive
varying-error dispersion with this explicit sign-vector pushforward.
`epistemicSignLaw_outcome_model` proves that independently sampling this
sign vector and a standard Gaussian under `mu+scale*z` generates exactly
the actual varying-error outcome law.
`epistemicLayerBranchLaw_eq_sign_mixture` gives its `2^n` genuine Gaussian
components. `epistemicLayerBranchLaw_eq_signDensity` proves their actual
normalized density. Positivity of every standard deviation follows from
positive base scale and errors in `[0,1)`.

Constant errors recover the previous actual populations as whole measures,
including their genuine Binomial count representations and Gaussian mixtures.
The general finite varying-error populations have actual dispersion moments,
variance and fourth central moment products as well.

**Missing:** nothing for this explicit finite fair-branch construction.
The general finite conditional Markov hierarchy and its literal normalized
positive-parent density-input specialization are also proved in EU-03.
The source's displayed matrix/vector row mismatch is corrected in EU-04.

### EU-02. Remark 2: uncertainty around a zero probability implies a positive floor — not ok

No probability-estimation or posterior model is defined.

**Missing:** a precise model of estimation error and a justified lower bound.
A symmetric error of one percentage point around zero cannot itself be a
probability-valued error model with both signs. An uncertain estimate alone
does not imply a universal strictly positive lower bound on the true
probability.

### EU-03. Section II: actual repeated conditional density integration — corrected

`epistemicGaussianScaleKernel` now constructs the genuine measurable
Gaussian conditional law and proves it is a Markov kernel.
`epistemicGaussianMixtureLaw` is the actual marginal for any dispersion
prior and is normalized whenever the prior is a probability measure.
`epistemicGaussianMixtureLaw_outcome_model` identifies the whole law with
independent prior/standard-Gaussian sampling under `mu+scale*z`.
It recovers the actual varying-error population for its genuine scale prior.

For every probability prior concentrated on positive scales,
`epistemicGaussianMixtureLaw_eq_withDensity` proves Eq. 1's actual marginal
density is the prior integral of the true Gaussian density. Joint
measurability justifies Tonelli. The density is measurable, integrates
to one and is finite Lebesgue-a.e.; pointwise finiteness at every outcome
is not assumed. Actual event probabilities equal its density integrals.
Proper Dirac and varying-error dispersion priors witness the hypotheses.

`epistemicScaleHierarchy` now constructs the actual repeated conditional
scale law from an arbitrary proper prior and measurable Markov transitions.
Its normalization is independently proved. Positive support propagates
through every transition from the positive prior.
`epistemicScaleHierarchy_lintegral` proves genuine integration under that
hierarchy equals the complete iterated conditional integral for any
measurable nonnegative test function.
`epistemicHierarchyOutcomeLaw_eq_withDensity` proves the actual Gaussian
population has the resulting iterated density; its mass is one, it is
measurable and finite Lebesgue-a.e., and actual event probabilities equal
its density integrals. A genuine scale-dependent fair transition supplies
proper witnesses, including an explicit two-transition integral.

The source's multi-layer display uses fixed `phi(x;mu,sigma)` where the
Gaussian must depend on the sampled observation scale `hat sigma_1`.
The corrected kernel model orders transitions from outer uncertainty
toward that observation scale and records each conditional dependency.

`epistemicDensityScaleKernel` now constructs each actual conditional
kernel directly from its prescribed nonnegative density on the positive
half-line. Joint measurability and conditional mass one give the actual
Markov law; positive scale support follows from absolute continuity.
A positive hyperprior is likewise constructed from its input density.
`epistemicHierarchyIntegral_density_inputs` turns every conditional kernel
integral into the source's literal positive-half-line density-weighted
integrals; the two-layer theorem explicitly gives `f_0*f_1*GaussianPDF`.

`epistemicPositiveDensityHierarchyLaw_eq_withDensity` needs normalization
only at positive parent scales, as in the source. Global kernels are built
by extending invalid nonpositive parents, and positive-domain integral
congruence proves the final formula retains the original `f_i` exactly.
`epistemicPositiveDensityHierarchyPDF_lintegral` proves total mass one;
the original density is measurable and finite Lebesgue-a.e. A continuous
parent-dependent unit-interval conditional density and continuous prior
witness the assumptions. Another witness is zero at nonpositive parents,
so the source-domain theorem does not assume global normalization.

**Missing:** nothing for this corrected finite conditional-density
construction, with joint measurability explicit and the Gaussian depending
on the sampled observation scale. Infinite-depth laws and additional
moment/tail claims remain separate.

### EU-04. Section II: actual 2ⁿ-component Gaussian density — corrected

`epistemicLayerBranchLaw_eq_sign_mixture` derives Eq. gn's actual fair
Gaussian mixture from the genuine varying-error recursion. Its scales are
the source products over all sign vectors, with weight `2^(-n)`.
`epistemicLayerBranchLaw_eq_signDensity` proves its Lebesgue density is
`epistemicSignDensity` for positive base scale and all finite errors in
`[0,1)`. Every component scale is independently proved positive.
The density is nonnegative, measurable and L1; its real and nonnegative
integrals both equal one. `epistemicLayerBranchLaw_real_eq_signDensity`
identifies every measurable event probability with its actual density
integral. Constant-error binomial density identities are also proved.

The printed example matrix T starts with all plus signs, while its
following vector M^3 and M_1^3 start with all minus signs. They reverse
the rows despite the displayed definition `M_i=prod_j(1+epsilon_j*T_ij)`.
`epistemic_sign_matrix_first_row_counterexample` follows that definition:
with all three errors one-half, the first row has multiplier `27/8`,
whereas the printed M_1^3 gives `1/8`. Reversing both row orderings
consistently preserves the sum; Eq. gn's density itself is proved.

**Missing:** nothing for the actual fair finite density on the positive-scale
domain, with the source's row illustration corrected as above.

### EU-05. Section III: actual constant-error collapse to binomial weights — ok

`epistemicScaleLaw_integral_binomial` derives the actual binomial-weighted
expectation of every real-valued dispersion test function by recursive
mixture integration and Pascal's identity.

`epistemicScaleLaw_eq_binomial` identifies the actual recursive
dispersion measure with the genuine Binomial(n,1/2) count pushforward
through the printed scale function. The whole-law conclusion uses
all bounded continuous test functions, rather than a few moment values.
`epistemicBranchLaw_eq_binomial_mixture` proves the actual Gaussian
population is the corresponding binomial-weighted sum of genuine
Gaussian measures. Concrete depth-two positive-scale witnesses include
an actual middle-scale probability of one-half.

**Missing:** nothing for the actual constant-error measure collapse.
Its positive-scale density identity and the general finite fair sign-vector
construction are also proved in EU-04 and EU-01.

### EU-06. Actual natural-order dispersion moment — ok for the finite constant-error law

`epistemicSigmaMoment_eq` proves, for all natural $n,k$,
$epistemicSigmaMoment(n,k,σ,ε)=σ^k M_k(ε)^n$, where
$M_k(ε)=((1+ε)^k+(1-ε)^k)/2$.

`epistemicScaleLaw_moment` now proves the same value for the actual
dispersion expectation, with independent actual-law L1 at every order.
`epistemicScaleLaw_moment_eq_sigmaMoment` identifies the genuine moment
with the earlier weighted expression. The actual dispersion has mean
`sigma` and is positive a.e. on the source's standard-deviation domain.

**Missing:** nothing for the actual natural-order dispersion moments of
this finite constant-error model. The actual Binomial whole-law
representation is proved in EU-05.

### EU-07. Second- and fourth-order layer factors — ok

`epistemicMomentFactor_two` and `epistemicMomentFactor_four` prove
$M₂=1+ε²$ and $M₄=1+6ε²+ε⁴$.

**Missing:** nothing for these polynomial identities.

### EU-08. Actual dispersion second and fourth moments — ok for the finite constant-error law

`epistemicVariance_eq` and `epistemicSigmaFourthMoment_eq` prove
the weighted second/fourth powers of the scale.

`epistemicBranchLaw_variance_eq_scaleMoment` now identifies the second
scale sum with the actual outcome variance. Three times the fourth
scale sum is proved to be the actual fourth central outcome moment.

`epistemicScaleLaw_moment_eq_sigmaMoment` identifies both scale sums
with genuine moments of the actual dispersion law, which independently
generates the recursive outcome population with a standard Gaussian.

**Missing:** nothing for these actual dispersion/outcome identities.
The actual Binomial whole-law representation is proved in EU-05.

### EU-09. First raw outcome moment and preservation of μ — ok for the finite recursive law

The source states $E[X]=μ$ for the mixture.

`epistemicBranchLaw_mean` proves the actual expectation is `mu` at
every finite depth. The population is normalized and its observation
is independently proved L1.

**Missing:** nothing for this finite constant-error population.

### EU-10. Actual second raw outcome moment and variance — ok for the finite recursive law

The source gives $E[X²]=μ²+σ²(1+ε²)^n$ and
$Var(X)=σ²(1+ε²)^n$.

`epistemicBranchLaw_moment_two` and `epistemicBranchLaw_variance` now
prove these actual-law equalities. The actual variance is identified
with the earlier weighted dispersion second moment.

**Missing:** nothing for the finite constant-error population.

### EU-11. Actual third raw outcome moment and zero skewness — ok for the finite recursive law

The source gives $E[X³]=μ³+3μσ²(1+ε²)^n$ and zero skewness.

`epistemicBranchLaw_moment_three` proves the actual raw moment.
The actual third central moment vanishes; the standardized ratio is
zero. `epistemicBranchLaw_variance_pos` supplies positive actual
variance when `sigma` is nonzero. Full reflection symmetry is EU-13.

**Missing:** nothing on this finite nondegenerate constant-error domain.

### EU-12. Fourth raw outcome moment — false as printed; corrected actual theorem proved

The source prints $3μ⁴$ as the leading term.

`epistemicBranchLaw_moment_four` proves the corrected actual formula
with leading `mu^4` and all remaining terms retained. The proper
one-layer model with `mu=sigma=1`, `epsilon=1/2` has actual fourth
raw moment `259/16`, whereas the printed expression gives `291/16`.
`epistemicBranchLaw_fourth_source_counterexample` formally certifies
the discrepancy. Actual fourth-power L1 is proved independently.

**Missing:** nothing for the corrected finite recursive-law theorem
and literal refutation. The source's erroneous expression is not proved.

### EU-13. Actual symmetry of the outcome distribution — ok for the finite recursive law

The source states that layering scale uncertainty preserves symmetry.

`epistemicBranchLaw_reflection` proves that the actual population's
pushforward under `x -> 2*mu-x` equals the same actual measure at
every finite depth. A nondegenerate depth-two example verifies it.

**Missing:** nothing for this finite constant-error population.

### EU-14. Actual raw- and excess-kurtosis expressions — ok for the finite recursive law

`epistemicKurtosis_eq` and `epistemicExcessKurtosis_eq` prove
$3(1+6ε²+ε⁴)^n/(1+ε²)^{2n}$ and that quantity minus three, assuming $σ≠0$.

`epistemicBranchLawKurtosis_eq` now identifies this expression with the
ratio of actual central moments. `epistemicBranchLawKurtosis_closed`
and `epistemicBranchLaw_excessKurtosis` prove the stated actual raw
and excess formulas, with positive actual variance for `sigma!=0`.

**Missing:** nothing for this finite constant-error population.

### EU-15. Actual kurtosis at least three, and strictly greater with uncertainty — ok for the finite recursive law

`epistemicMomentFactor_four_ge_two_sq`,
`epistemicMomentFactor_four_strict`,
`epistemicKurtosis_ge_three`, `epistemicKurtosis_gt_three` and
`epistemicExcessKurtosis_nonneg` prove the inequalities.
Strictness requires $n≥1$, $σ≠0$ and $ε≠0$.

`epistemicBranchLawKurtosis_ge_three` and
`epistemicBranchLawKurtosis_gt_three` prove these inequalities for
the actual normalized recursive population, using its actual moments.
The one-layer positive-scale, half-error model has actual kurtosis
`123/25>3` and positive actual variance.

**Missing:** nothing for these actual finite-population inequalities.
A kurtosis inequality does not establish a regularly varying tail.

### EU-16. Actual variance and kurtosis divergence as n → ∞ — ok with nonzero scale and uncertainty

`epistemicBranchLaw_variance_tendsto_atTop` and
`epistemicBranchLaw_centralMoment_four_tendsto_atTop` prove divergence
of the actual finite-population variance and fourth central moment.
`epistemicBranchLawKurtosis_geometric` identifies the actual Pearson
ratio with `3*(B/A^2)^n`, whose base exceeds one for nonzero error.
`epistemicBranchLawKurtosis_tendsto_atTop` and
`epistemicBranchLaw_excessKurtosis_tendsto_atTop` prove both actual
kurtosis divergences. All use `sigma!=0` and `epsilon!=0`.

Zero-error certificates prove constant actual variance and kurtosis,
clarifying the needed hypotheses. Concrete unit-scale, half-error
populations witness every divergence statement.

**Missing:** nothing for these limits of finite-population moments.
An infinite-depth law or tail-class claim is separate in EU-17.

### EU-17. Power-law tail generation — not ok as stated; unscaled point-mass weak limit proved

The module proves growing moment expressions.
For the actual dispersion law, `epistemicScaleLaw_moment_rpow` now
proves the real-order moment formula. For `0<p<1` and nonzero error
in `(0,1)`, `epistemicScaleLaw_fractional_moment_tendsto_zero` proves
these actual fractional moments tend to zero, while the actual first
dispersion moment stays fixed. A limit-law argument must account for
this behavior as well as the growing outcome variance and kurtosis.

`epistemicScaleLaw_tail_tendsto_zero` and
`epistemicScaleProba_tendsto_dirac` now prove concentration and weak
convergence of the actual dispersion laws to `Dirac(0)`.
`epistemicOutcomeProba_tendsto_dirac` uses the independent Gaussian
product model to prove the actual unscaled outcomes converge weakly
to `Dirac(mu)` for fixed `sigma>0`, `epsilon in (0,1)` and common mean.
`epistemicOutcomeProba_weak_limit_unique` formally identifies every
weak limit with this point mass. The same actual sequence's variance
is proved to diverge. Thus a different nondegenerate power-law weak
limit on this fixed-parameter, unscaled domain is excluded.

**Missing:** a precise mathematical interpretation and proof for the
source's graphical tail-shape assertion, any moving-threshold or
rescaled limit, and a formal finite-depth tail-class statement.
Growing kurtosis alone does not establish regular variation.

### EU-18. Constant-error exceedance formula and numerical tables — not ok

The source gives a weighted erfc sum and ratios to a baseline Gaussian.

`epistemicBranchLaw_real_eq_integral_density` proves the actual
mixture survival integral on the positive-scale constant-error domain.
`epistemicBranchLaw_real_Ici_binomial` proves the genuine exceedance is
the binomial-weighted Gaussian-tail sum.
`epistemicBranchLaw_real_Ici_erfc` proves the corrected actual erfc sum
with `K-mu`, and `epistemicBranchLaw_real_Ici_erfc_zero_mean` gives the
literally printed formula for `mu=0`. `erfc_eq_one_sub_integral` identifies
the CDF-defined erfc with the source's actual integral definition by
Gaussian differentiation and the fundamental theorem of calculus.

The uncentered formula for general mean is false:
`epistemic_uncentered_exceedance_counterexample` uses the actual N(1,1)
law at threshold one. Its exceedance is one-half, strictly above the
printed uncentered probability. The corrected formula preserves all
source probabilities on its intended zero-mean domain. An actual
finite-depth mean-one mixture also exceeds its mean with probability
one-half.

**Missing:** certified numerical table values/error bounds and verification
of which error parameter belongs to each printed table. The corrected
analytic exceedance formula and its integral-erfc interpretation are proved.

### EU-19. Section IV: actual decaying-error variance product — corrected

`epistemicLayerBranchLaw_variance` derives the genuine varying-error
population variance as `sigma^2 * prod_{i<n}(1+epsilon_i^2)` by actual
mixture integration, independent L1 and the actual mean.
`epistemicLayerBranchLaw_variance_decaying` identifies the geometrically
decaying case with the earlier `decayingErrorVariance` expression.
This is now an actual-law equality, beyond a directly defined scalar product.
The law is independently proved normalized and generated by an actual
random dispersion and independent standard Gaussian.

Source index `i=0` corresponds to its first error `epsilon_1`, so the
sequence is `epsilon_1*kappa^i`. The prose `epsilon_n=kappa^n*epsilon_1`
needs exponent `n-1`. The displayed q-Pochhammer expression also conflicts
with the source's own plus-sign definition of `[a;q]_n`.
`epistemic_decaying_pochhammer_sign_counterexample` proves the actual
one-layer variance is 5/4 while the literal negative-argument, plus-sign
convention gives 3/4. The variance product is proved as displayed; using
the usual minus-sign Pochhammer convention repairs that notation.

**Missing:** nothing for the actual recursive-law variance product with
these source notation/index corrections. The actual independent sign-vector
product space and its whole-law representation are proved in EU-01.

### EU-20. Actual decaying-error variance exceeds the base and increases with depth — ok

`decayingErrorVariance_ge_base` and `decayingErrorVariance_mono`
prove the finite-product inequalities. Their actual-law bridges
`epistemicLayerBranchLaw_variance_decaying_ge_base` and
`epistemicLayerBranchLaw_variance_decaying_monotone` now transfer both
claims to genuine outcome population variances. Nonzero base scale
also gives positive actual variance at every finite varying-error depth.

**Missing:** nothing for these actual finite-population comparisons.

### EU-21. Actual decaying-error fourth central moment — ok

`epistemicLayerBranchLaw_momentAbout_four` computes the actual varying-error
fourth moment about every center. At the actual mean,
`epistemicLayerBranchLaw_centralMoment_four_decaying` proves the printed
`3*sigma^4*prod_{i<n}(1+6*epsilon_1^2*kappa^(2*i)+epsilon_1^4*kappa^(4*i))`.
All integrated powers are independently L1 under genuine Gaussian mixtures.
A proper depth-two population with different errors one-half and one-quarter
has actual variance `85/16` and fourth central moment `43419/256`.

**Missing:** nothing for the finite varying-error fourth central moment.

### EU-22. Capped moments and convergence for decaying errors — not ok fully

The actual finite-population variance and fourth central moments equal
the source products. For `0<=kappa<1`,
`epistemicLayerBranchLaw_variance_decaying_le` bounds every actual variance
by `sigma^2*exp(epsilon_1^2/(1-kappa^2))`.
`epistemicLayerBranchLaw_centralMoment_four_decaying_le` bounds every actual
fourth central moment by
`3*sigma^4*exp(6*epsilon_1^2/(1-kappa^2)+epsilon_1^4/(1-kappa^4))`.

The actual moment sequences are monotone in depth, and
`epistemicLayerBranchLaw_variance_decaying_converges` and
`epistemicLayerBranchLaw_centralMoment_four_decaying_converges` prove
finite real limits between the base Gaussian moments and these caps.
These are limits of actual moments, without assuming an infinite law
or interchanging expectation and a weak limit.
`epistemicLayerScaleLaw_ae_pos_decaying` gives genuine positive dispersion
at every finite depth for the source parameters.
`epistemicLayerBranchLaw_variance_kappa_one_diverges` verifies that
`kappa=1` with nonzero error is the nondecaying case, with unbounded
actual variance; the closed interval alone does not ensure decay.

**Missing:** the all-orders higher-moment extension, an actual infinite-depth
law with justified moment convergence to that law, and certified numerical
coefficients 1.23 and 9.88. A joint limit `kappa->1`, `epsilon->0` also
requires control of their relative rates.

### EU-23. Section V: exact log-additivity — ok

`log_multiplicative_error` proves
$log(λ̂∏(1+ε_i))=log(λ̂)+Σlog(1+ε_i)$ for positive $λ̂$ and factors.

**Missing:** nothing for this finite algebraic identity.

### EU-24. Upper bound log(1 + ε) ≤ ε — ok

`log_one_add_le_self` proves the inequality for $ε>-1$.

**Missing:** nothing for the upper bound.

### EU-25. Log linearization and accumulated error — ok with explicit rate conditions

The source replaces each log factor by its first-order error.
`log_one_add_remainder_bounds` proves, for `|epsilon|<=r<1`,
`0<=epsilon-log(1+epsilon)<=epsilon^2/(1-r)` for both signs.
`log_multiplicative_error_remainder_bounds` and its absolute-error
corollary bound the entire finite product's discrepancy by
`sum(epsilon_i^2)/(1-r)`. All positive-factor hypotheses follow from
the explicit radius bound.

`log_multiplicative_error_normalized_remainder_tendsto_zero` proves
normalized approximation under the sufficient condition
`sum(epsilon_ni^2)/a_n -> 0`, for a positive normalization and a uniform
radius below one. Nonzero shrinking errors `1/(2*(n+1))` give a checked
example with normalization one. The earlier suggested lower bound
$ε-ε²/2≤log(1+ε)$ for signed errors is not used; it fails for negative
errors near zero.

**Missing:** nothing for these quantitative deterministic bounds. They
do not supply the extra rate condition for arbitrary errors in the paper;
the proposed fixed-error uncentered CLT is formally refuted in EU-26.

### EU-26. CLT and lognormal precision law — false as printed; corrected iid CLT ok

The source appeals to independent errors with finite variances bounded below.

`epistemicPrecisionGaussianTailGap_tendsto_half` and
`epistemicPrecisionGaussianTailGap_not_tendsto_zero` refute the proposed
uncentered Gaussian approximation under a genuine infinite iid process.
Each error is a fair signed `epsilon`, with actual mean zero, finite second
moment and variance `epsilon^2`. For every fixed `0<epsilon<1`, including
`1/100`, the actual log-precision upper-tail probability at zero tends to
zero, whereas the proposed `N(0,n*epsilon^2)` probability is always one half
at positive depths. Their discrepancy tends to one half. The actual
product's whole law and positive support are proved before taking this limit.

`epistemic_log_precision_CLT` proves the corrected theorem for iid errors
uniformly bounded in magnitude by `r<1`. The log factors are proved L2.
The actual log precision is centered by the initial log precision plus
`n*E[log(1+epsilon_0)]` and normalized by `sqrt(n)`; it converges in
distribution to a centered Gaussian with the actual log-factor variance.
For the signed iid model, `epistemic_signed_log_precision_CLT` gives the
explicit strictly negative mean `log(1-epsilon^2)/2` and strictly positive
variance `((log(1+epsilon)-log(1-epsilon))/2)^2`.
`epistemic_signed_precision_normalized_lognormal_CLT` proves a genuine
lognormal limit for the exponential of that centered, normalized log.

**Missing:** nothing for the printed-claim counterexample or the corrected
bounded-iid theorem. Extending the corrected theorem to independent,
nonidentically distributed errors would need Lindeberg/Lyapunov conditions;
finite variances bounded below alone do not guarantee such a CLT.
Zero mean of the errors does not center their logarithms, and an
unnormalized sum of growing variance does not have a fixed normal limit.
EU-25's separate linearization theorem requires its accumulated-error
condition before an approximation argument can be used.

### EU-27. Normal–Lognormal mixture and moments — ok with kurtosis convention corrected

The actual precision prior `LognormalMeasure.lognormalReal m v` is now constructed, with
positive support, whole-measure Gaussian log transform, and every real
power L1. Its actual moments are `exp(p*m+v*p^2/2)`, including inverse
moments. `LognormalMeasure.lognormalReal_eq_withDensity` proves the literal positive
lognormal density and its normalization for nonzero log variance.
`epistemicNormalLognormalLaw` is the actual compound probability measure,
generated by independent lognormal precision and Gaussian innovation.
Positive precision gives conditional Gaussian variance `1/lambda`.
Every actual centered natural power is proved L1 before evaluating
moments. `epistemicNormalLognormalLaw_eq_withDensity` identifies the
whole law's normalized density; for nonzero log variance,
`epistemicNormalLognormalDensity_eq_lintegral` proves the literal
positive integral of the two source densities.

Actual mean, variance and fourth central moment are `mu`,
`exp(-m+v/2)` and `3*exp(-2*m+2*v)`. The actual Pearson kurtosis is
`3*exp(v)`, and excess is `3*(exp(v)-1)`. A formal proper-law
counterexample excludes the source's displayed value under the
Pearson convention. These are compound-population moments, distinct
from the constant-error finite-sum model.

`epistemic_compound_density_product` proves that the product of the
actual densities equals the single combined exponential integrand in
Eq. compound. `epistemicNormalLognormalDensity_eq_exp_integral` gives
the resulting actual density integral for the source's `S>0` domain.

**Missing:** nothing for the actual mixture, its density representations,
normalization or corrected moments. The later Gamma approximation is
a separate distributional claim.

### EU-28. Gamma/Lognormal moment and CV matching — ok as exact moment identities

The source matches Gamma shape/rate to a lognormal precision law.

The actual lognormal prior has the proved mean `exp(m+v/2)`, variance
`(exp(v)-1)*exp(2*m+v)` and squared coefficient of variation `exp(v)-1`.

`gammaMeasure_integrable_rpow` and `gammaMeasure_moment_rpow` prove
actual Gamma power L1 and moments for positive shape/rate and
`alpha+p>0`. The actual mean, variance and CV are `alpha/beta`,
`alpha/beta^2` and `1/sqrt(alpha)`.

`epistemicGammaMatch_probability` proves the source's matched shape
and rate give a proper population for `v>0`.
`epistemicGammaMatch_mean`, `_variance` and `_cv` prove that its actual
mean, variance and coefficient of variation equal those of the actual
`Lognormal(0,v)` prior, with both input moment families proved separately.

**Missing:** nothing for exact first-two-moment and CV matching.
Equality of these moments supplies no distributional approximation
error bound; that is a separate claim in EU-30.

### EU-29. Gamma and Lognormal tail/hazard comparison — not ok

`gammaHazard` is the actual Gamma density divided by its actual
population survival. `gammaMeasure_survival_hasDerivAt` and
`gammaPDFReal_hasDerivAt` prove the required calculus from the actual
density representation and its independently established L1.
`gammaHazard_tendsto_rate` proves the corrected Gamma hazard limit
beta for every positive shape and rate. The survival denominator is
strictly positive at every positive threshold.

`gamma_rate_hazard_counterexample` uses a proper shape-one, rate-two
population to refute the printed reciprocal limit; the stronger
`gammaHazard_not_tendsto_inverse_rate` excludes it for all positive
rates other than one. The exact unit-shape survival is exponential.

`LognormalMeasure.lognormalHazard` uses the actual normalized lognormal
law and its proved density. Its displayed erfc formula is proved by
`lognormalHazard_eq_erfc`; its denominator is strictly positive on the
positive continuous domain. `lognormalHazard_tendsto_zero` proves the
zero limit using the actual Gaussian Mills ratio and the vanishing
logarithmic scaling factor, for every log location and nonzero log
variance.

`gammaMeasure_integrable_exp_mul` and `mgf_gammaMeasure` prove finite
positive exponential moments and the actual MGF `(beta/(beta-t))^alpha`
for every `t<beta`. `gammaMeasure_survival_le_exp` supplies an actual
exponential tail upper bound. The universal positive exponential moment
and a proper `Gamma(1,rate=2)` counterexample formally refute the
source's heavy-tail classification under the standard no-positive-
exponential-moment criterion. The density's beta is consistently a rate.

`gammaMeasure_survival_eq_incompleteGamma` derives the actual survival
`Gamma(alpha,beta*x)/Gamma(alpha)` by scaling the genuine Euler tail
integral. `gammaHazard_eq_incompleteGamma` proves the corresponding
rate formula. `gammaHazard_scale_eq_incompleteGamma` recovers the
source's literal finite display for the actual rate `1/b`, making
its scale b explicit. `gammaHazard_scale_tendsto_inverse` proves
the reciprocal limit for that scale convention.

`gamma_lognormal_tail_ratio_tendsto_zero` proves that the ratio of
the actual Gamma survival to actual lognormal survival tends to zero,
for every positive Gamma shape/rate and nonzero lognormal log variance.
The derivative of the ratio is the hazard difference times the ratio;
an exponentially weighted ratio is eventually decreasing.
`eventually_gamma_survival_lt_lognormal` gives an eventual strict
tail-probability inequality. This statement concerns right tails and
does not establish the global or outcome-mixture ordering in EU-30.

`LognormalMeasure.lognormalReal_exponential_tail_ratio_tendsto_zero`
proves the actual lognormal survival dominates every decreasing
exponential tail. `lognormalReal_not_integrable_exp_mul` proves that
every strictly positive exponential moment fails for nonzero log
variance. The exact integrability domain is `v=0 or t<=0`; the atomic
zero-variance case admits all exponential moments. This completes the
Gamma/lognormal heavy-tail distinction under that criterion.

**Missing:** their maximum-domain claims.

### EU-30. Gamma as a lower bound for Lognormal, then for the outcome mixture — not ok

The source uses a same-CV Gamma approximation to support conclusions about
the lognormal mixture.

**Missing:** specify the order or error metric, prove the precision-law
comparison and prove that the mixing operation preserves the desired outcome
comparison. Matching mean/CV or comparing right tails of precision is
insufficient: large outcome values also depend on behavior near zero
precision.

### EU-31. Section VI: evaluate the Normal–Gamma compound integral — not ok

`epistemicNormalGammaLaw` is now the actual Gaussian Markov mixture
with the proper Gamma precision prior mapped by inverse square root.
`epistemicNormalGammaLaw_probability` proves properness for all positive
shape and rate. `epistemicNormalGammaLaw_outcome_model` identifies the
whole law with an independent Gamma precision and Gaussian innovation.
Centered powers are independently L1 for `alpha>k/2`; their actual
moments factor into the evaluated Gamma inverse moment and Gaussian
moment by justified Fubini.

`epistemicNormalGammaLaw_eq_withDensity` now proves the actual normalized
Lebesgue density representation. `epistemicNormalGammaDensity_eq_lintegral`
identifies it with the positive-precision integral in Eq. compoundGamma.
Its integral is one, it is measurable and finite a.e., and the whole
compound measure is absolutely continuous for every positive shape/rate.

**Missing:** explicit Euler evaluation of that density integral and its
identification with the correctly scaled Student probability measure.
Sharp nonintegrability outside the proved moment range also remains.
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

**Paper verdict: not ok.** The strong-Pareto tail-moment integral, actual
finite iid maximum law, actual hidden-mass CDF and its expectation are
proved. The general-p hidden moment now has a genuine scaled-Beta
pushforward, exact Gamma-ratio expectation and its printed leading
asymptotic. The zeroth hidden moment has the supported Beta(1,n) CDF and mean
`1/(n+1)`; the printed exact exponential law is formally refuted.
The actual finite-mean arithmetic sample mean is unbiased, and the
source's necessary-underestimation claim is formally refuted for every
nonempty Pareto sample. General-p Proposition 1, limit theorems and the
Gaussian comparison remain incomplete. The source's Fréchet substitution requires a precise
approximation or asymptotic statement.

### HM-01. Visible-plus-hidden moment decomposition — ok for the exact Pareto model

The source splits the population moment at the random sample maximum.

`paretoSample_moment_decomposition` splits the actual population moment
at the actual observed maximum for positive scale/index and `p<α`.
The population power's integrability, sample-function measurability and
integrability, and the expected decomposition are proved. The visible and
hidden density expressions are identified with the actual measure integrals.

**Missing:** nothing for this finite-sample exact-Pareto decomposition.
An asymptotic-tail model remains a separate extension.

### HM-02. Eq. 2: strong-Pareto p-th tail moment — ok

`paretoTailMoment_eq` proves
$∫_K^∞ x^p αl^αx^{-α-1}dx=αl^αK^{p-α}/(α-p)$
for $l>0$, $α>0$, $p<α$, $K≥l$.

**Missing:** nothing for this exact integral. It is not merely a rearrangement
of a supplied closed expression. `paretoMeasure_tailMoment_eq` additionally
identifies the result as a true truncated expectation under the supported
Pareto law, with a separate population-integrability theorem.

### HM-03. Zeroth and first tail-moment specializations — ok

`paretoTailMoment_at_zero` identifies the survival function.
`paretoTailMoment_at_one` identifies the first tail expectation.

**Missing:** nothing for these specializations. The source's introductory
$L^{-α}$ survival coefficient and later $L^α$ scale formulas need a
consistent scale convention before combining its displayed statements
literally.

### HM-04. Exact iid sample-maximum CDF — ok

`paretoSampleMaximum_cdf` in
[Maximum.lean](Stats/HiddenMoments/Maximum.lean) proves the CDF of the
actual coordinate maximum under the actual Pareto product sample law.
For positive scale/index and nonempty samples it equals
$(1-(l/k)^α)^n$ above the scale and zero below it.

**Missing:** nothing for this exact finite-sample probability statement.
The earlier scalar expression remains available as its supported branch.

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

HM-04 supplies the actual exact maximum law.

The actual general-p hidden moment is now a measurable integrable random
variable, with Eq. 2 proved at the actual random maximum almost surely.
`paretoHiddenMoment_map_beta_rpow` proves its genuine law as a scaled
power pushforward of the normalized Beta(1,n) measure.

**Missing:** the explicit density and its Jacobian/support calculation,
and a justified Fréchet approximation for the printed density. The exact
pushforward and its actual expectation are now proved.

### HM-07. Remark 1: sample survival ratio is exponential — not ok literally

For a finite continuous iid sample, the remaining survival mass at its
maximum is supported in $[0,1]$. An ordinary exponential distribution has
positive mass above one.

`paretoHiddenMass_not_exponential` now proves the actual finite-sample
pushforward differs from Exp(n). `paretoHiddenMass_cdf` and
`paretoSampleSurvivalRatio_cdf` prove the corrected supported Beta(1,n) CDF.

**Missing:** nothing for that finite-sample correction and refutation.
The scaled exponential weak limit is now proved in HM-12; the source's
unscaled exponential expression comes from the Fréchet substitution.

### HM-08. Beta CDF and its maximum-CDF substitution — ok

`paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF` proves the substitution
between the two defined real functions. The candidate ratio CDF is
$1-(1-y)^n$.

`paretoHiddenMass_cdf` now establishes the actual probability statement
under the true product sample law, including both support branches.
`paretoSampleSurvivalRatio_cdf` transfers it to the explicit ratio by an
almost-sure equality.

**Missing:** nothing for these CDF identities. The global actual CDF uses
the supported extension, rather than the polynomial outside `[0,1]`.

### HM-09. Derivative of the candidate CDF — ok

`paretoSampleSurvivalRatioPDF_eq_deriv` proves the derivative
$n(1-y)^{n-1}$.

`betaPDFReal_one_nat_eq` supplies the normalized supported density, and
`paretoHiddenMass_map_beta` identifies it with the actual hidden-mass law.

**Missing:** nothing for the polynomial derivative and its supported
finite-sample density interpretation.

### HM-10. Actual hidden-mass mean 1/(n+1) — ok

`paretoSampleSurvivalRatio_mean` proves
$∫₀¹ y n(1-y)^{n-1}dy=1/(n+1)$ for $n≥1$.

`paretoHiddenMass_mean` additionally proves the expectation of the actual
population hidden mass under the actual iid sample law. Measurability,
boundedness, integrability and the almost-sure Pareto-ratio identification
are proved, rather than assumed.

**Missing:** nothing for the actual zeroth hidden-moment expectation.

### HM-11. Difference between 1/n and 1/(n+1) — ok algebraically

`paretoSampleSurvivalRatio_mean_asymptotic_gap` proves
$1/n-1/(n+1)=1/(n(n+1))$.

**Missing:** nothing for the equality. An explicit big-O estimate for this
scalar difference is not stated. The actual scaled distributional limit
is now proved separately in HM-12.

### HM-12. Scaled sample-survival ratio converges to Exp(1) — ok

`scaledHiddenMassLaw_tendsto` now proves full weak convergence of the
actual scaled hidden-mass pushforwards to Mathlib's actual Exp(1)
probability measure. The positive sample sizes are indexed by `n+1`.
`scaledHiddenMassLaw_cdf_tendsto` proves the actual CDF convergence at
every real threshold, and `probabilityMeasure_tendsto_of_cdf` supplies
the proved bridge to the weak topology.

The result holds for every probability population with continuous CDF.
`paretoScaledHiddenMassLaw_tendsto` specializes it to every positive
strong-Pareto scale and tail index; continuity is proved, not supplied
without a witness. Actual exponential and infinite-mean Pareto examples
check the hypotheses.

**Missing:** nothing for this corrected scaled exponential weak limit.
The exact finite-sample unscaled exponential assertion remains false.

### HM-13. Expected general-p hidden moment — corrected exact mean and asymptotic proved

The source gives the Fréchet-model expression
$l^p n^{p/α-1}Γ(1-p/α)$; it is not the exact finite-sample expectation.

For the actual strong-Pareto product sample with `l>0`, `α>0`, `p<α` and
`n>0`, `paretoHiddenMoment_mean_gamma` now proves the exact expectation
$l^p Γ(r)Γ(n+1)/Γ(n+1+r)$, where $r=1-p/α>0$.
The hidden-moment random variable, L1 property, Beta pushforward law and
Gamma evaluation are all proved from the population measure and actual
sample coordinates.

`paretoHiddenMoment_mean_scaled_tendsto` proves the scaled expectation
limit. `paretoHiddenMoment_mean_ratio_tendsto` proves its ratio to the
printed expression tends to one. Thus the printed expression has a
precise asymptotic interpretation for the exact strong-Pareto model.

**Missing:** nothing for this corrected exact-Pareto expectation and
asymptotic. A general regularly varying population or an exact Fréchet
maximum model would require separate assumptions and law calculations.

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

### HM-17. Distribution independence of hidden probability mass — ok for continuous CDFs

The source emphasizes that the $p=0$ result does not depend on tail thickness.

`continuousHiddenMass_map_beta` now proves the actual hidden-mass law is
Beta(1,n) for every probability population with a continuous CDF and every
nonempty finite iid sample. `sampleMaximum_cdf_transform` and
`continuousHiddenMass_tail_ge` prove the corresponding actual probability
statements, and `continuousHiddenMass_mean` gives expectation `1/(n+1)`.
The sample law is an actual independent product; the variable is an actual
population tail probability. Exp(1) supplies non-Pareto witnesses.

**Missing:** nothing for this continuous-CDF extension. The exact
finite-sample exponential claim remains false, and atomic populations
require a different formulation.

### HM-18. Higher-moment numerical comparisons and convergence claims — not ok

The source plots hidden moments and compares Pareto and Gaussian behavior.

**Missing:** formal quantitative bounds for the compared expectations and
rates, or certified numerical integrations. The existing deterministic
Pareto formula does not validate all sample-size plots.

### HM-19. Necessary sample-mean underestimation — false literally; correction proved

The conclusion's statement about the actual sample mean is too strong.

`sampleMean` is the actual observed arithmetic average, proved measurable,
integrable and unbiased under a finite population first moment.
`paretoSampleMean_unbiased` proves its actual expectation, and
`paretoSampleMean_upper_tail_lower` proves a strictly positive overshoot
probability for every nonempty finite iid Pareto sample with `l>0`, `α>1`.
The threshold is the actual finite population mean.

`paretoSampleMean_not_always_below_mean` refutes the literal claim.
For Pareto(1,2) at size one, the actual overshoot probability is `1/4`;
at size two, it is at least `1/16` while the mean remains two.

`paretoSample_visibleMoment_lt_population` now proves the corrected
truncated-population-integral statement, almost surely under the actual
finite iid sample law. The two sample quantities are explicitly distinguished.

**Missing:** nothing for the finite-mean unbiasedness, refutation and
corrected population-truncation statement. Confidence bounds and the
decision models of HM-20 remain separate.

### HM-20. Confidence about the size of the unseen and risk applications — not ok

The module provides deterministic tail-moment expressions and the actual
finite-sample law and mean of the zeroth hidden moment.

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
`paretoMeasure_integrable_id_iff` now additionally proves that the actual
identity random variable under the supported Pareto probability measure
is integrable exactly when `1<α`, for positive scale/index. The density
integrability conclusion is therefore connected to the genuine law.

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

The actual strong-Pareto moment threshold is proved in SP-08, and the
finite iid product sample is constructed.

**Missing:** the applicable LLN/nonconvergence theorem, a
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
| Binary Forecasts | Theorem 1, line 353: convergence of I₁/I₂ | **ok** with its Definition 4 classes | BF-10–BF-14; both operational class implications, actual density/law and L1 bridges, general RV branch and standard Gaussian case; independent analytical class identifications remain BF-04a |
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
   Branching Gaussian mixtures and remaining actual iid-sum laws. The measurable Brier average
   and its moment integrability are now proved.
   These are the most common missing links between proved algebra and paper
   theorems.
3. **Replace proxy asymptotics with results for the paper's quantities.**
   Keep the genuine lognormal Loulakis limit separate from the small-$σ$
   cumulant and large-$σ$ surrogate formulas. Derive limits for the same
   distributional object whose finite-$n$ behavior is being discussed.
4. **Correct literal source formulas before formalizing them.**
   The Gaussian payoff gap and finite-sample hidden-mass law now have
   proved corrections. The put ratio, noncentered fourth moment and
   Gaussian hidden-mass evaluation still need their source-to-law repairs.
   Impossible statements should be replaced by explicit corrected
   propositions, with their scope recorded.
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
