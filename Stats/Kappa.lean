module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  Headline definition (paper Eq. 1).  For an iid sample `X_1, …, X_n` with
  finite mean, let `M(n) := E[|S_n − E[S_n]|]` be the mean absolute
  deviation (MAD) of the partial sum `S_n := X_1 + ⋯ + X_n`.  Define
      κ(n₀, n) := 2 − log(n/n₀) / log(M(n)/M(n₀)).

  Intuition: κ = 0 for Gaussian (where `M(n) ∝ √n`), κ = 1 for Cauchy
  (`M(n) ∝ n`), κ ∈ (0, 1) for unimodal fat-tailed distributions with
  finite mean.  Operational metric for the rate of convergence under the
  law of large numbers — for a Pareto with tail index `α ∈ (1, 2)`,
  κ asymptotes to `2 − α > 0`.

  Umbrella module — the formalisation is split into submodules:

  * `Stats.Kappa.Basic` — abstract κ-definition and stable-basin
    invariance, Gaussian/Cauchy specialisations, `n_ν` sample-size
    translation (Eq. 7), and the κ additive decomposition (Eq. 2).
  * `Stats.Kappa.Exponential` — exponential / Gamma closed form
    (Eq. 15, 16) and Stirling-based asymptotic (Appendix C).
  * `Stats.Kappa.CubicStudent` — cubic Student T (α = 3) closed form
    (Eq. 9, 10) and the Loulakis identity (Appendix A) for the upper
    incomplete Gamma.
  * `Stats.Kappa.CubicStudentAsymptotic` — Stirling/Laplace asymptotic
    `log(n) · κ_{1, n} → log(π²/4)`.
  * `Stats.Kappa.CubicStudentLaplace` — DCT-based proof of
    `incompleteGamma_laplace_asymptotic` (the Laplace asymptotic of
    `Γ(n+1, n)`, formerly an axiom).
  * `Stats.Kappa.CubicStudentExpIntegral` — PDF of the cubic-Student
    sum (paper Eq. 11, Appendix A) via the complex negative-index
    exponential integral `E_{−n}(z) := ∫_1^∞ t^n · e^(−z·t) dt`.
    Reduces to two integration axioms (Fourier-inversion cosine split
    and substitution `u = 1 + √3 ω`) plus an algebraic factorisation.
  * `Stats.Kappa.Cumulant` — General cumulant API:
    `K_i(X) := iteratedDeriv i (cgf X μ) 0`, with `K_0 = 0`,
    `K_1 = mean`, `K_2 = Var`, `K_i(Σ_N X_i) = N · K_i(Y)` for iid
    sums, plus `cumulantSkewness` and `cumulantKurtosis` (and their
    `centralMoment`-ratio equivalents).
  * `Stats.Kappa.Lognormal` — Loulakis' abstract lower bound: under a
    subexponentiality-style assumption `M(n)/M(1) ≥ n`, one obtains
    `κ_{1,n} ≥ 1`.
  * `Stats.Kappa.LognormalCumulants` — closed-form lognormal cumulants
    (paper Appendix B): `K_1^n`–`K_4^n`, skewness, kurtosis, and the
    σ → 0 / n → ∞ cumulant-proxy limits.
  * `Stats.Kappa.GaussianMixture` — Gaussian-mixture kurtosis (Eq. 17)
    and the P-class linkage to `Stats.Theorem1`.
  * `Stats.Kappa.GaussianSwitchingMean` — equal-variance Gaussian
    switching-mean closed-form κ₁ (Eq. 18) and the algebraic
    negative-κ sign criterion.
  * `Stats.Kappa.TableI` — closed-form κ₁ for Student T, Pareto,
    Normal-with-switching-variance, and lognormal (paper Table I
    rows 1, 3, 4, 5).
  * `Stats.Kappa.PearsonIV` — Pearson IV approximation (paper
    Section IV-B-3): ODE-based class definition, MAD closed form
    (Eq. 13), and the explicit lognormal-matched coefficients
    (paper Eq. 12 "box of formulas").
  * `Stats.Kappa.Stable` — α-stable distribution infrastructure
    (paper Section IV-A, Eq. 4): characteristic function, class
    predicate, ϕ(t)^n identity, sum-of-stable closure, and
    κ_{n₀, n} = 2 − ᾱ stable-class invariance.
  * `Stats.Kappa.PoissonCDF` — Poisson CDF at the mean → 1/2
    (todo3.md C.3, route (b)): combines the Loulakis identity, the
    Laplace asymptotic for `Γ(n+1, n)` (C.1), and Mathlib's Stirling.
  * `Stats.Kappa.IIdTriangle` — iid triangle inequality `M(n) ≤ n·M(1)`
    from first principles (todo5.md Phase A): closes the structural
    shell of `kappa_upper_bound_subadditive` via `IdentDistrib`-based
    transport of integrability and `Finset.abs_sum_le_sum_abs`.
  * `Stats.Kappa.LognormalMeasure` — lognormal as a probability measure
    (todo5.md Phase B.1–B.4): push-forward of `gaussianReal` under
    `Real.exp`; tail formula `ℙ(X > x) = 1 − Φ((log x − μ)/√v)`.
    Infrastructure for the Loulakis subexponentiality argument.
  * `Stats.Kappa.MaxIIdBound` — Loulakis inclusion-exclusion lower bound
    on the iid max event (todo5.md Phase C.1): `ℙ(max X_i > t) ≥
    n·ℙ(X_0 > t) − (n choose 2)·ℙ(X_0 > t)²`.  Pure combinatorial
    probability (Bernoulli + induction); no distribution-specific
    assumption.
  * `Stats.Kappa.SumMaxBound` — trivial bound `ℙ(S_n > t) ≥ ℙ(max X_i > t)`
    for non-negative iid `X` (todo5.md Phase C.2).
  * `Stats.Kappa.MadLayerCake` — MAD layer-cake identity (todo5.md Phase B.6):
    `𝔼|X − m| = 2 · ∫_{t > 0} ℙ(X > m + t) dt` when `𝔼X = m`.
    Ascending layer cake on `(X − m)⁺` doubled via the symmetric form
    `𝔼(X − m)⁺ = 𝔼(m − X)⁺`.
  * `Stats.Kappa.LognormalMarkov` — Hölder/Markov bound on the lognormal
    tail (todo5.md Phase B.5): `ℙ(Y > t) ≤ t^(−γ) · exp(γμ + γ²v/2)`,
    via Chernoff (`measure_ge_le_exp_mul_mgf`) + Gaussian mgf
    (`mgf_id_gaussianReal`).  At `μ = −v/2`, exponent becomes
    `γ(γ−1)v/2 < 0` for `γ ∈ (0, 1)` — the σ→∞ decay that drives the
    Loulakis second-order term to zero.
  * `Stats.Kappa.LoulakisAlgebraic` — algebraic Loulakis lower bound
    (todo5.md Phase C.3a): for nonneg iid `X : Fin n → Ω → ℝ` with
    representative law `Y₀` of mean `m`,
        `M(n) ≥ 2 · (n · ∫_{t>0} ℙ(Y₀ > nm + t) dt
                    − C(n,2) · ∫_{t>0} ℙ(Y₀ > nm + t)² dt)`.
    Combines B.6 (layer cake) + C.2 (sum ≥ max) + C.1 (incl-excl).
    Pure algebra, no `σ→∞` limit.
  * `Stats.Kappa.LognormalAsymptotic` — σ→∞ asymptotic of `M(1)`
    (todo5.md Phase B.7): with the σ-parametrised
    `Y σ ω := exp(σω − σ²/2)` on `(ℝ, gaussianReal 0 1)`,
    `M(1; σ) = ∫|Y σ − 1| → 2` as `σ → ∞`.  Proof: pointwise
    `Y σ ω → 0` (exponent → -∞), DCT on `min(Y σ, 1)`, mean condition
    `𝔼Y σ = 1`.
  * `Stats.Kappa.LoulakisLiminf` — Loulakis main asymptotic
    `liminf σ→∞ M(n;σ)/M(1;σ) ≥ n` (todo5.md Phase C.3b).  Abstract
    statement combining the algebraic Loulakis bound (C.3a) with the
    σ→∞ asymptotics (B.7 for `M(1) → 2`, B.5 for Hölder decay of the
    `∫ ℙ²` second-order term) via `Filter.liminf`.
  * `Stats.Kappa.LognormalIIdSetup` — n-fold iid lognormal construction
    on `(Fin n → ℝ, Measure.pi (gaussianReal 0 1))` (todo6.md Phase 6.1).
  * `Stats.Kappa.LognormalTailIntegrals` — `An σ → 1` (todo6.md
    Phase 6.2) + Hölder bound + `ℙ_σ(Y > c) → 0` (Phase 6.3 partial).
  * `Stats.Kappa.LoulakisLognormal` — lognormal-specialised Loulakis
    liminf `liminf σ→∞ M(n; σ)/M(1; σ) ≥ n` (todo6.md Phase 6.4 wire-up),
    parameterised over the Bn → 0 hypothesis pending the integration
    follow-up.
-/
public import Stats.Kappa.Basic
public import Stats.Kappa.Exponential
public import Stats.Kappa.CubicStudent
public import Stats.Kappa.CubicStudentAsymptotic
public import Stats.Kappa.CubicStudentLaplace
public import Stats.Kappa.CubicStudentExpIntegral
public import Stats.Kappa.Cumulant
public import Stats.Kappa.Lognormal
public import Stats.Kappa.LognormalCumulants
public import Stats.Kappa.GaussianMixture
public import Stats.Kappa.GaussianSwitchingMean
public import Stats.Kappa.TableI
public import Stats.Kappa.PearsonIV
public import Stats.Kappa.Stable
public import Stats.Kappa.PoissonCDF
public import Stats.Kappa.IIdTriangle
public import Stats.Kappa.LognormalMeasure
public import Stats.Kappa.MaxIIdBound
public import Stats.Kappa.SumMaxBound
public import Stats.Kappa.MadLayerCake
public import Stats.Kappa.LognormalMarkov
public import Stats.Kappa.LoulakisAlgebraic
public import Stats.Kappa.LognormalAsymptotic
public import Stats.Kappa.LoulakisLiminf
public import Stats.Kappa.LognormalIIdSetup
public import Stats.Kappa.LognormalTailIntegrals
public import Stats.Kappa.LoulakisLognormal

@[expose] public section
