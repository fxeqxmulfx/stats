module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need? A Pre-asymptotic Metric for Fat-tailedness",
    arXiv:1802.05495v3, Definition 1 and Sections III–IV.

  For actual iid sums with a finite mean, the paper uses the MAD
      M(n) = E|S_n - E S_n|,
  then κ(n₀,n) = 2 - log(n/n₀) / log(M(n)/M(n₀)).
  `Stats.Kappa.Basic` instead takes a supplied real function M. Its
  square-root and linear reference-curve identities do not establish
  the MAD law of a random sum. In particular, Cauchy laws do not have
  the finite mean required by Definition 1.

  This umbrella exposes:
    * Basic: abstract κ algebra, reference curves, sample-size power
      expressions and corrected positive-index decompositions.
    * Exponential, CubicStudent, TableI and Pareto: supplied special-law
      MAD expressions, finite-Beta integrals and special-function analysis.
      The actual iid-sum MAD identifications remain separate.
    * CubicStudentAsymptotic, CubicStudentLaplace, CubicStudentExpIntegral
      and PoissonCDF: incomplete-Gamma, Fourier-integral and asymptotic
      results for the defined functions, with no extra axioms.
    * Cumulant: actual CGF derivatives and the hypotheses needed for
      cumulant identities. LognormalCumulants: candidate closed cumulants
      and excess-kurtosis proxy limits.
    * GaussianMixture and GaussianSwitchingMean: candidate moment/MAD
      expressions and their algebraic inequalities; mixture-law bridges
      remain open.
    * PearsonIV: a differentiability/ODE predicate, conditional IBP
      algebra and candidate coefficients. Normalization, mean, actual
      cumulant matching and the density's MAD remain open.
    * Stable: explicit function formulas and conditional power identities.
      Probability-law existence, iid-sum identification and actual MAD
      scaling are not established by these function predicates.
    * IIdTriangle, LognormalMeasure, MaxIIdBound, SumMaxBound and
      MadLayerCake: genuine probability and integrability infrastructure.
    * LognormalMarkov, LognormalAsymptotic, LognormalIIdSetup,
      LognormalTailIntegrals, LoulakisAlgebraic, LoulakisLiminf and
      LoulakisLognormal: the actual Gaussian-product construction and
      completed large-volatility Loulakis limit for every fixed n ≥ 2.
    * Lognormal: additional conditional abstract κ bounds.

  REVIEW.md, K-01–K-47, records exact paper correspondence and the
  remaining probability-law and approximation gaps.
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
