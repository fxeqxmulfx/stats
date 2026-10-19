module

/-
  Audit every declaration originating in Stats modules, including private
  declarations, for transitive dependence on non-standard axioms.
  Run: lake build Stats.AxiomAudit
  Keep the `import all` list exhaustive when adding Stats source modules;
  these imports include their private declarations under the module system.
-/
import all Stats
import all Stats.Arbitrage
import all Stats.BinaryForecasts
import all Stats.BinaryForecasts.Bernoulli
import all Stats.BinaryForecasts.Brier
import all Stats.BinaryForecasts.CharacteristicScale
import all Stats.BinaryForecasts.Conflation
import all Stats.BinaryForecasts.Exponential
import all Stats.BinaryForecasts.ParetoSensitivity
import all Stats.BinaryForecasts.SigmaClosures
import all Stats.BinaryForecasts.SigmaSensitivity
import all Stats.BlackScholes
import all Stats.BlackScholes.CallPrice
import all Stats.BlackScholes.Erfc
import all Stats.BlackScholes.Greeks
import all Stats.BlackScholes.PutCall
import all Stats.BlackScholes.ReturnsSmile
import all Stats.BlackScholes.ReturnsSmileExamples
import all Stats.BlackScholes.Smile
import all Stats.BlackScholes.StdNormal
import all Stats.BlackScholes.StrictButterfly
import all Stats.BlackScholes.Survival
import all Stats.Calculus
import all Stats.Calculus.CallPrice
import all Stats.Calculus.Greeks
import all Stats.Calculus.PutShadow
import all Stats.CarrMadan
import all Stats.Copula.Basic
import all Stats.EpistemicUncertainty
import all Stats.Hedging
import all Stats.HiddenMoments
import all Stats.Kappa
import all Stats.Kappa.Basic
import all Stats.Kappa.CubicStudent
import all Stats.Kappa.CubicStudentAsymptotic
import all Stats.Kappa.CubicStudentExpIntegral
import all Stats.Kappa.CubicStudentLaplace
import all Stats.Kappa.Cumulant
import all Stats.Kappa.Exponential
import all Stats.Kappa.GaussianMixture
import all Stats.Kappa.GaussianSwitchingMean
import all Stats.Kappa.IIdTriangle
import all Stats.Kappa.Lognormal
import all Stats.Kappa.LognormalAsymptotic
import all Stats.Kappa.LognormalCumulants
import all Stats.Kappa.LognormalIIdSetup
import all Stats.Kappa.LognormalMarkov
import all Stats.Kappa.LognormalMeasure
import all Stats.Kappa.LognormalTailIntegrals
import all Stats.Kappa.LoulakisAlgebraic
import all Stats.Kappa.LoulakisLiminf
import all Stats.Kappa.LoulakisLognormal
import all Stats.Kappa.MadLayerCake
import all Stats.Kappa.MaxIIdBound
import all Stats.Kappa.Pareto
import all Stats.Kappa.Pareto.Basic
import all Stats.Kappa.Pareto.Beta
import all Stats.Kappa.Pareto.Defs
import all Stats.Kappa.Pareto.LowerBounds
import all Stats.Kappa.Pareto.RationalIntegral
import all Stats.Kappa.Pareto.Regression
import all Stats.Kappa.PearsonIV
import all Stats.Kappa.PoissonCDF
import all Stats.Kappa.Stable
import all Stats.Kappa.SumMaxBound
import all Stats.Kappa.TableI
import all Stats.LayerCake
import all Stats.Pareto
import all Stats.Pareto.AbstractCall
import all Stats.Pareto.Basic
import all Stats.Pareto.Calibration
import all Stats.Pareto.Measure
import all Stats.Pareto.Mispricing
import all Stats.Pareto.Put
import all Stats.Pareto.PutCallParity
import all Stats.Pareto.Returns
import all Stats.Pareto.TailRisk
import all Stats.RegularVariation
import all Stats.RegularVariation.Abelian
import all Stats.RegularVariation.Abelian.Basic
import all Stats.RegularVariation.Abelian.Bounded
import all Stats.RegularVariation.Abelian.FullSV
import all Stats.RegularVariation.Abelian.Potter
import all Stats.RegularVariation.Application
import all Stats.RegularVariation.Closure
import all Stats.RegularVariation.Defs
import all Stats.RegularVariation.Examples
import all Stats.RegularVariation.Karamata
import all Stats.RegularVariation.Karamata.Grid
import all Stats.RegularVariation.Karamata.Helpers
import all Stats.RegularVariation.Karamata.Measurable
import all Stats.RegularVariation.Karamata.Monotone
import all Stats.RegularVariation.Multivariate
import all Stats.RegularVariation.Representation
import all Stats.RegularVariation.Representation.Converse
import all Stats.RegularVariation.Representation.Forward
import all Stats.RegularVariation.UCT
import all Stats.RegularVariation.UCT.Measurable
import all Stats.RegularVariation.UCT.Monotone
import all Stats.RegularVariation.UCT.Potter
import all Stats.RegularVariation.Verify
import all Stats.Review.ParetoLegacy
import all Stats.ReviewChecks
import all Stats.RiskMeasures
import all Stats.RiskMeasures.CVaR
import all Stats.RiskMeasures.Drawdown
import all Stats.RiskMeasures.Kelly
import all Stats.RiskMeasures.MLE
import all Stats.RiskMeasures.MarkowitzFailure
import all Stats.RiskMeasures.Moments
import all Stats.RiskMeasures.Spectral
import all Stats.SinglePointForecasts
import all Stats.TailOptionPricing
import all Stats.Theorem1
import all Stats.Verify
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut failures : Nat := 0
  let mut axioms : NameSet := {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless moduleName == `Stats || moduleName.toString.startsWith "Stats." do
      continue
    declarations := declarations + 1
    match info with
    | .thmInfo _ => theorems := theorems + 1
    | _ => pure ()
    for ax in ← collectAxioms name do
      axioms := axioms.insert ax
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      failures := failures + 1
      logError m!"NON_CORE_AXIOM {ax}"
  logInfo m!"STATS_AUDIT declarations={declarations} theorems={theorems} non_core_axioms={failures} axioms={axioms.toArray}"
