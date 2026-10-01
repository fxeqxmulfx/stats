/-
  Audit every declaration originating in Stats modules, including private
  declarations, for transitive dependence on non-standard axioms.
  Run: lake build Stats.AxiomAudit
-/
import Stats
import Stats.RegularVariation
import Stats.Pareto.Measure
import Stats.Copula.Basic
import Stats.ReviewChecks
import Stats.Verify
import Stats.RegularVariation.Verify
import Lean.Util.CollectAxioms

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
