module

/-
  Operational transitive-axiom scanner used by Stats.AxiomAudit.
  The separate module keeps its exhaustive project-import list short.
  It uses declaration origin, including private declarations, and the
  official Lean transitive axiom collector for each project root.
-/
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

public section
meta section

open Lean Elab Command

/-- Audit every imported Stats declaration, failing on non-core axioms. -/
elab "audit_stats" : command => do
  let env ← getEnv
  let statsModules := env.header.moduleNames.map fun n => n == `Stats || n.toString.startsWith "Stats."
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut failures : Nat := 0
  let mut axioms : NameSet := {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless statsModules[idx.toNat]! do
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
