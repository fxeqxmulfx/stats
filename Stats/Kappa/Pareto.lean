module

/-
  Corrected finite-Beta expression for Taleb's Pareto row,
  arXiv:1802.05495v3, Table I. The literal improper Beta definition is
  retained only for diagnostics; the current ratio is convergent and
  positive, with a nondegenerate exact regression at alpha = 2.
-/
public import Stats.Kappa.Pareto.Defs
public import Stats.Kappa.Pareto.Beta
public import Stats.Kappa.Pareto.Basic
public import Stats.Kappa.Pareto.LowerBounds
public import Stats.Kappa.Pareto.RationalIntegral
public import Stats.Kappa.Pareto.Regression
