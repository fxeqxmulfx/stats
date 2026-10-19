module

/-
  Historical invalid translation of the Pareto row in Taleb,
  arXiv:1802.05495v3, Table I and its incomplete-Beta footnote.
  These separate nonintegrable Beta integrals collapsed to zero in the
  former implementation. Keep this isolated model for the regression
  certificates; the current formula uses finite interior differences.
-/
public import Stats.Kappa.Pareto.Defs

@[expose] public section

open Real Set MeasureTheory

namespace StatsReview

/-- The former integrand, subtracting two separately divergent integrals. -/
noncomputable def legacyParetoIntegrand (α y : ℝ) : ℝ :=
  -2 * α ^ 2 * (y + 2) ^ (-2 * α - 1) * (2 / (α - 1) - y) *
    (TailOptionPricing.incompleteBeta (1 / (y + 2)) (-α) (1 - α)
      - TailOptionPricing.incompleteBeta ((y + 1) / (y + 2)) (-α) (1 - α))

/-- The former ratio expression, retained only to certify its zero value. -/
noncomputable def legacyParetoRatio (α : ℝ) : ℝ :=
  (α - 1) ^ (2 - α) * α ^ (α - 1) *
    ∫ y in (0 : ℝ)..(2 / (α - 1)), legacyParetoIntegrand α y

/-- The former κ expression, retained only to certify its constant value 2. -/
noncomputable def legacyParetoKappa (α : ℝ) : ℝ :=
  2 - Real.log 2 / Real.log (legacyParetoRatio α)

end StatsReview
