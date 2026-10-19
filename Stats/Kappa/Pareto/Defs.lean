module

/-
  Taleb, arXiv:1802.05495v3, Table I, Pareto row and its incomplete-Beta
  footnote (kappa-n-final.tex, line 209). The two printed Beta integrals
  diverge separately. Their difference is corrected by using a common
  interior base point, so it is an ordinary finite integral between the
  two positive endpoints. This correction is not a literal formalization
  of the footnote's improper integrals.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open Real Set MeasureTheory

namespace TailOptionPricing

/-- The literal real incomplete-Beta integral in the paper's footnote.
For the Pareto parameters it is not integrable and its total Bochner value
is zero. It is retained for the historical diagnostic, not used to evaluate
the corrected Pareto difference below. -/
noncomputable def incompleteBeta (z a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..z, t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- The Beta kernel, positive for every real `a,b` when `0 < t < 1`. -/
noncomputable def betaKernel (a b t : ℝ) : ℝ :=
  t ^ (a - 1) * (1 - t) ^ (b - 1)

/-- A Beta primitive based at `1/2`. Its differences on `(0,1)` are finite
integrals even at the negative parameters of the paper's Pareto row.
The arbitrary base point cancels; no individual improper Beta value is
asserted to converge. -/
noncomputable def incompleteBetaCentered (z a b : ℝ) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..z, betaKernel a b t

/-- Corrected Table I Pareto integrand: the printed Beta difference is
interpreted as one convergent integral between its positive endpoints.
For `α > 1` and `0 ≤ y ≤ 2/(α-1)` both endpoints lie in `(0,1)`.
The connection to the actual iid-sum MAD is a separate probability theorem. -/
noncomputable def paretoIntegrand (α y : ℝ) : ℝ :=
  -2 * α ^ 2 * (y + 2) ^ (-2 * α - 1) * (2 / (α - 1) - y) *
    (incompleteBetaCentered (1 / (y + 2)) (-α) (1 - α)
      - incompleteBetaCentered ((y + 1) / (y + 2)) (-α) (1 - α))

/-- The paper's proposed Pareto ratio with the corrected finite Beta
difference. This analytic expression is not identified with an actual
`M(2)/M(1)` merely by naming it a ratio. -/
noncomputable def paretoRatio (α : ℝ) : ℝ :=
  (α - 1) ^ (2 - α) * α ^ (α - 1) *
    ∫ y in (0 : ℝ)..(2 / (α - 1)), paretoIntegrand α y

/-- The logarithmic expression obtained from the corrected analytic ratio.
A distributional interpretation still requires the genuine Pareto MAD
identity. Source: arXiv:1802.05495v3, Table I, with the correction above. -/
noncomputable def paretoKappa (α : ℝ) : ℝ :=
  2 - Real.log 2 / Real.log (paretoRatio α)

end TailOptionPricing
