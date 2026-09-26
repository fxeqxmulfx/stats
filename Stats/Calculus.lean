/-
  Calculus of the strong-Pareto call price:
    • generic FTC for `K ↦ ∫_K^∞ F(s) ds` (`hasDerivAt_integral_Ioi`),
    • Breeden–Litzenberger first/second derivatives,
    • continuity on `Ici l`,
    • strict convexity on `Ioi l` and on the closed `Ici l`,
    • pure-power-law butterfly bound (Eq. 8 specialised).

  Umbrella module — the formalisation is split into:

  * `Stats.Calculus.CallPrice` — generic FTC + Breeden–Litzenberger
    for the call, plus continuity, convexity, and the butterfly bound.
  * `Stats.Calculus.PutShadow` — Breeden–Litzenberger for the upside-returns
    shadow put plus its strict convexity / boundary continuity.
  * `Stats.Calculus.Greeks` — Pareto Greeks `∂C/∂α`, `∂C/∂l`,
    `∂P̂/∂α`, `∂P̂/∂l`.
-/
import Stats.Calculus.CallPrice
import Stats.Calculus.PutShadow
import Stats.Calculus.Greeks
