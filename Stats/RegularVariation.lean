module

/-
  Karamata's theory of regular variation — **umbrella module**.

  Proves the structural results needed for the full slowly-varying version
  of Theorem 1.  In particular, the Karamata bound
  `log L(s · e^t) − log L(s) = o(t)` follows from slow variation,
  eventual positivity, and measurability (or the stated monotonicity).

  All proofs are closed.  This module is imported by
  `Stats.TailOptionPricing`, so the full Theorem 1 and the full
  slowly-varying Abelian theorem are available through `import Stats`.
  `Stats.AxiomAudit` checks transitive axiom dependencies across the library.

  ## Sub-modules

  * `Defs`            — `IsSlowlyVarying` and equivalence with `RV_0`.
  * `Examples`        — constants, `Real.log`, `(log s)^k`.
  * `Closure`         — eventually-equal, mul, div, translation.
  * `UCT`             — Uniform Convergence Theorem (monotone + measurable
                        variants) and Potter's bounds.
  * `Karamata`        — the `o`-bound `log L = o(log s)`, monotone variant
                        proved directly via iteration; the measurable
                        variant via the Korevaar UCT.
  * `Representation`  — Karamata's representation theorem
                        `L(s) = c(s) · exp(∫_T^s ε(u)/u du)` (both
                        directions); follows the BGT 1.3.1 recipe.
  * `Application`     — Theorem 1 full slowly-varying via the Karamata bound.
  * `Abelian`         — Karamata's Abelian theorem (bounded and full
                        measurable slowly varying forms):
                        `∫_K^∞ L(s)·s^(-α) ds ~ L(K)·K^(1-α)/(α-1)`,
                        and the asymptotic ratio version of Result 1 / Eq. (3).
  * `Multivariate`    — finite-dimensional projection definitions and
                        elementary inner-product/norm identities.

  ## Roadmap

  ```
  IsSlowlyVarying  ←→  IsRegularlyVarying _ 0           [definition unfold]
        │
        ▼
  Examples (const, log, log^k, eventually-bounded)      [direct]
        │
        ▼
  Closure: products, quotients, translation             [direct]
        │
        ▼
  UCT (uniform convergence on compact intervals)        [HARD — Baire / Steinhaus]
        │ alternatively, monotone variant               [easier — Karamata's original]
        ▼
  Potter's bounds                                       [from UCT]
        │
        ▼
  Karamata representation L(s) = c(s)·exp(∫ ε(u)/u du)  [from UCT]
        │
        ▼
  log L(s) = o(log s)                                   [from representation;
                                                         **monotone variant
                                                         proved directly**]
        │
        ▼
  Karamata bound: log L(s·e^t) − log L(s) = o(t)        [from log-bound]
        │
        ▼
  Theorem 1, full slowly-varying version                [direct corollary]
  ```
-/
public import Stats.RegularVariation.Defs
public import Stats.RegularVariation.Examples
public import Stats.RegularVariation.Closure
public import Stats.RegularVariation.UCT
public import Stats.RegularVariation.Karamata
public import Stats.RegularVariation.Representation
public import Stats.RegularVariation.Application
public import Stats.RegularVariation.Abelian
public import Stats.RegularVariation.Multivariate

@[expose] public section
