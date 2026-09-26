/-
  Karamata's theory of regular variation — **umbrella module**.

  Lays out definitions and the chain of target theorems needed to close the
  gap in `survivalLogReturn_not_regularlyVarying_slow` (Theorem 1, full
  slowly-varying version), where the *Karamata bound*
  `log L(s · e^t) − log L(s) = o(t)` is currently passed as an explicit
  hypothesis (`h_subexp`).  Karamata's representation theorem turns that
  hypothesis into a consequence of "L is slowly varying".

  The module is **deliberately not imported by `Stats.TailOptionPricing`**.
  It still contains `sorry` placeholders for non-trivial structural results
  so that the published API rooted at `Stats.lean → Stats.TailOptionPricing`
  remains axiom-clean (still: 80 theorems, 0 `sorry`).  Individual results
  here can be migrated piece-by-piece into the main API once closed,
  and ultimately upstreamed to `Mathlib/Analysis/SpecialFunctions/`.

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
  * `Abelian`         — Karamata's Abelian theorem (bounded-`L` form):
                        `∫_K^∞ L(s)·s^(-α) ds ~ L(K)·K^(1-α)/(α-1)`,
                        and the asymptotic ratio version of Result 1 / Eq. (3).

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
import Stats.RegularVariation.Defs
import Stats.RegularVariation.Examples
import Stats.RegularVariation.Closure
import Stats.RegularVariation.UCT
import Stats.RegularVariation.Karamata
import Stats.RegularVariation.Representation
import Stats.RegularVariation.Application
import Stats.RegularVariation.Abelian
