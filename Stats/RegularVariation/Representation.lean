module

/-
  Karamata's representation theorem for slowly varying functions.

  **Theorem (Karamata, 1933).**  A measurable, eventually positive function
  `L : ℝ → ℝ` is slowly varying iff there exist `T > 0`, measurable
  `c, ε : ℝ → ℝ`, and `c₀ > 0` such that
  - `c(s) → c₀` as `s → ∞`
  - `ε(s) → 0` as `s → ∞`
  - `L(s) = c(s) · exp(∫_T^s ε(u)/u du)` for all `s ≥ T`.

  Umbrella module — the proof is split into:

  * `Stats.RegularVariation.Representation.Converse` — `IsKaramataRepresentation`
    predicate and the easy direction (representation ⇒ SV).
  * `Stats.RegularVariation.Representation.Forward` — the hard direction
    (SV ⇒ representation) via the BGT recipe (additive η + moving
    average ξ + UCT bound + back-substitution).
-/
public import Stats.RegularVariation.Representation.Converse
public import Stats.RegularVariation.Representation.Forward

@[expose] public section
