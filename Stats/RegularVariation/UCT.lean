module

/-
  Karamata's theory of regular variation — Uniform Convergence Theorem
  and Potter's bounds.

  Two variants of UCT:
  * Monotone (Karamata 1933): elementary sandwich proof.
  * Measurable (Korevaar et al.): Csiszár–Erdős proof using a Lebesgue-DCT
    measure-counting argument on indicator functions.

  Potter's bounds are a quantitative consequence of UCT in each variant.

  Umbrella module — the formalisation is split into:

  * `Stats.RegularVariation.UCT.Monotone` — monotone UCT.
  * `Stats.RegularVariation.UCT.Measurable` — measurable UCT.
  * `Stats.RegularVariation.UCT.Potter` — Potter bounds in both variants.
-/
public import Stats.RegularVariation.UCT.Monotone
public import Stats.RegularVariation.UCT.Measurable
public import Stats.RegularVariation.UCT.Potter

@[expose] public section
