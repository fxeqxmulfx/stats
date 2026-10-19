module

/-
  Karamata's Abelian theorem and the slowly-varying generalisation of
  Result 1 / Eq. (3).

  For survival `bF(s) = L(s) · s^(-α)` with `L` slowly varying and α > 1,
  the call price
      C(K) := ∫_K^∞ L(s) · s^(-α) ds
  satisfies the **asymptotic** version of Result 1
      C(K) · (α - 1) / (L(K) · K^(1-α))  →  1   as K → ∞,
  hence the **asymptotic** ratio
      C(c·K) / C(K)  →  c^(1-α).

  Umbrella module — the formalisation is split into:

  * `Stats.RegularVariation.Abelian.Basic` — `survivalSV`, `callPriceSV`,
    substitution identity, and the strong-Pareto special case.
  * `Stats.RegularVariation.Abelian.Bounded` — Abelian theorem under
    bounded-L assumption.
  * `Stats.RegularVariation.Abelian.Potter` — global Potter bound.
  * `Stats.RegularVariation.Abelian.FullSV` — full SV form of the
    Abelian theorem.
-/
public import Stats.RegularVariation.Abelian.Basic
public import Stats.RegularVariation.Abelian.Bounded
public import Stats.RegularVariation.Abelian.Potter
public import Stats.RegularVariation.Abelian.FullSV

@[expose] public section
