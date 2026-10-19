module

/-
  Strong-Pareto core: definitions and Results 1, 2, 3 from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  Layer-cake form taken as the *definition* of `callPrice`:
    C(K) = ∫_K^∞ ℙ(S > s) ds.

  Umbrella module — the formalisation is split into submodules:

  * `Stats.Pareto.Basic` — Result 1 (Eqs. 2–3): `survival`, `callPrice`,
    `callPrice_eq`, `callPrice_ratio`, plus the shifted-rpow integral helper.
  * `Stats.Pareto.Returns` — Result 2 (Eqs. 4–6): `survivalReturns`,
    `callPriceReturns`, `callPriceReturns_eq`, `callPriceReturns_pow_eq`,
    `callPriceReturns_invert`, `callPriceReturns_ratio`.
  * `Stats.Pareto.Put` — Result 3 (Eq. 7, corrected) and density
    normalisation: `putIntegrand`, `putRaw`, `putPrice`, `densityMass`.
  * `Stats.Pareto.PutCallParity` — put-call parity in the strong-Pareto
    density and the upside-Pareto returns density.
  * `Stats.Pareto.TailRisk` — VaR, CVaR, tail expectation under the
    strong-Pareto density.
  * `Stats.Pareto.AbstractCall` — abstract call-price functional
    `callPrice_F F K := ∫_K^∞ F(s) ds` and the Pareto envelope.
  * `Stats.Pareto.Mispricing` — BS-vs-Pareto gap asymptotics plus the
    variance-swap non-integrability for `α ≤ 2`.
  * `Stats.Pareto.Calibration` — multi-anchor parameter inversion and
    term structure under `α`-stable scaling.
-/
public import Stats.Pareto.Basic
public import Stats.Pareto.Returns
public import Stats.Pareto.Put
public import Stats.Pareto.PutCallParity
public import Stats.Pareto.TailRisk
public import Stats.Pareto.AbstractCall
public import Stats.Pareto.Mispricing
public import Stats.Pareto.Calibration

@[expose] public section
