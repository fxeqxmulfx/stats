module

/-
  Umbrella module for the concrete lognormal Black–Scholes development.

  Sub-modules:
    Stats/BlackScholes/Survival.lean   — `survivalLN` and basic properties.
    Stats/BlackScholes/StdNormal.lean  — `stdNormalCdf`, location-scale,
                                         exp-tilt, Mills' ratio, Φ derivative.
    Stats/BlackScholes/CallPrice.lean  — `callPriceBS`, expectation form,
                                         decomposition, closed forms,
                                         risk-neutral survival, dominance.
    Stats/BlackScholes/Erfc.lean       — `erfc` + connections + α lower bound
                                         in the paper's `(1/2) erfc(...)` form.
    Stats/BlackScholes/Greeks.lean     — `bs_pdf_identity`, `Δ`, `Γ`, K-Greek,
                                         risk-neutral BSC dominance, martingale.
    Stats/BlackScholes/PutCall.lean    — `putPriceBS`, parity, put closed forms.
-/
public import Stats.BlackScholes.Survival
public import Stats.BlackScholes.StdNormal
public import Stats.BlackScholes.CallPrice
public import Stats.BlackScholes.Erfc
public import Stats.BlackScholes.Greeks
public import Stats.BlackScholes.PutCall
public import Stats.BlackScholes.Smile
public import Stats.BlackScholes.ReturnsSmile
public import Stats.BlackScholes.ReturnsSmileExamples
public import Stats.BlackScholes.StrictButterfly

@[expose] public section
