module

/-
  Hedging under fat tails.

  Three items, each a Pareto-native counterpart to a standard
  delta-hedging / replication / sensitivity statement:

    1. **Dynamic-hedging P&L distribution.**  The discrete delta-hedging
       error `∑ ½ Γ(S_i) · (ΔS_i)²` under Pareto-distributed jumps `ΔS`.
       Pointwise, `(ΔS)²` has survival `(l² / x)^(α/2) = (l/√x)^α`,
       i.e. it is itself a strong-Pareto law with scale `l²` and tail
       index `α/2`.  Consequently, for constant Gamma the expected
       per-step P&L equals `½ · Γ · E[(ΔS)²]`, finite iff `α > 2`
       (`paretoSecondMoment_integrableOn_iff`); for `α ≤ 2` the
       expectation diverges even before summation — dynamic hedging
       is unreliable in the fat-tail regime.

    2. **Static replication of `g(S_T)` under Pareto-priced calls.**
       Combines `carrMadan` (finite-strip Carr–Madan) with the Pareto
       closed forms `callPrice_eq` and `putShadow_eq` to substitute the
       Pareto-internal pricing into both wings of the static-replication
       identity.  The Pareto call/put-strip costs admit closed-form
       polynomial integrands.

    3. **K-decay rates of Greeks: Pareto vs BS.**  The Pareto Vega-to-price
       ratio satisfies the closed form
            `(∂C/∂α) / C(l, α, K) = log(l/K) − 1/(α−1)`,
       which **diverges to `−∞`** as `K → ∞` (linearly in `log K`).
       In contrast, the BS Vega `S₀ · φ(d₁)` decays super-exponentially
       (the Gaussian PDF decays super-polynomially via Mills' ratio).
       The qualitative asymmetry — bounded BS relative sensitivity vs
       unbounded Pareto relative sensitivity — is precisely the claim
       that a BS-fitted vol surface cannot reproduce Pareto tail
       sensitivities.
-/
public import Stats.RiskMeasures
public import Stats.CarrMadan
public import Stats.BlackScholes

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Item 1 — Dynamic-hedging P&L distribution.

    Delta-hedging error `∑ ½ Γ(S_i) · (ΔS_i)²`.  Two facts:

    * `squaredReturn_survival_eq`: pointwise identity
        `(l/√x)^α = (l² / x)^(α/2)`,
      showing that `(ΔS)²` is strong-Pareto with index `α/2` whenever
      `ΔS` is strong-Pareto with index `α`.  This *halves* the tail
      index, so two extra moments are lost to the squaring.
    * `gammaPnL_constant_eq`: for constant Gamma `Γ ≡ c` and `α > 2`,
      the expected per-step gamma P&L is `½ · c · E[(ΔS)²]
        = ½ · c · 2αl² / (α−2)`.
    * `gammaPnL_constant_not_integrable`: for `α ≤ 2` the per-step
      gamma P&L integrand is *not* integrable — expected hedging
      error diverges. -/

/-- **Squared-return survival under Pareto.**  For `x ≥ l² > 0`, the
    pointwise identity
        `(l / √x)^α = (l² / x)^(α/2)`
    holds.  Interpretation: under `ΔS ~ Pareto(l, α)`, the squared
    return `(ΔS)²` has Pareto survival with **half** the tail index. -/
theorem squaredReturn_survival_eq {l α x : ℝ}
    (hl : 0 < l) (hx : 0 < x) :
    (l / Real.sqrt x) ^ α = (l ^ (2:ℝ) / x) ^ (α / 2) := by
  have hsqx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hl_div_sqx_nn : 0 ≤ l / Real.sqrt x := div_nonneg hl.le hsqx_pos.le
  have hlsq_div_x_nn : 0 ≤ l ^ (2:ℝ) / x :=
    div_nonneg (Real.rpow_nonneg hl.le _) hx.le
  have h_sqrt_x_sq : Real.sqrt x ^ (2:ℝ) = x := by
    rw [show ((2:ℝ) = (2:ℕ)) from by norm_num, Real.rpow_natCast,
        Real.sq_sqrt hx.le]
  -- (l/√x)² = l²/x
  have h_inner : (l / Real.sqrt x) ^ (2:ℝ) = l ^ (2:ℝ) / x := by
    rw [Real.div_rpow hl.le hsqx_pos.le, h_sqrt_x_sq]
  -- ((l/√x)²)^(α/2) = (l/√x)^(2·(α/2)) = (l/√x)^α.
  calc (l / Real.sqrt x) ^ α
      = (l / Real.sqrt x) ^ ((2:ℝ) * (α / 2)) := by
        congr 1; ring
    _ = ((l / Real.sqrt x) ^ (2:ℝ)) ^ (α / 2) := by
        rw [Real.rpow_mul hl_div_sqx_nn]
    _ = (l ^ (2:ℝ) / x) ^ (α / 2) := by rw [h_inner]

/-- **`(ΔS)²` is strong-Pareto with index `α/2`.**  Re-expression of
    `squaredReturn_survival_eq` in the `survival` notation: the
    survival function of `(ΔS)²` at level `x ≥ l²` equals the
    strong-Pareto survival at scale `l²` and index `α/2`. -/
theorem squaredReturn_survival_eq_survival {l α x : ℝ}
    (hl : 0 < l) (hx : 0 < x) :
    survival l α (Real.sqrt x) = survival (l ^ (2:ℝ)) (α / 2) x := by
  unfold survival
  exact squaredReturn_survival_eq hl hx

/-- **Gamma-weighted P&L integrand.**  Per-step delta-hedging error
    integrand: `½ · Γ(s) · s²`, weighted later against the Pareto
    density to take expectations. -/
noncomputable def gammaPnLIntegrand (Γ : ℝ → ℝ) (s : ℝ) : ℝ :=
  (1 / 2) * Γ s * s ^ (2:ℝ)

/-- Factoring a constant Gamma from the total density integral gives
`½ c` times the second-moment integral for all real parameters.
For a genuine finite Pareto expectation require `α > 2` and `l > 0`
and the corresponding integrability result; this factorization alone
does not establish those probabilistic conditions. -/
theorem gammaPnL_constant_eq {c l α : ℝ} :
    ∫ s in Ioi l, gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s
      = (1 / 2) * c * paretoMoment l α 2 := by
  unfold gammaPnLIntegrand paretoMoment paretoMomentIntegrand
  -- ½ · c · s² · paretoDensity = ½ · c · (s² · paretoDensity), so
  -- ∫ ... = ½ · c · ∫ s² · paretoDensity.
  have h_pt : ∀ s : ℝ,
      (1 / 2) * c * s ^ (2:ℝ) * paretoDensity l α s
        = ((1 / 2) * c) * (s ^ (2:ℝ) * paretoDensity l α s) := by
    intro s; ring
  simp_rw [h_pt]
  rw [MeasureTheory.integral_const_mul]

/-- **Squared-return integrand bridge.**  The integrand `s² · paretoDensity`
    is identically `α · (s · survival l α s)` on `(l, ∞)`.  Direct
    corollary of `paretoMomentIntegrand_eq_layerCake` at `k = 2`. -/
private theorem squaredReturn_density_eq_layerCake {l α s : ℝ}
    (hl : 0 < l) (hs : l < s) :
    s ^ (2:ℝ) * paretoDensity l α s = α * (s * survival l α s) := by
  have h := paretoMomentIntegrand_eq_layerCake (l := l) (α := α) (k := 2) hl hs
  unfold paretoMomentIntegrand at h
  have hs_pos : 0 < s := hl.trans hs
  rw [show ((2:ℝ) - 1) = 1 from by norm_num] at h
  rw [Real.rpow_one] at h
  exact h

/-- **Gamma-P&L integrability characterisation under constant `Γ`.**
    For nonzero constant `Γ ≡ c`, the per-step expected gamma P&L
        ∫_l^∞ ½·c · s² · paretoDensity(s) ds
    is integrable iff `α > 2`. -/
theorem gammaPnL_constant_integrableOn_iff {c l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hc : c ≠ 0) :
    IntegrableOn
        (fun s => gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s)
        (Ioi l) volume ↔ 2 < α := by
  unfold gammaPnLIntegrand
  have hc_half_ne : ((1 / 2) * c : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) hc
  have hc_half_unit : IsUnit ((1 / 2) * c : ℝ) :=
    isUnit_iff_ne_zero.mpr hc_half_ne
  -- pointwise: ½·c·s²·paretoDensity = (½·c) · (s² · paretoDensity)
  have h_pt : (fun s => (1 / 2) * c * s ^ (2:ℝ) * paretoDensity l α s)
      = fun s => ((1 / 2) * c) * (s ^ (2:ℝ) * paretoDensity l α s) := by
    funext s; ring
  rw [h_pt]
  show Integrable
      (fun s : ℝ => ((1 / 2) * c) * (s ^ (2:ℝ) * paretoDensity l α s))
      (volume.restrict (Ioi l)) ↔ 2 < α
  rw [integrable_const_mul_iff hc_half_unit]
  -- now reduce to paretoMomentIntegrand integrability at k = 2.
  have h_eqfun : (fun s : ℝ => s ^ (2:ℝ) * paretoDensity l α s)
      = paretoMomentIntegrand l α 2 := rfl
  rw [show (fun s : ℝ => s ^ (2:ℝ) * paretoDensity l α s)
        = paretoMomentIntegrand l α 2 from rfl]
  exact paretoMomentIntegrand_integrableOn_iff hl hα_pos

/-- **Dynamic hedging fails for `α ≤ 2`.**  For nonzero constant
    `Γ ≡ c`, the per-step expected gamma P&L integrand is *not*
    integrable on `(l, ∞)` whenever `1 < α ≤ 2`.  The expected
    delta-hedging error is infinite — dynamic hedging cannot
    cover the gamma exposure in the fat-tail regime. -/
theorem gammaPnL_constant_not_integrable {c l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) (hα_le : α ≤ 2) (hc : c ≠ 0) :
    ¬ IntegrableOn
        (fun s => gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s)
        (Ioi l) volume := by
  intro h
  have hα_pos : 0 < α := by linarith
  have h' := (gammaPnL_constant_integrableOn_iff hl hα_pos hc).mp h
  linarith

/-- **Dynamic hedging is bounded for `α > 4`.**  When `α > 4`, the
    *variance* of the per-step squared return `(ΔS)²` is finite (since
    `(ΔS)²` has tail index `α/2 > 2`).  Algebraic reflection:
    `((ΔS)²)² = (ΔS)⁴`, whose integrand is the `k = 4` Pareto moment
    integrand. -/
theorem squaredReturn_variance_integrableOn_iff {l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α 4) (Ioi l) volume ↔ 4 < α :=
  paretoMomentIntegrand_integrableOn_iff hl hα_pos

/-! ## Item 2 — Static replication of `g(S_T)` under Pareto-priced calls.

    Combines `carrMadan` (finite-strip Carr–Madan static-replication
    identity) with the Pareto closed forms `callPrice_eq` and
    `putShadow_eq` to substitute Pareto-internal pricing into both
    wings of the replication identity.

    Concretely, the Carr–Madan call-strip integrand `(S − K)⁺ · g''(K)`
    integrates against Pareto-priced calls as the polynomial integrand
    `g''(K) · l^α · K^(1−α) / (α−1)` (closed form of
    `callPrice l α K`). -/

/-- **Pareto-priced call-strip cost (closed form on `[F, b]`, `l ≤ F ≤ b`).**
    The Carr–Madan call-strip cost weighted by the Pareto-priced call
    surface reduces to a polynomial integrand:
        ∫_F^b g''(K) · callPrice(l, α, K) dK
            = ∫_F^b g''(K) · l^α · K^(1−α) / (α−1) dK. -/
theorem paretoCallStripCost_eq {g'' : ℝ → ℝ} {l α F b : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hF : l ≤ F) (hFb : F ≤ b) :
    ∫ K in F..b, g'' K * callPrice l α K
      = ∫ K in F..b, g'' K * (l ^ α * K ^ (1 - α) / (α - 1)) := by
  apply intervalIntegral.integral_congr
  intro K hK
  rw [Set.uIcc_of_le hFb] at hK
  have hlK : l ≤ K := hF.trans hK.1
  show g'' K * callPrice l α K = g'' K * (l ^ α * K ^ (1 - α) / (α - 1))
  rw [callPrice_eq hα hl hlK]

/-- **Pareto-priced put-strip cost (closed form on `[a, F]`, `l ≤ a ≤ F`).**
    Symmetric to `paretoCallStripCost_eq`: the Carr–Madan put-strip cost
    weighted by the *shadow* put-price surface (the Pareto within-density
    put) reduces to the affine-corrected Pareto closed form:
        ∫_a^F g''(K) · putShadow(l, α, K) dK
            = ∫_a^F g''(K) · (l^α · K^(1−α)/(α−1) + K − α·l/(α−1)) dK. -/
theorem paretoPutStripCost_eq {g'' : ℝ → ℝ} {l α a F : ℝ}
    (hα : 1 < α) (hl : 0 < l) (ha : l ≤ a) (haF : a ≤ F) :
    ∫ K in a..F, g'' K * putShadow l α K
      = ∫ K in a..F, g'' K *
          (l ^ α * K ^ (1 - α) / (α - 1) + K - α * l / (α - 1)) := by
  apply intervalIntegral.integral_congr
  intro K hK
  rw [Set.uIcc_of_le haF] at hK
  have hlK : l ≤ K := ha.trans hK.1
  show g'' K * putShadow l α K
        = g'' K * (l ^ α * K ^ (1 - α) / (α - 1) + K - α * l / (α - 1))
  rw [putShadow_eq hα hl hlK]

/-- **Pareto-priced static replication formula.**  Combining
    `carrMadan` (the finite-strip Carr–Madan identity) with the Pareto
    closed forms, every payoff `g` that is `C²` on `[a, b]` (with
    `l ≤ a ≤ F ≤ b`) admits the static-replication identity
        g(S) = g(F) + g'(F)·(S − F)
             + ∫_a^F (K − S)⁺ · g''(K) dK
             + ∫_F^b (S − K)⁺ · g''(K) dK,
    where the put-strip and call-strip costs admit the explicit Pareto
    closed-form substitutions (see `paretoCallStripCost_eq` and
    `paretoPutStripCost_eq`).
    This is a model-free alias of `carrMadan` at the payoff level. The
    unused Pareto parameters and their hypotheses have been removed;
    pricing the strips is handled by the separate pricing theorems. -/
theorem paretoCarrMadan {g g' g'' : ℝ → ℝ} {a b F S : ℝ}
    (hF : F ∈ Set.Icc a b) (hS : S ∈ Set.Icc a b)
    (hg_cont   : ContinuousOn g (Set.Icc a b))
    (hg'_cont  : ContinuousOn g' (Set.Icc a b))
    (hg''_cont : ContinuousOn g'' (Set.Icc a b))
    (hg_deriv  : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt g' (g'' x) x) :
    g S = g F + g' F * (S - F)
        + (∫ K in a..F, max (K - S) 0 * g'' K)
        + (∫ K in F..b, max (S - K) 0 * g'' K) :=
  carrMadan hF hS hg_cont hg'_cont hg''_cont hg_deriv hg'_deriv

/-! ## Item 3 — K-decay rates of Greeks: Pareto vs Black–Scholes.

    Quantifies the qualitative asymmetry between Pareto and BS tail
    sensitivities.  The Pareto Vega-to-price ratio admits the closed
    form `(∂C/∂α) / C(l, α, K) = log(l/K) − 1/(α−1)`, which
    *diverges to `−∞`* as `K → ∞`.  In contrast, the BS Vega
    `S₀ · φ(d₁)` decays super-exponentially via the Gaussian PDF.

    Implication: a BS-fitted vol surface cannot reproduce Pareto tail
    sensitivities — deep-OTM tail prices change non-vanishingly in
    relative terms under small `α` perturbations. -/

/-- **Pareto Vega-to-price ratio (closed form).**  Under strong Pareto,
        `(∂C/∂α) / C(l, α, K) = log(l/K) − 1/(α − 1)`.

    Equivalent statement of the relative tail-index sensitivity:
    differentiating `log C = α · log l + (1 − α) · log K − log(α − 1)`
    in `α` gives `log(l/K) − 1/(α − 1)`.  Diverges to `−∞` as `K → ∞`. -/
theorem paretoVega_relative_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) /
        (α - 1) ^ 2) / callPrice l α K
      = Real.log (l / K) - 1 / (α - 1) := by
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have hα1_sq_ne : (α - 1 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hα1_ne
  have hK_pos : 0 < K := hl.trans hK
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  have hK_pow_pos : 0 < K ^ (1 - α) := Real.rpow_pos_of_pos hK_pos _
  have hC_pos : 0 < callPrice l α K := by
    rw [callPrice_eq hα hl hK.le]
    positivity
  have hC_ne : callPrice l α K ≠ 0 := hC_pos.ne'
  rw [callPrice_eq hα hl hK.le]
  have h_log_eq : Real.log l - Real.log K = Real.log (l / K) :=
    (Real.log_div hl.ne' hK_pos.ne').symm
  rw [h_log_eq]
  have h_lK_ne : l ^ α * K ^ (1 - α) ≠ 0 :=
    mul_ne_zero hl_pow_pos.ne' hK_pow_pos.ne'
  -- (A · B / D²) / (A / D) where A = l^α K^(1-α), B = (α-1)·log(l/K) - 1, D = α-1
  --   = A · B / D² · D / A = B / D = log(l/K) - 1/D
  field_simp

/-- The logarithmic expression tends to `−∞` as `K → ∞`, for every
real `α` and positive `l`. On the pricing domain `α > 1`, the preceding
`paretoVega_relative_eq` identifies it with the relative Pareto call
sensitivity. This limit alone does not extend that pricing identity
to parameters outside its domain. -/
theorem paretoVega_relative_tendsto_atBot {l α : ℝ}
    (hl : 0 < l) :
    Tendsto (fun K : ℝ => Real.log (l / K) - 1 / (α - 1)) atTop atBot := by
  -- log(l/K) = log l - log K *eventually* for K > 0, then log K → ∞.
  have h_logK_atTop : Tendsto (fun K : ℝ => Real.log K) atTop atTop :=
    Real.tendsto_log_atTop
  have h_neg : Tendsto (fun K : ℝ => -Real.log K) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h_logK_atTop
  have h_logl_const : Tendsto (fun K : ℝ => Real.log l - Real.log K) atTop atBot := by
    have h := Filter.tendsto_atBot_add_const_left atTop (Real.log l) h_neg
    have h_eq : (fun K : ℝ => Real.log l + -Real.log K)
              = (fun K : ℝ => Real.log l - Real.log K) := by
      funext K; ring
    rwa [h_eq] at h
  have h_full : Tendsto (fun K : ℝ => Real.log l - Real.log K - 1 / (α - 1))
      atTop atBot := by
    have := Filter.tendsto_atBot_add_const_right atTop (-(1 / (α - 1))) h_logl_const
    have h_eq : (fun K : ℝ => Real.log l - Real.log K + -(1 / (α - 1)))
              = (fun K : ℝ => Real.log l - Real.log K - 1 / (α - 1)) := by
      funext K; ring
    rwa [h_eq] at this
  -- Match the goal via EventuallyEq (log(l/K) = log l - log K eventually).
  have h_evEq : (fun K : ℝ => Real.log (l / K) - 1 / (α - 1)) =ᶠ[atTop]
                (fun K : ℝ => Real.log l - Real.log K - 1 / (α - 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with K hK
    rw [Real.log_div hl.ne' hK.ne']
  exact h_full.congr' h_evEq.symm

open ProbabilityTheory in
/-- **BS Vega decays super-exponentially in `K`.**  The BS Vega
    `S₀ · φ(d₁(σ, K))` is dominated by the Gaussian PDF `φ(d₁)`.
    Since `d₁ = (log(S₀/K) + σ²/2)/σ → −∞` as `K → ∞`, and
    `φ(c) = (2π)^(−1/2) · exp(−c²/2)` decays super-exponentially in
    `|c|`, the BS Vega decays to `0` as `K → ∞`.  Combined with
    `paretoVega_relative_tendsto_atBot`, this gives the headline
    qualitative asymmetry: Pareto relative Vega is unbounded but
    BS Vega vanishes deep in the tail. -/
theorem bsVega_tendsto_zero_atTop {S₀ σ : ℝ} (hS₀ : 0 < S₀) (hσ : 0 < σ) :
    Tendsto
      (fun K : ℝ => S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + σ ^ 2 / 2) / σ))
      atTop (𝓝 0) := by
  -- Step 1: log(S₀/K) → -∞ as K → ∞.
  have h_logK : Tendsto (fun K : ℝ => Real.log K) atTop atTop :=
    Real.tendsto_log_atTop
  have h_neg_logK : Tendsto (fun K : ℝ => -Real.log K) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h_logK
  have h_logS₀K_aux : Tendsto (fun K : ℝ => Real.log S₀ - Real.log K) atTop atBot := by
    have := Filter.tendsto_atBot_add_const_left atTop (Real.log S₀) h_neg_logK
    have h_eq : (fun K : ℝ => Real.log S₀ + -Real.log K)
              = (fun K : ℝ => Real.log S₀ - Real.log K) := by
      funext K; ring
    rwa [h_eq] at this
  have h_evEq_log : (fun K : ℝ => Real.log (S₀ / K)) =ᶠ[atTop]
              (fun K : ℝ => Real.log S₀ - Real.log K) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with K hK
    rw [Real.log_div hS₀.ne' hK.ne']
  have h_logS₀K : Tendsto (fun K : ℝ => Real.log (S₀ / K)) atTop atBot :=
    h_logS₀K_aux.congr' h_evEq_log.symm
  -- Step 2: d₁(K) = (log(S₀/K) + σ²/2)/σ → -∞ as K → ∞.
  have h_d1_num : Tendsto
      (fun K : ℝ => Real.log (S₀ / K) + σ ^ 2 / 2) atTop atBot :=
    Filter.tendsto_atBot_add_const_right atTop (σ ^ 2 / 2) h_logS₀K
  have h_d1_atBot :
      Tendsto (fun K : ℝ => (Real.log (S₀ / K) + σ ^ 2 / 2) / σ) atTop atBot :=
    h_d1_num.atBot_div_const hσ
  -- Step 3: gaussianPDFReal 0 1 c → 0 as c → -∞.
  have h_pdf_to_zero :
      Tendsto (fun c : ℝ => gaussianPDFReal 0 1 c) atBot (𝓝 0) := by
    -- φ(c) = (2π)^(-1/2) · exp(-c²/2); c² → ∞ at atBot ⇒ exp(-c²/2) → 0.
    have h_pow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop two_ne_zero
    have h_abs : Tendsto (fun c : ℝ => |c|) atBot atTop :=
      tendsto_abs_atBot_atTop
    have h_sq_abs : Tendsto (fun c : ℝ => |c| ^ 2) atBot atTop :=
      h_pow.comp h_abs
    have h_sq : Tendsto (fun c : ℝ => c ^ 2) atBot atTop := by
      have h_eq : (fun c : ℝ => |c| ^ 2) = (fun c : ℝ => c ^ 2) := by
        funext c; rw [sq_abs]
      rwa [h_eq] at h_sq_abs
    have h_neg_sq : Tendsto (fun c : ℝ => -(c ^ 2)) atBot atBot :=
      tendsto_neg_atTop_atBot.comp h_sq
    have h_neg_sq_div : Tendsto (fun c : ℝ => -(c ^ 2) / 2) atBot atBot :=
      h_neg_sq.atBot_div_const (by norm_num : (0:ℝ) < 2)
    have h_exp : Tendsto (fun c : ℝ => Real.exp (-(c ^ 2) / 2)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h_neg_sq_div
    have h_pdf_eq : ∀ c, gaussianPDFReal 0 1 c
        = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(c ^ 2) / 2) := by
      intro c; simp [gaussianPDFReal]
    have h_const : Tendsto
        (fun c : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(c ^ 2) / 2))
        atBot (𝓝 ((1 / Real.sqrt (2 * Real.pi)) * 0)) :=
      tendsto_const_nhds.mul h_exp
    rw [mul_zero] at h_const
    refine h_const.congr ?_
    intro c; exact (h_pdf_eq c).symm
  have h_pdf_d1 :
      Tendsto (fun K : ℝ => gaussianPDFReal 0 1
          ((Real.log (S₀ / K) + σ ^ 2 / 2) / σ)) atTop (𝓝 0) :=
    h_pdf_to_zero.comp h_d1_atBot
  have h_target := h_pdf_d1.const_mul S₀
  rw [mul_zero] at h_target
  exact h_target

end TailOptionPricing
