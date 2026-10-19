module

/-
  Smile correction in Eq. (10).

  When the Black–Scholes volatility `σ` depends on the strike `K`, the total
  derivative of `BSC(K, σ(K))` in `K` picks up a chain-rule contribution:
        d/dK BSC = ∂BSC/∂K + ∂BSC/∂σ · σ'(K)
                 = −Φ(d₂)   + S₀·φ(d₁) · σ'(K)
  where the second term is the "smile correction" of the paper.

  Here `σ` denotes total volatility. At time to expiry `t`, annual volatility
  is multiplied by `sqrt t`; Stats.BlackScholes.ReturnsSmile carries that
  factor through the strike derivative and the returns-tail bound.
  The theorem `callPriceBS_σ_eq_callPriceBS_riskNeutral` below connects this
  real-valued parametrization to the integral-defined lognormal call price.
-/
public import Stats.BlackScholes.Greeks
public import Stats.BlackScholes.Erfc

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

/-- **`σ`-parametric Black–Scholes call price (closed form).**
    `S₀ · Φ(d₁(σ, K)) − K · Φ(d₂(σ, K))`,
    with `d₁ = (log(S₀/K) + σ²/2)/σ`, `d₂ = (log(S₀/K) − σ²/2)/σ`.
    This total closed-form expression represents a call price on the
    positive-spot, positive-strike, positive-volatility domain proved by
    `callPriceBS_σ_eq_callPriceBS_riskNeutral`. For boundary values use the
    actual-law `callPriceBS`, which includes the zero-variance payoff. -/
noncomputable def callPriceBS_σ (S₀ : ℝ) (σ : ℝ) (K : ℝ) : ℝ :=
  S₀ * stdNormalCdf ((Real.log (S₀ / K) + σ^2 / 2) / σ) -
  K * stdNormalCdf ((Real.log (S₀ / K) - σ^2 / 2) / σ)

open ProbabilityTheory MeasureTheory in
/-- **σ-form of the BS PDF identity.**
        `S₀ · φ((log(S₀/K) + σ²/2)/σ) = K · φ((log(S₀/K) − σ²/2)/σ)`
    for `σ > 0`.  Mirrors `bs_pdf_identity` with `√v` replaced by `σ` directly. -/
theorem bs_pdf_identity_σ {S₀ K σ : ℝ}
    (hS₀ : 0 < S₀) (hσ : 0 < σ) (hK : 0 < K) :
    S₀ * gaussianPDFReal 0 1 ((Real.log (S₀ / K) + σ^2 / 2) / σ) =
    K * gaussianPDFReal 0 1 ((Real.log (S₀ / K) - σ^2 / 2) / σ) := by
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_pdf : ∀ c : ℝ, gaussianPDFReal 0 1 c =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(c^2) / 2) := by
    intro c; simp [gaussianPDFReal, NNReal.coe_one]
  rw [h_pdf, h_pdf]
  set a : ℝ := Real.log (S₀ / K) with ha_def
  rw [show S₀ * (1 / Real.sqrt (2 * Real.pi) *
        Real.exp (-((a + σ^2 / 2) / σ)^2 / 2)) =
        (1 / Real.sqrt (2 * Real.pi)) *
          (S₀ * Real.exp (-((a + σ^2 / 2) / σ)^2 / 2)) from by ring,
      show K * (1 / Real.sqrt (2 * Real.pi) *
        Real.exp (-((a - σ^2 / 2) / σ)^2 / 2)) =
        (1 / Real.sqrt (2 * Real.pi)) *
          (K * Real.exp (-((a - σ^2 / 2) / σ)^2 / 2)) from by ring]
  congr 1
  rw [show S₀ = Real.exp (Real.log S₀) from (Real.exp_log hS₀).symm,
      show K = Real.exp (Real.log K) from (Real.exp_log hK).symm,
      ← Real.exp_add, ← Real.exp_add]
  congr 1
  have ha_eq : Real.log S₀ - Real.log K = a := by
    rw [ha_def, Real.log_div hS₀.ne' hK.ne']
  have h_sq_diff : ((a + σ^2 / 2) / σ)^2 - ((a - σ^2 / 2) / σ)^2 = 2 * a := by
    field_simp
    ring
  linarith [ha_eq, h_sq_diff]

open ProbabilityTheory MeasureTheory in
/-- **Smile-corrected Greek (Eq. 10's chain-rule contribution).**
    For `S₀ > 0`, `K₀ > 0`, and a strike-dependent volatility `σ : ℝ → ℝ`
    with `σ(K₀) > 0` and `HasDerivAt σ σ' K₀`, the total derivative of
    the smile-aware BSC at `K = K₀` is
        `d/dK [BSC(K, σ(K))] = −Φ(d₂(σ(K₀), K₀)) + S₀ · φ(d₁(σ(K₀), K₀)) · σ'(K₀)`,
    where the second term is the paper's smile correction. -/
theorem callPriceBS_σ_smile_hasDerivAt
    {S₀ K₀ : ℝ} (hS₀ : 0 < S₀) (hK : 0 < K₀)
    {σ : ℝ → ℝ} {σ' : ℝ} (hσ_pos : 0 < σ K₀)
    (hσ_deriv : HasDerivAt σ σ' K₀) :
    HasDerivAt (fun K => callPriceBS_σ S₀ (σ K) K)
      (-stdNormalCdf ((Real.log (S₀ / K₀) - (σ K₀)^2 / 2) / σ K₀) +
       S₀ * gaussianPDFReal 0 1
         ((Real.log (S₀ / K₀) + (σ K₀)^2 / 2) / σ K₀) * σ') K₀ := by
  have hK_ne : K₀ ≠ 0 := hK.ne'
  have hσK_ne : σ K₀ ≠ 0 := hσ_pos.ne'
  have hσK_sq_pos : 0 < (σ K₀)^2 := pow_pos hσ_pos 2
  -- d/dK[log(S₀/K)] = -1/K
  have h_log_deriv : HasDerivAt (fun K : ℝ => Real.log (S₀ / K)) (-1 / K₀) K₀ := by
    have h_log_K : HasDerivAt Real.log (1 / K₀) K₀ := by
      have := Real.hasDerivAt_log hK_ne; rwa [one_div]
    have h_diff : HasDerivAt (fun K : ℝ => Real.log S₀ - Real.log K)
        (0 - 1 / K₀) K₀ := (hasDerivAt_const K₀ _).sub h_log_K
    have h_ev : (fun K : ℝ => Real.log (S₀ / K)) =ᶠ[𝓝 K₀]
        (fun K : ℝ => Real.log S₀ - Real.log K) := by
      filter_upwards [eventually_gt_nhds hK] with K hK_pos
      rw [Real.log_div hS₀.ne' hK_pos.ne']
    have h := h_diff.congr_of_eventuallyEq h_ev
    convert h using 1; ring
  -- d/dK[σ(K)²] = 2·σ(K₀)·σ'
  have h_sq_σ : HasDerivAt (fun K => (σ K)^2) (2 * σ K₀ * σ') K₀ := by
    have h := hσ_deriv.pow 2
    convert h using 1; ring
  -- d/dK[σ(K)²/2] = σ(K₀)·σ'
  have h_sq_σ_half : HasDerivAt (fun K => (σ K)^2 / 2) (σ K₀ * σ') K₀ := by
    have h := h_sq_σ.div_const 2
    convert h using 1; ring
  -- Numerator derivatives.
  have h_num_d1 : HasDerivAt (fun K => Real.log (S₀ / K) + (σ K)^2 / 2)
      (-1 / K₀ + σ K₀ * σ') K₀ := h_log_deriv.add h_sq_σ_half
  have h_num_d2 : HasDerivAt (fun K => Real.log (S₀ / K) - (σ K)^2 / 2)
      (-1 / K₀ - σ K₀ * σ') K₀ := h_log_deriv.sub h_sq_σ_half
  -- Quotient rule for d₁ and d₂.
  have h_d1_deriv : HasDerivAt
      (fun K => (Real.log (S₀ / K) + (σ K)^2 / 2) / σ K)
      (((-1 / K₀ + σ K₀ * σ') * σ K₀ -
        (Real.log (S₀ / K₀) + (σ K₀)^2 / 2) * σ') / (σ K₀)^2) K₀ :=
    h_num_d1.div hσ_deriv hσK_ne
  have h_d2_deriv : HasDerivAt
      (fun K => (Real.log (S₀ / K) - (σ K)^2 / 2) / σ K)
      (((-1 / K₀ - σ K₀ * σ') * σ K₀ -
        (Real.log (S₀ / K₀) - (σ K₀)^2 / 2) * σ') / (σ K₀)^2) K₀ :=
    h_num_d2.div hσ_deriv hσK_ne
  -- Chain rule: Φ ∘ d₁ and Φ ∘ d₂.
  set d₁K₀ : ℝ := (Real.log (S₀ / K₀) + (σ K₀)^2 / 2) / σ K₀ with hd₁_def
  set d₂K₀ : ℝ := (Real.log (S₀ / K₀) - (σ K₀)^2 / 2) / σ K₀ with hd₂_def
  set δ₁ : ℝ := ((-1 / K₀ + σ K₀ * σ') * σ K₀ -
        (Real.log (S₀ / K₀) + (σ K₀)^2 / 2) * σ') / (σ K₀)^2 with hδ₁_def
  set δ₂ : ℝ := ((-1 / K₀ - σ K₀ * σ') * σ K₀ -
        (Real.log (S₀ / K₀) - (σ K₀)^2 / 2) * σ') / (σ K₀)^2 with hδ₂_def
  have h_Φd1 : HasDerivAt
      (fun K => stdNormalCdf ((Real.log (S₀ / K) + (σ K)^2 / 2) / σ K))
      (gaussianPDFReal 0 1 d₁K₀ * δ₁) K₀ :=
    (stdNormalCdf_hasDerivAt _).comp K₀ h_d1_deriv
  have h_Φd2 : HasDerivAt
      (fun K => stdNormalCdf ((Real.log (S₀ / K) - (σ K)^2 / 2) / σ K))
      (gaussianPDFReal 0 1 d₂K₀ * δ₂) K₀ :=
    (stdNormalCdf_hasDerivAt _).comp K₀ h_d2_deriv
  -- S₀·Φ(d₁) and K·Φ(d₂) via const_mul / product rule.
  have h_S₀_Φd1 : HasDerivAt
      (fun K => S₀ * stdNormalCdf ((Real.log (S₀ / K) + (σ K)^2 / 2) / σ K))
      (S₀ * (gaussianPDFReal 0 1 d₁K₀ * δ₁)) K₀ := h_Φd1.const_mul S₀
  have h_K_Φd2 : HasDerivAt
      (fun K => K * stdNormalCdf ((Real.log (S₀ / K) - (σ K)^2 / 2) / σ K))
      (1 * stdNormalCdf d₂K₀ + K₀ * (gaussianPDFReal 0 1 d₂K₀ * δ₂)) K₀ :=
    (hasDerivAt_id K₀).mul h_Φd2
  -- BSC = S₀·Φ(d₁) − K·Φ(d₂).
  have h_BSC := h_S₀_Φd1.sub h_K_Φd2
  -- Simplify the derivative value via `bs_pdf_identity_σ`.
  have h_pdf_id : S₀ * gaussianPDFReal 0 1 d₁K₀ =
      K₀ * gaussianPDFReal 0 1 d₂K₀ :=
    bs_pdf_identity_σ hS₀ hσ_pos hK
  have h_val :
      S₀ * (gaussianPDFReal 0 1 d₁K₀ * δ₁) -
        (1 * stdNormalCdf d₂K₀ + K₀ * (gaussianPDFReal 0 1 d₂K₀ * δ₂)) =
      -stdNormalCdf d₂K₀ +
        S₀ * gaussianPDFReal 0 1 d₁K₀ * σ' := by
    -- Substitute δ₁, δ₂ and use h_pdf_id.
    rw [hδ₁_def, hδ₂_def, hd₁_def, hd₂_def]
    set a : ℝ := Real.log (S₀ / K₀) with ha_def
    set s : ℝ := σ K₀ with hs_def
    set Φd₂ : ℝ := stdNormalCdf ((a - s^2 / 2) / s) with hΦd₂_def
    set φd₁ : ℝ := gaussianPDFReal 0 1 ((a + s^2 / 2) / s) with hφd₁_def
    set φd₂ : ℝ := gaussianPDFReal 0 1 ((a - s^2 / 2) / s) with hφd₂_def
    -- h_pdf_id : S₀·φd₁ = K₀·φd₂
    have h_id : S₀ * φd₁ = K₀ * φd₂ := h_pdf_id
    -- LHS = S₀·φd₁·δ₁ - Φd₂ - K₀·φd₂·δ₂
    -- where δ₁ = ((-1/K₀ + s·σ')·s - (a + s²/2)·σ')/s²
    --       δ₂ = ((-1/K₀ - s·σ')·s - (a - s²/2)·σ')/s²
    -- Goal: LHS = -Φd₂ + S₀·φd₁·σ'
    -- Multiply numerators and use the bs_pdf_identity to cancel.
    have hs_ne : s ≠ 0 := hσK_ne
    have hs_sq_ne : s^2 ≠ 0 := pow_ne_zero 2 hs_ne
    -- Massage the LHS into a polynomial expression in S₀·φd₁ and K₀·φd₂,
    -- then substitute h_id.
    have h_lhs_expand :
        S₀ * (φd₁ * (((-1 / K₀ + s * σ') * s - (a + s^2 / 2) * σ') / s^2)) -
          (1 * Φd₂ +
           K₀ * (φd₂ * (((-1 / K₀ - s * σ') * s - (a - s^2 / 2) * σ') / s^2))) =
        -Φd₂ +
          (S₀ * φd₁ - K₀ * φd₂) * ((-1 / K₀) / s) +
          (S₀ * φd₁ + K₀ * φd₂) * (σ' / 2) +
          (S₀ * φd₁ - K₀ * φd₂) * (-(a * σ') / s^2) := by
      field_simp
      ring
    rw [h_lhs_expand]
    -- Use h_id to make the (S₀·φd₁ - K₀·φd₂) terms vanish, and
    -- (S₀·φd₁ + K₀·φd₂) = 2·S₀·φd₁.
    have h_diff : S₀ * φd₁ - K₀ * φd₂ = 0 := by linarith
    have h_sum : S₀ * φd₁ + K₀ * φd₂ = 2 * (S₀ * φd₁) := by linarith
    rw [h_diff, h_sum]
    ring
  rw [← h_val]
  -- Show that the function `fun K => callPriceBS_σ S₀ (σ K) K` equals
  -- `fun K => S₀·Φ(d₁(K)) − K·Φ(d₂(K))` (this is just the def of callPriceBS_σ).
  exact h_BSC

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes Vega** (σ-parametric form, fixed strike).
    `∂/∂σ [BSC_σ(S₀, σ, K)] = S₀ · φ(d₁(σ, K))` at any positive `σ₀`,
    where `d₁ = (log(S₀/K) + σ²/2)/σ`.  This is the standard "vega"
    sensitivity; the formula falls out of `bs_pdf_identity_σ` after
    applying the quotient rule to `d₁` and `d₂` w.r.t. `σ`. -/
theorem callPriceBS_σ_vega_hasDerivAt
    {S₀ K σ₀ : ℝ} (hS₀ : 0 < S₀) (hσ : 0 < σ₀) (hK : 0 < K) :
    HasDerivAt (fun σ => callPriceBS_σ S₀ σ K)
      (S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + σ₀^2 / 2) / σ₀)) σ₀ := by
  have hσ_ne : σ₀ ≠ 0 := hσ.ne'
  have hσ_sq_ne : σ₀^2 ≠ 0 := pow_ne_zero 2 hσ_ne
  -- d/dσ[σ²/2] = σ
  have h_id : HasDerivAt (fun σ : ℝ => σ) 1 σ₀ := hasDerivAt_id' σ₀
  have h_sq_σ_half : HasDerivAt (fun σ : ℝ => σ^2 / 2) σ₀ σ₀ := by
    have h := (h_id.pow 2).div_const 2
    convert h using 1; ring
  have h_const : HasDerivAt (fun _ : ℝ => Real.log (S₀ / K)) 0 σ₀ :=
    hasDerivAt_const σ₀ _
  have h_num_d1 :
      HasDerivAt (fun σ : ℝ => Real.log (S₀ / K) + σ^2 / 2) σ₀ σ₀ := by
    have := h_const.add h_sq_σ_half; convert this using 1; ring
  have h_num_d2 :
      HasDerivAt (fun σ : ℝ => Real.log (S₀ / K) - σ^2 / 2) (-σ₀) σ₀ := by
    have := h_const.sub h_sq_σ_half; convert this using 1; ring
  have h_d1_deriv : HasDerivAt
      (fun σ : ℝ => (Real.log (S₀ / K) + σ^2 / 2) / σ)
      ((σ₀ * σ₀ - (Real.log (S₀ / K) + σ₀^2 / 2)) / σ₀^2) σ₀ := by
    have h := h_num_d1.div h_id hσ_ne
    convert h using 1; ring
  have h_d2_deriv : HasDerivAt
      (fun σ : ℝ => (Real.log (S₀ / K) - σ^2 / 2) / σ)
      (((-σ₀) * σ₀ - (Real.log (S₀ / K) - σ₀^2 / 2)) / σ₀^2) σ₀ := by
    have h := h_num_d2.div h_id hσ_ne
    convert h using 1; ring
  set d₁σ₀ : ℝ := (Real.log (S₀ / K) + σ₀^2 / 2) / σ₀ with hd₁_def
  set d₂σ₀ : ℝ := (Real.log (S₀ / K) - σ₀^2 / 2) / σ₀ with hd₂_def
  set δ₁ : ℝ := (σ₀ * σ₀ - (Real.log (S₀ / K) + σ₀^2 / 2)) / σ₀^2 with hδ₁_def
  set δ₂ : ℝ := ((-σ₀) * σ₀ - (Real.log (S₀ / K) - σ₀^2 / 2)) / σ₀^2 with hδ₂_def
  have h_Φd1 : HasDerivAt
      (fun σ : ℝ => stdNormalCdf ((Real.log (S₀ / K) + σ^2 / 2) / σ))
      (gaussianPDFReal 0 1 d₁σ₀ * δ₁) σ₀ :=
    (stdNormalCdf_hasDerivAt _).comp σ₀ h_d1_deriv
  have h_Φd2 : HasDerivAt
      (fun σ : ℝ => stdNormalCdf ((Real.log (S₀ / K) - σ^2 / 2) / σ))
      (gaussianPDFReal 0 1 d₂σ₀ * δ₂) σ₀ :=
    (stdNormalCdf_hasDerivAt _).comp σ₀ h_d2_deriv
  have h_S₀_Φd1 := h_Φd1.const_mul S₀
  have h_K_Φd2 := h_Φd2.const_mul K
  have h_BSC := h_S₀_Φd1.sub h_K_Φd2
  -- Use bs_pdf_identity_σ to simplify the derivative.
  have h_pdf_id : S₀ * gaussianPDFReal 0 1 d₁σ₀ = K * gaussianPDFReal 0 1 d₂σ₀ :=
    bs_pdf_identity_σ hS₀ hσ hK
  have h_val :
      S₀ * (gaussianPDFReal 0 1 d₁σ₀ * δ₁) -
        K * (gaussianPDFReal 0 1 d₂σ₀ * δ₂) =
      S₀ * gaussianPDFReal 0 1 d₁σ₀ := by
    have h_swap :
        K * (gaussianPDFReal 0 1 d₂σ₀ * δ₂) =
        S₀ * (gaussianPDFReal 0 1 d₁σ₀ * δ₂) := by
      have h_id : K * gaussianPDFReal 0 1 d₂σ₀ = S₀ * gaussianPDFReal 0 1 d₁σ₀ :=
        h_pdf_id.symm
      calc K * (gaussianPDFReal 0 1 d₂σ₀ * δ₂)
          = (K * gaussianPDFReal 0 1 d₂σ₀) * δ₂ := by ring
        _ = (S₀ * gaussianPDFReal 0 1 d₁σ₀) * δ₂ := by rw [h_id]
        _ = S₀ * (gaussianPDFReal 0 1 d₁σ₀ * δ₂) := by ring
    rw [h_swap, show S₀ * (gaussianPDFReal 0 1 d₁σ₀ * δ₁) -
           S₀ * (gaussianPDFReal 0 1 d₁σ₀ * δ₂) =
        S₀ * gaussianPDFReal 0 1 d₁σ₀ * (δ₁ - δ₂) from by ring]
    rw [hδ₁_def, hδ₂_def]
    have h_diff :
        (σ₀ * σ₀ - (Real.log (S₀ / K) + σ₀^2 / 2)) / σ₀^2 -
          ((-σ₀) * σ₀ - (Real.log (S₀ / K) - σ₀^2 / 2)) / σ₀^2 = 1 := by
      field_simp; ring
    rw [h_diff, mul_one]
  rw [← h_val]
  exact h_BSC

open ProbabilityTheory MeasureTheory in
/-- **Connection between the two BS development branches.**  The σ-parametric
    closed form `callPriceBS_σ S₀ σ K` (real-valued `σ`) coincides with the
    abstract `callPriceBS S₀ (−v/2) v K` (NNReal-valued `v`) when
    `σ = √v`, i.e., `v = σ²`.

    This formalises that the two BS development branches in this codebase
    agree on the risk-neutral closed form. -/
theorem callPriceBS_σ_eq_callPriceBS_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS_σ S₀ (Real.sqrt (v : ℝ)) K =
      callPriceBS S₀ (-((v : ℝ) / 2)) v K := by
  rw [callPriceBS_closed_form_riskNeutral hS₀ hv hK]
  unfold callPriceBS_σ
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have h_sq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := by
    rw [sq, Real.mul_self_sqrt hv_pos.le]
  rw [h_sq]

open ProbabilityTheory MeasureTheory in
/-- **Conditional price-tail bound for a supplied digital inequality.**
    This algebraic helper assumes `h_no_arb`; it does not derive that input
    from a differentiable smile or a matched butterfly. Its tail model is
    `(l / K)^α`. The final returns-tail bound in arXiv:1908.02347v3,
    "Arbitrage Boundaries", is proved by
    `alpha_lower_bound_returns_smile_erfc` in Stats.BlackScholes.ReturnsSmile. -/
theorem alpha_lower_bound_smile_erfc
    {l α S₀ K₁ σ' : ℝ} {σ : ℝ → ℝ}
    (hl : 0 < l) (hK₁ : l < K₁)
    (h_no_arb : (l / K₁) ^ α ≤
      (1/2) * erfc ((Real.log (K₁ / S₀) + (σ K₁) ^ 2 / 2) /
        (σ K₁ * Real.sqrt 2)) -
      S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K₁) + (σ K₁) ^ 2 / 2) / σ K₁) * σ') :
    Real.log
        ((1/2) * erfc ((Real.log (K₁ / S₀) + (σ K₁) ^ 2 / 2) /
            (σ K₁ * Real.sqrt 2)) -
          S₀ * gaussianPDFReal 0 1
            ((Real.log (S₀ / K₁) + (σ K₁) ^ 2 / 2) / σ K₁) * σ') /
      Real.log (l / K₁) ≤ α :=
  alpha_lower_bound hl hK₁ h_no_arb

end TailOptionPricing
