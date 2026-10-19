module

/-
  Black–Scholes Greeks under risk-neutral parametrisation.

  • K-derivative `∂BSC/∂K = −Φ(d₂(K))` from the layer-cake form.
  • Martingale property `E[exp(X)] = 1` under `μ = −v/2`.
  • The BS PDF identity `S₀·φ(d₁) = K·φ(d₂)`, completing-the-square kernel.
  • Delta `∂BSC/∂S₀ = Φ(d₁(S₀, K))`.
  • Gamma (= `∂Δ/∂S₀ = φ(d₁) / (S₀·√v)`).
  • Risk-neutral specialisation of the BSC tail dominance Eq. (9):
    `(l/K₁)^α ≤ Φ(d₂(K₁))`.
  • Algebraic put-form `callPriceBS − S₀ + K = K·Φ(−d₂) − S₀·Φ(−d₁)`
    (the BS put formula stated without defining the put price).
-/
public import Stats.BlackScholes.CallPrice

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral Black–Scholes Greek (delta-of-cash).**  Under risk-neutral
    parametrisation `μ = −v/2`, the strike-derivative of the call price is
        `∂BSC/∂K = −Φ(d₂(K))`,
    where `d₂(K) = (log(S₀/K) − v/2)/√v`. -/
theorem callPriceBS_riskNeutral_hasDerivAt_stdNormalCdf
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt (callPriceBS S₀ (-((v : ℝ) / 2)) v)
      (-stdNormalCdf
        ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) K := by
  have h : HasDerivAt (callPriceBS S₀ (-((v : ℝ) / 2)) v)
      (-(survivalLN S₀ (-((v : ℝ) / 2)) v K)) K :=
    callPriceBS_hasDerivAt hS₀ hv hK
  rwa [survivalLN_riskNeutral_eq_stdNormalCdf hS₀ hv hK] at h

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral martingale property of the spot.**  Under risk-neutral
    parametrisation `μ = −v/2`,
        `∫ exp(x) ∂(𝒩(-v/2, v)) = 1`.
    Equivalently, `E[S_T] = S₀` for `S_T = S₀ · exp(X)`. -/
theorem integral_exp_gaussianReal_riskNeutral {v : ℝ≥0} :
    ∫ x, Real.exp x ∂(gaussianReal (-((v : ℝ) / 2)) v) = 1 := by
  have h := congrFun (mgf_id_gaussianReal (μ := -((v : ℝ) / 2)) (v := v)) 1
  have h_arg : -((v : ℝ) / 2) * 1 + (v : ℝ) * (1 : ℝ)^2 / 2 = 0 := by ring
  rw [h_arg, Real.exp_zero] at h
  show ∫ x, Real.exp x ∂(gaussianReal (-((v : ℝ) / 2)) v) = 1
  have h_mgf : mgf id (gaussianReal (-((v : ℝ) / 2)) v) 1 =
      ∫ x, Real.exp x ∂(gaussianReal (-((v : ℝ) / 2)) v) := by
    unfold mgf
    simp [id]
  rw [← h_mgf]; exact h

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes put price formula via put–call parity.**
        `P(K) = K · Φ(−d₂) − S₀ · Φ(−d₁) = callPriceBS − S₀ + K`,
    stated as the algebraic identity (no separate put-price definition). -/
theorem callPriceBS_riskNeutral_putForm
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ (-((v : ℝ) / 2)) v K - S₀ + K =
    K * stdNormalCdf
        (-((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) -
    S₀ * stdNormalCdf
      (-((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ))) := by
  rw [callPriceBS_closed_form_riskNeutral hS₀ hv hK,
      stdNormalCdf_neg, stdNormalCdf_neg]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes PDF identity.**  The completing-the-square fact
        `S₀ · φ(d₁) = K · φ(d₂)`,
    where `d₁ = (log(S₀/K) + v/2)/√v` and `d₂ = (log(S₀/K) − v/2)/√v`.
    Algebraic kernel for all standard BS Greeks. -/
theorem bs_pdf_identity
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) =
    K * gaussianPDFReal 0 1
      ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have h_sqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
  have h_sqrt_ne : Real.sqrt (v : ℝ) ≠ 0 := h_sqrt_pos.ne'
  have h_sqrt_sq : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
    Real.mul_self_sqrt hv_pos.le
  have h_pdf : ∀ c : ℝ, gaussianPDFReal 0 1 c =
      (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(c^2) / 2) := by
    intro c; simp [gaussianPDFReal, NNReal.coe_one]
  rw [h_pdf, h_pdf]
  set σ : ℝ := Real.sqrt (v : ℝ) with hσ_def
  set a : ℝ := Real.log (S₀ / K) with ha_def
  have hσ_ne : σ ≠ 0 := h_sqrt_ne
  have hσ_sq : σ * σ = (v : ℝ) := h_sqrt_sq
  rw [show S₀ * (1 / Real.sqrt (2 * Real.pi) *
        Real.exp (-((a + (v : ℝ) / 2) / σ)^2 / 2)) =
        (1 / Real.sqrt (2 * Real.pi)) *
          (S₀ * Real.exp (-((a + (v : ℝ) / 2) / σ)^2 / 2)) from by ring,
      show K * (1 / Real.sqrt (2 * Real.pi) *
        Real.exp (-((a - (v : ℝ) / 2) / σ)^2 / 2)) =
        (1 / Real.sqrt (2 * Real.pi)) *
          (K * Real.exp (-((a - (v : ℝ) / 2) / σ)^2 / 2)) from by ring]
  congr 1
  rw [show S₀ = Real.exp (Real.log S₀) from (Real.exp_log hS₀).symm,
      show K = Real.exp (Real.log K) from (Real.exp_log hK).symm,
      ← Real.exp_add, ← Real.exp_add]
  congr 1
  have ha_eq : Real.log S₀ - Real.log K = a := by
    rw [ha_def, Real.log_div hS₀.ne' hK.ne']
  have h_sq_diff : ((a + (v : ℝ) / 2) / σ)^2 - ((a - (v : ℝ) / 2) / σ)^2 =
      2 * a := by
    rw [show (v : ℝ) = σ * σ from hσ_sq.symm]
    field_simp
    ring
  linarith [ha_eq, h_sq_diff]

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes Delta** (risk-neutral, zero rates).
        `∂/∂S₀ [BSC(S₀, K)] = Φ(d₁(S₀, K))`,
    where `d₁ = (log(S₀/K) + v/2)/√v`. -/
theorem callPriceBS_riskNeutral_hasDerivAt_S₀
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt (fun S => callPriceBS S (-((v : ℝ) / 2)) v K)
      (stdNormalCdf
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ))) S₀ := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have h_sqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
  have h_sqrt_ne : Real.sqrt (v : ℝ) ≠ 0 := h_sqrt_pos.ne'
  have hS₀_ne : S₀ ≠ 0 := hS₀.ne'
  set σ := Real.sqrt (v : ℝ) with hσ_def
  have h_log_deriv : HasDerivAt (fun S : ℝ => Real.log (S / K)) (1 / S₀) S₀ := by
    have h_log_S : HasDerivAt Real.log (1 / S₀) S₀ := by
      have := Real.hasDerivAt_log hS₀_ne; rwa [one_div]
    have h_log_diff : HasDerivAt (fun S : ℝ => Real.log S - Real.log K)
        (1 / S₀) S₀ := h_log_S.sub_const _
    have h_ev : (fun S : ℝ => Real.log (S / K)) =ᶠ[𝓝 S₀]
        (fun S : ℝ => Real.log S - Real.log K) := by
      filter_upwards [eventually_gt_nhds hS₀] with S hS
      rw [Real.log_div hS.ne' hK.ne']
    exact h_log_diff.congr_of_eventuallyEq h_ev
  have h_d₁_deriv : HasDerivAt
      (fun S : ℝ => (Real.log (S / K) + (v : ℝ) / 2) / σ)
      (1 / (S₀ * σ)) S₀ := by
    have h := (h_log_deriv.add_const ((v : ℝ) / 2)).div_const σ
    convert h using 1; field_simp
  have h_d₂_deriv : HasDerivAt
      (fun S : ℝ => (Real.log (S / K) - (v : ℝ) / 2) / σ)
      (1 / (S₀ * σ)) S₀ := by
    have h := (h_log_deriv.sub_const ((v : ℝ) / 2)).div_const σ
    convert h using 1; field_simp
  have h_Φd₁_deriv : HasDerivAt
      (fun S : ℝ => stdNormalCdf
        ((Real.log (S / K) + (v : ℝ) / 2) / σ))
      (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) + (v : ℝ) / 2) / σ) *
        (1 / (S₀ * σ))) S₀ :=
    (stdNormalCdf_hasDerivAt _).comp S₀ h_d₁_deriv
  have h_Φd₂_deriv : HasDerivAt
      (fun S : ℝ => stdNormalCdf
        ((Real.log (S / K) - (v : ℝ) / 2) / σ))
      (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) - (v : ℝ) / 2) / σ) *
        (1 / (S₀ * σ))) S₀ :=
    (stdNormalCdf_hasDerivAt _).comp S₀ h_d₂_deriv
  have h_S_Φd₁ : HasDerivAt
      (fun S : ℝ => S * stdNormalCdf
        ((Real.log (S / K) + (v : ℝ) / 2) / σ))
      (1 * stdNormalCdf
          ((Real.log (S₀ / K) + (v : ℝ) / 2) / σ) +
       S₀ * (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) + (v : ℝ) / 2) / σ) *
        (1 / (S₀ * σ)))) S₀ :=
    (hasDerivAt_id S₀).mul h_Φd₁_deriv
  have h_K_Φd₂ : HasDerivAt
      (fun S : ℝ => K * stdNormalCdf
        ((Real.log (S / K) - (v : ℝ) / 2) / σ))
      (K * (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) - (v : ℝ) / 2) / σ) *
        (1 / (S₀ * σ)))) S₀ :=
    h_Φd₂_deriv.const_mul K
  have h_closed_deriv := h_S_Φd₁.sub h_K_Φd₂
  have h_pdf_id := bs_pdf_identity hS₀ hv hK
  set Φd₁ := stdNormalCdf ((Real.log (S₀ / K) + (v : ℝ) / 2) / σ)
  set φd₁ := gaussianPDFReal 0 1 ((Real.log (S₀ / K) + (v : ℝ) / 2) / σ)
  set φd₂ := gaussianPDFReal 0 1 ((Real.log (S₀ / K) - (v : ℝ) / 2) / σ)
  have h_val : 1 * Φd₁ + S₀ * (φd₁ * (1 / (S₀ * σ))) -
      K * (φd₂ * (1 / (S₀ * σ))) = Φd₁ := by
    have h1 : S₀ * (φd₁ * (1 / (S₀ * σ))) = φd₁ / σ := by
      field_simp
    have h2 : K * (φd₂ * (1 / (S₀ * σ))) = K * φd₂ / (S₀ * σ) := by ring
    have h3 : φd₁ / σ = (S₀ * φd₁) / (S₀ * σ) := by
      rw [mul_div_mul_left φd₁ σ hS₀_ne]
    rw [h1, h2, h3, h_pdf_id]
    ring
  rw [h_val] at h_closed_deriv
  have h_ev : (fun S => callPriceBS S (-((v : ℝ) / 2)) v K) =ᶠ[𝓝 S₀]
      (fun S : ℝ =>
      S * stdNormalCdf ((Real.log (S / K) + (v : ℝ) / 2) / σ) -
      K * stdNormalCdf ((Real.log (S / K) - (v : ℝ) / 2) / σ)) := by
    filter_upwards [eventually_gt_nhds hS₀] with S hS
    exact callPriceBS_closed_form_riskNeutral hS hv hK
  exact h_closed_deriv.congr_of_eventuallyEq h_ev

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes Gamma** (risk-neutral, zero rates).
        `Γ = ∂²BSC/∂S₀² = ∂Δ/∂S₀ = φ(d₁) / (S₀ · √v)`. -/
theorem callPriceBS_riskNeutral_gamma
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt
      (fun S => stdNormalCdf
        ((Real.log (S / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)))
      (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) /
        (S₀ * Real.sqrt (v : ℝ))) S₀ := by
  have hv_pos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hv)
  have h_sqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
  have h_sqrt_ne : Real.sqrt (v : ℝ) ≠ 0 := h_sqrt_pos.ne'
  have hS₀_ne : S₀ ≠ 0 := hS₀.ne'
  set σ := Real.sqrt (v : ℝ) with hσ_def
  have h_log_deriv : HasDerivAt (fun S : ℝ => Real.log (S / K)) (1 / S₀) S₀ := by
    have h_log_S : HasDerivAt Real.log (1 / S₀) S₀ := by
      have := Real.hasDerivAt_log hS₀_ne; rwa [one_div]
    have h_log_diff : HasDerivAt (fun S : ℝ => Real.log S - Real.log K)
        (1 / S₀) S₀ := h_log_S.sub_const _
    have h_ev : (fun S : ℝ => Real.log (S / K)) =ᶠ[𝓝 S₀]
        (fun S : ℝ => Real.log S - Real.log K) := by
      filter_upwards [eventually_gt_nhds hS₀] with S hS
      rw [Real.log_div hS.ne' hK.ne']
    exact h_log_diff.congr_of_eventuallyEq h_ev
  have h_d₁_deriv : HasDerivAt
      (fun S : ℝ => (Real.log (S / K) + (v : ℝ) / 2) / σ)
      (1 / (S₀ * σ)) S₀ := by
    have h := (h_log_deriv.add_const ((v : ℝ) / 2)).div_const σ
    convert h using 1; field_simp
  have h := (stdNormalCdf_hasDerivAt _).comp S₀ h_d₁_deriv
  convert h using 1
  · rfl
  · rw [div_eq_mul_inv, one_div, mul_comm]

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral specialisation of the BSC tail dominance theorem (Eq. 9).**
        `(l/K₁)^α ≤ Φ(d₂(K₁))`,
    where `d₂(K₁) = (log(S₀/K₁) − v/2)/√v`. -/
theorem BSC_riskNeutral_tail_dominates_at_match
    {l α S₀ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match :
        (∫ s in Set.Ioi K₁, survivalLN S₀ (-((v : ℝ) / 2)) v s) =
        callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) +
          (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ (-((v : ℝ) / 2)) v s)
          ≥ 2 * callPrice l α K₁) :
    (l / K₁) ^ α ≤
    stdNormalCdf
      ((Real.log (S₀ / K₁) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
  have h := BSC_lognormal_tail_dominates_at_match
    hα hl hK₁ hS₀ hv ha_pos ha_lt h_match h_butterfly
  rwa [survivalLN_riskNeutral_eq_stdNormalCdf hS₀ hv (hl.trans hK₁)] at h

end TailOptionPricing
