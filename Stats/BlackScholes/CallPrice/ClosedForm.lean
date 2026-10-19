module

/-
  Lognormal call closed forms for arXiv:1908.02347v3, Arbitrage Boundaries.
  The logarithmic and standard-normal formulas use strictly positive spot
  and strike and nonzero Gaussian variance.
-/
public import Stats.BlackScholes.CallPrice.Basic
public import Stats.BlackScholes.StdNormal

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

/-! ### Black–Scholes closed form via Gaussian completing-the-square. -/

open ProbabilityTheory MeasureTheory in
/-- **Volume conversion of `gaussianReal` set integral.**  For `v ≠ 0`,
        `∫_{s} g(x) ∂(𝒩(μ, v)) = ∫_{s} φ_{μ,v}(x) · g(x) dx`.
    Set-integral analogue of `integral_gaussianReal_eq_integral_smul`. -/
theorem setIntegral_gaussianReal_eq_setIntegral_pdf_mul {μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(gaussianReal μ v) =
    ∫ x in s, gaussianPDFReal μ v x * g x ∂volume := by
  rw [gaussianReal_of_var_ne_zero μ hv]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
        (measurable_gaussianPDF μ v)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))
        g hs]
  refine setIntegral_congr_fun hs (fun x _ => ?_)
  rw [smul_eq_mul, toReal_gaussianPDF]

open ProbabilityTheory MeasureTheory in
/-- **Restricted exponential moment of a Gaussian.**  For `X ∼ 𝒩(μ, v)` with
    `v ≠ 0` and any `c : ℝ`:
        `∫_{Ioi c} exp(x) ∂(𝒩(μ, v)) = exp(μ + v/2) · 𝒩(μ+v, v)(Ioi c)`.
    Esscher consequence of `gaussianPDFReal_exp_tilt`. -/
theorem setIntegral_Ioi_exp_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    ∫ x in Set.Ioi c, Real.exp x ∂(gaussianReal μ v) =
    Real.exp (μ + (v : ℝ) / 2) *
      (gaussianReal (μ + (v : ℝ)) v).real (Set.Ioi c) := by
  rw [setIntegral_gaussianReal_eq_setIntegral_pdf_mul hv _ measurableSet_Ioi]
  have h_tilt_eq : ∫ x in Set.Ioi c, gaussianPDFReal μ v x * Real.exp x ∂volume =
      ∫ x in Set.Ioi c,
        Real.exp (μ + (v : ℝ) / 2) *
          gaussianPDFReal (μ + (v : ℝ)) v x ∂volume := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    have h := gaussianPDFReal_exp_tilt (μ := μ) hv 1 x
    rw [show (1 : ℝ) * x = x from by ring,
        show μ * 1 = μ from by ring,
        show (v : ℝ) * (1 : ℝ)^2 / 2 = (v : ℝ) / 2 from by ring,
        show μ + (v : ℝ) * 1 = μ + (v : ℝ) from by ring] at h
    rw [mul_comm (gaussianPDFReal μ v x) (Real.exp x), h]
  rw [h_tilt_eq, MeasureTheory.integral_const_mul]
  congr 1
  show ∫ x in Set.Ioi c, gaussianPDFReal (μ + (v : ℝ)) v x ∂volume =
       ((gaussianReal (μ + (v : ℝ)) v) (Set.Ioi c)).toReal
  rw [gaussianReal_apply_eq_integral _ hv,
      ENNReal.toReal_ofReal (by
        apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
        intro x _; exact gaussianPDFReal_nonneg _ v x)]

open ProbabilityTheory MeasureTheory in
/-- **Decomposition of the Black–Scholes call price.**  For `S_T = S₀ · exp X`
    with `X ∼ 𝒩(μ, v)` (`v ≠ 0`) and strike `K > 0`:
        `BSC(K) = S₀ · exp(μ + v/2) · 𝒩(μ+v, v)(Ioi (log(K/S₀)))
                  − K · 𝒩(μ, v)(Ioi (log(K/S₀)))`. -/
theorem callPriceBS_decompose
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ μ v K =
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      (gaussianReal (μ + (v : ℝ)) v).real
        (Set.Ioi (Real.log (K / S₀))) -
    K * (gaussianReal μ v).real (Set.Ioi (Real.log (K / S₀))) := by
  set c := Real.log (K / S₀) with hc_def
  have hKS₀ : 0 < K / S₀ := div_pos hK hS₀
  rw [callPriceBS_eq_expectation]
  have h_payoff_eq : ∀ x : ℝ, max (S₀ * Real.exp x - K) 0 =
      Set.indicator (Set.Ioi c) (fun y => S₀ * Real.exp y - K) x := by
    intro x
    by_cases hx : x ∈ Set.Ioi c
    · have hxc : c < x := hx
      have h_exp_gt : K < S₀ * Real.exp x := by
        rw [hc_def, Real.log_lt_iff_lt_exp hKS₀] at hxc
        rw [div_lt_iff₀ hS₀] at hxc
        linarith
      rw [Set.indicator_of_mem hx]
      exact max_eq_left (sub_nonneg.mpr h_exp_gt.le)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_Ioi, not_lt] at hx
      have h_exp_le : S₀ * Real.exp x ≤ K := by
        have h_exp_le_exp : Real.exp x ≤ Real.exp c := Real.exp_le_exp.mpr hx
        rw [hc_def, Real.exp_log hKS₀] at h_exp_le_exp
        have h_mul : S₀ * Real.exp x ≤ S₀ * (K / S₀) :=
          mul_le_mul_of_nonneg_left h_exp_le_exp hS₀.le
        rwa [mul_div_cancel₀ K hS₀.ne'] at h_mul
      exact max_eq_right (sub_nonpos.mpr h_exp_le)
  rw [show (fun x => max (S₀ * Real.exp x - K) 0) =
        Set.indicator (Set.Ioi c) (fun y => S₀ * Real.exp y - K) from
      funext h_payoff_eq]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  have h_int_exp : Integrable (fun x : ℝ => Real.exp x) (gaussianReal μ v) := by
    simpa using integrable_exp_mul_gaussianReal (μ := μ) (v := v) 1
  have h_int_S₀exp : Integrable (fun x : ℝ => S₀ * Real.exp x) (gaussianReal μ v) :=
    h_int_exp.const_mul S₀
  have h_int_const : Integrable (fun _ : ℝ => K) (gaussianReal μ v) :=
    integrable_const K
  rw [MeasureTheory.integral_sub h_int_S₀exp.integrableOn h_int_const.integrableOn]
  rw [MeasureTheory.integral_const_mul S₀ Real.exp]
  rw [setIntegral_const]
  rw [setIntegral_Ioi_exp_gaussianReal hv]
  rw [smul_eq_mul, mul_comm ((gaussianReal μ v).real (Set.Ioi c)) K]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes call price closed form (general parametrisation).**
    For `S_T = S₀ · exp X` with `X ∼ 𝒩(μ, v)` (`v ≠ 0`) and strike `K > 0`:
        `BSC(K) = S₀ · exp(μ + v/2) · (1 − Φ((log(K/S₀) − μ − v)/√v))
                  − K · (1 − Φ((log(K/S₀) − μ)/√v))`. -/
theorem callPriceBS_closed_form_general
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ μ v K =
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      (1 - stdNormalCdf
        ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ))) -
    K * (1 - stdNormalCdf
      ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ))) := by
  rw [callPriceBS_decompose hS₀ hv hK]
  have h_first :
      (gaussianReal (μ + (v : ℝ)) v).real (Set.Ioi (Real.log (K / S₀))) =
      1 - stdNormalCdf
        ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ)) := by
    rw [gaussianReal_real_Ioi_eq hv, ← one_sub_stdNormalCdf]
    congr 2; ring
  have h_second :
      (gaussianReal μ v).real (Set.Ioi (Real.log (K / S₀))) =
      1 - stdNormalCdf
        ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ)) := by
    rw [gaussianReal_real_Ioi_eq hv, ← one_sub_stdNormalCdf]
  rw [h_first, h_second]

open ProbabilityTheory MeasureTheory in
/-- **Black–Scholes closed form, risk-neutral / zero-rate parametrisation.**
    Specialising to `μ = −v/2`:
        `BSC(K) = S₀ · Φ(d₁) − K · Φ(d₂)`,
    with `d₁ = (log(S₀/K) + v/2)/√v` and `d₂ = (log(S₀/K) − v/2)/√v`. -/
theorem callPriceBS_closed_form_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ (-((v : ℝ) / 2)) v K =
    S₀ * stdNormalCdf
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) -
    K * stdNormalCdf
      ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
  rw [callPriceBS_closed_form_general hS₀ hv hK]
  have h_exp_zero : Real.exp (-((v : ℝ) / 2) + (v : ℝ) / 2) = 1 := by
    rw [show -((v : ℝ) / 2) + (v : ℝ) / 2 = 0 from by ring, Real.exp_zero]
  rw [h_exp_zero, mul_one]
  have hKS₀_pos : 0 < K / S₀ := div_pos hK hS₀
  have h_log_neg : Real.log (S₀ / K) = -Real.log (K / S₀) := by
    rw [← Real.log_inv, inv_div]
  have h_arg1 : (Real.log (K / S₀) - -((v : ℝ) / 2) - (v : ℝ)) /
                Real.sqrt (v : ℝ) =
                -((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
    rw [h_log_neg]; field_simp; ring
  have h_arg2 : (Real.log (K / S₀) - -((v : ℝ) / 2)) / Real.sqrt (v : ℝ) =
                -((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
    rw [h_log_neg]; field_simp; ring
  rw [h_arg1, h_arg2]
  rw [stdNormalCdf_neg, stdNormalCdf_neg]
  ring

open ProbabilityTheory MeasureTheory in
/-- **Risk-neutral lognormal survival in `Φ(d₂)` form.**  Under risk-neutral
    parametrisation `μ = −v/2`,
        `survivalLN S₀ (−v/2) v K = Φ(d₂(K))`,
    where `d₂(K) = (log(S₀/K) − v/2)/√v`. -/
theorem survivalLN_riskNeutral_eq_stdNormalCdf
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    survivalLN S₀ (-((v : ℝ) / 2)) v K =
    stdNormalCdf ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
  rw [survivalLN_eq_one_sub_stdNormalCdf hS₀ hv hK]
  have h_log_neg : Real.log (S₀ / K) = -Real.log (K / S₀) := by
    rw [← Real.log_inv, inv_div]
  have h_arg : (Real.log (K / S₀) - -((v : ℝ) / 2)) / Real.sqrt (v : ℝ) =
                -((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
    rw [h_log_neg]; field_simp; ring
  rw [h_arg, stdNormalCdf_neg]
  ring

end TailOptionPricing
