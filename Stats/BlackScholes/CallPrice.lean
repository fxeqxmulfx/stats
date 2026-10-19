module

/-
  Black–Scholes call price `callPriceBS` and its closed forms.

  • Layer-cake form `callPriceBS S₀ μ v K = ∫_K^∞ ℙ(S_T > s) ds`.
  • First-derivative Greek `∂BSC/∂K = −survivalLN(K)` (Breeden–Litzenberger).
  • Continuity in `K`.
  • Expectation form `callPriceBS = E_Q[(S_T − K)⁺]` via the layer-cake bridge.
  • Lognormal specialisation of the BSC tail-dominance theorem.
  • Volume conversion `setIntegral_gaussianReal_eq_setIntegral_pdf_mul`.
  • Restricted exponential moment `setIntegral_Ioi_exp_gaussianReal`.
  • `callPriceBS_decompose` and the closed forms (general + risk-neutral).
  • Risk-neutral survival in `Φ(d₂)` form.
-/
public import Stats.BlackScholes.StdNormal
public import Stats.LayerCake

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory in
/-- **Black–Scholes call price (zero rates) under risk-neutral lognormal**:
    `BSC(K) = ∫_K^∞ ℙ(S_T > s) ds`. -/
noncomputable def callPriceBS (S₀ μ : ℝ) (v : ℝ≥0) (K : ℝ) : ℝ :=
  ∫ s in Set.Ioi K, survivalLN S₀ μ v s

open ProbabilityTheory in
/-- **Breeden–Litzenberger for Black–Scholes.**  For the lognormal call price
    `BSC(K) = ∫_K^∞ ℙ(S_T > s) ds`, the first derivative is
    `∂BSC/∂K = −ℙ(S_T > K) = −survivalLN(K)`. -/
theorem callPriceBS_hasDerivAt {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hK : 0 < K) :
    HasDerivAt (callPriceBS S₀ μ v) (-(survivalLN S₀ μ v K)) K := by
  have hK_half_pos : 0 < K / 2 := by linarith
  have hK_half_lt : K / 2 < K := by linarith
  exact hasDerivAt_integral_Ioi hK_half_lt
    (integrableOn_survivalLN hS₀ hK_half_pos)
    ((survivalLN_continuousOn hS₀ v).mono (Set.Ioi_subset_Ioi hK_half_pos.le))

open ProbabilityTheory in
/-- **`BSC` is continuous in `K` on the positive half-line.** -/
theorem callPriceBS_continuousOn {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) :
    ContinuousOn (callPriceBS S₀ μ v) (Set.Ioi 0) :=
  fun _ hK => (callPriceBS_hasDerivAt hS₀ hK).continuousAt.continuousWithinAt

open ProbabilityTheory in
/-- **Derivative of the lognormal survival in the strike.**  Chain rule on
        `survivalLN s = ∫_{log(s/S₀)}^∞ φ_{μ,v}`,
    using FTC for the half-line and `d/ds[log(s/S₀)] = 1/s`. -/
theorem survivalLN_hasDerivAt {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hK : 0 < K) :
    HasDerivAt (survivalLN S₀ μ v)
      (-gaussianPDFReal μ v (Real.log (K / S₀)) / K) K := by
  have h_pdf_int : Integrable (gaussianPDFReal μ v) :=
    integrable_gaussianPDFReal μ v
  have h_pdf_cont : Continuous (gaussianPDFReal μ v) := by
    unfold gaussianPDFReal; fun_prop
  -- Outer FTC: f(c) = ∫_{Ioi c} φ has derivative -φ(c).
  have h_outer : HasDerivAt
      (fun c : ℝ => ∫ x in Set.Ioi c, gaussianPDFReal μ v x)
      (-gaussianPDFReal μ v (Real.log (K / S₀)))
      (Real.log (K / S₀)) :=
    hasDerivAt_integral_Ioi (by linarith : Real.log (K / S₀) - 1 < Real.log (K / S₀))
      h_pdf_int.integrableOn h_pdf_cont.continuousOn
  -- Inner: d/ds[log(s/S₀)] = 1/s at s = K > 0.
  have h_inner : HasDerivAt (fun s : ℝ => Real.log (s / S₀)) (1 / K) K := by
    have h_log_K : HasDerivAt Real.log (1 / K) K := by
      have := Real.hasDerivAt_log hK.ne'; rwa [one_div]
    have h_log_diff : HasDerivAt (fun s : ℝ => Real.log s - Real.log S₀)
        (1 / K) K := h_log_K.sub_const _
    have h_ev : (fun s : ℝ => Real.log (s / S₀)) =ᶠ[𝓝 K]
        (fun s : ℝ => Real.log s - Real.log S₀) := by
      filter_upwards [eventually_gt_nhds hK] with s hs
      rw [Real.log_div hs.ne' hS₀.ne']
    exact h_log_diff.congr_of_eventuallyEq h_ev
  have h_chain := h_outer.comp K h_inner
  convert h_chain using 1
  · funext s
    rfl
  · ring

open ProbabilityTheory in
/-- **Strict antitonicity of the lognormal survival.**  For `v ≠ 0`, the
    survival is *strictly* decreasing on `(0, ∞)`.  Refines
    `survivalLN_antitoneOn` (weak monotonicity). -/
theorem survivalLN_strictAntitoneOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictAntiOn (survivalLN S₀ μ v) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact survivalLN_continuousOn hS₀ v
  · rw [interior_Ioi]
    intro K hK
    have hK_pos : 0 < K := hK
    have h_deriv : deriv (survivalLN S₀ μ v) K =
        -gaussianPDFReal μ v (Real.log (K / S₀)) / K :=
      (survivalLN_hasDerivAt hS₀ hK_pos).deriv
    rw [h_deriv]
    have h_pdf_pos : 0 < gaussianPDFReal μ v (Real.log (K / S₀)) :=
      gaussianPDFReal_pos μ v _ hv
    exact div_neg_of_neg_of_pos (by linarith) hK_pos

open ProbabilityTheory in
/-- **Strict convexity of the Black–Scholes call price** (Breeden–Litzenberger
    second derivative is the positive Gaussian density divided by the strike).
    For `S₀ > 0`, `v ≠ 0`, the call price `K ↦ BSC(K)` is strictly convex on
    `(0, ∞)`. -/
theorem callPriceBS_strictConvexOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (callPriceBS S₀ μ v) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · intro K hK
    exact (callPriceBS_hasDerivAt hS₀ hK).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro K hK
    have hK_pos : 0 < K := hK
    -- First derivative: -survivalLN.
    have h_eqLocal : deriv (callPriceBS S₀ μ v) =ᶠ[𝓝 K]
        fun K' : ℝ => -(survivalLN S₀ μ v K') := by
      filter_upwards [eventually_gt_nhds hK_pos] with K' hK'
      exact (callPriceBS_hasDerivAt hS₀ hK').deriv
    -- Second derivative: gaussianPDFReal / K > 0.
    have h_neg : HasDerivAt (fun K' : ℝ => -(survivalLN S₀ μ v K'))
        (gaussianPDFReal μ v (Real.log (K / S₀)) / K) K := by
      have h : HasDerivAt (survivalLN S₀ μ v)
          (-gaussianPDFReal μ v (Real.log (K / S₀)) / K) K :=
        survivalLN_hasDerivAt hS₀ hK_pos
      have h_neg' := h.neg
      convert h_neg' using 1; ring
    have h2 : HasDerivAt (deriv (callPriceBS S₀ μ v))
        (gaussianPDFReal μ v (Real.log (K / S₀)) / K) K :=
      h_neg.congr_of_eventuallyEq h_eqLocal
    rw [show (deriv^[2] (callPriceBS S₀ μ v)) K =
        deriv (deriv (callPriceBS S₀ μ v)) K from rfl, h2.deriv]
    have h_pdf_pos : 0 < gaussianPDFReal μ v (Real.log (K / S₀)) :=
      gaussianPDFReal_pos μ v _ hv
    positivity

open ProbabilityTheory MeasureTheory in
/-- **BS call price as expectation.**  For `S_T = S₀ · exp X` with
    `X ∼ 𝒩(μ, v)` (`v ≠ 0`) and strike `K > 0`,
        `BSC(K) = E_Q[(S_T − K)⁺]`. -/
theorem callPriceBS_eq_expectation {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ μ v K =
    ∫ x, max (S₀ * Real.exp x - K) 0 ∂(gaussianReal μ v) := by
  have h_int_exp : Integrable (fun x : ℝ => Real.exp x) (gaussianReal μ v) := by
    have := integrable_exp_mul_gaussianReal (μ := μ) (v := v) 1
    simpa using this
  have h_int_S₀exp : Integrable (fun x : ℝ => S₀ * Real.exp x) (gaussianReal μ v) :=
    h_int_exp.const_mul S₀
  have h_meas_payoff : AEStronglyMeasurable
      (fun x : ℝ => max (S₀ * Real.exp x - K) 0) (gaussianReal μ v) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have h_int_payoff : Integrable
      (fun x : ℝ => max (S₀ * Real.exp x - K) 0) (gaussianReal μ v) := by
    refine MeasureTheory.Integrable.mono_nonneg h_int_S₀exp h_meas_payoff ?_ ?_
    · exact Filter.Eventually.of_forall (fun _ => le_max_right _ _)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h_pos : 0 < S₀ * Real.exp x := mul_pos hS₀ (Real.exp_pos _)
      exact max_le (by linarith) h_pos.le
  rw [expectation_max_eq_integral_survival (gaussianReal μ v) K h_int_payoff]
  unfold callPriceBS
  refine (setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)).symm
  have hs_pos : 0 < s := lt_trans hK hs
  have h_set_eq : {x : ℝ | s < S₀ * Real.exp x} =
      Set.Ioi (Real.log (s / S₀)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
    rw [Real.log_lt_iff_lt_exp (div_pos hs_pos hS₀), div_lt_iff₀ hS₀]
    constructor <;> intro h <;>
      linarith [mul_comm (Real.exp x) S₀, mul_comm S₀ (Real.exp x)]
  rw [h_set_eq, ← survivalLN_eq_gaussianReal_real_Ioi hv]

open ProbabilityTheory in
/-- **Concrete BS-tail dominance, lognormal version, unconditional.**
    Specialising `BSC_tail_dominates_at_match` to the Black-Scholes risk-neutral
    lognormal distribution. -/
theorem BSC_lognormal_tail_dominates_at_match
    {l α S₀ μ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match : (∫ s in Set.Ioi K₁, survivalLN S₀ μ v s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ μ v s)
          ≥ 2 * callPrice l α K₁) :
    (l / K₁) ^ α ≤ survivalLN S₀ μ v K₁ := by
  refine BSC_tail_dominates_at_match hα hl hK₁ ha_lt
    (integrableOn_survivalLN hS₀ ha_pos) ?_ h_match h_butterfly
  exact (survivalLN_continuousOn hS₀ v).mono (Set.Ioi_subset_Ioi ha_pos.le)

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
  rw [callPriceBS_eq_expectation hS₀ hv hK]
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
    {S₀ K : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    survivalLN S₀ (-((v : ℝ) / 2)) v K =
    stdNormalCdf ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
  rw [survivalLN_eq_one_sub_stdNormalCdf hv]
  have h_log_neg : Real.log (S₀ / K) = -Real.log (K / S₀) := by
    rw [← Real.log_inv, inv_div]
  have h_arg : (Real.log (K / S₀) - -((v : ℝ) / 2)) / Real.sqrt (v : ℝ) =
                -((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ)) := by
    rw [h_log_neg]; field_simp; ring
  rw [h_arg, stdNormalCdf_neg]
  ring

end TailOptionPricing
