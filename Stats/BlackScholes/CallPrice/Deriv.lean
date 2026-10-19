module

/-
  Lognormal call derivatives and local tail comparison for
  arXiv:1908.02347v3, Arbitrage Boundaries. Smooth density formulas require
  positive spot, positive strike and nonzero variance.
-/
public import Stats.BlackScholes.CallPrice.Basic

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory in
/-- **Breeden–Litzenberger for Black–Scholes.**  For the lognormal call price
    `BSC(K) = ∫_K^∞ ℙ(S_T > s) ds`, the first derivative is
    `∂BSC/∂K = −ℙ(S_T > K) = −survivalLN(K)`. -/
theorem callPriceBS_hasDerivAt {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt (callPriceBS S₀ μ v) (-(survivalLN S₀ μ v K)) K := by
  have hK_half_pos : 0 < K / 2 := by linarith
  have hK_half_lt : K / 2 < K := by linarith
  exact hasDerivAt_integral_Ioi hK_half_lt
    (integrableOn_survivalLN hS₀ hK_half_pos)
    ((survivalLN_continuousOn hS₀ hv).mono (Set.Ioi_subset_Ioi hK_half_pos.le))

open ProbabilityTheory in
/-- **`BSC` is continuous in `K` on the positive half-line.** -/
theorem callPriceBS_continuousOn {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) :
    ContinuousOn (callPriceBS S₀ μ v) (Set.Ioi 0) :=
  by
    by_cases hv : v = 0
    · subst hv
      have heq : callPriceBS S₀ μ 0 = fun K => max (S₀ * Real.exp μ - K) 0 :=
        funext (callPriceBS_zero_var S₀ μ)
      rw [heq]
      fun_prop
    · exact fun _ hK => (callPriceBS_hasDerivAt hS₀ hv hK).continuousAt.continuousWithinAt

open ProbabilityTheory in
/-- **Derivative of the lognormal survival in the strike.**  Chain rule on
        `survivalLN s = ∫_{log(s/S₀)}^∞ φ_{μ,v}`,
    using FTC for the half-line and `d/ds[log(s/S₀)] = 1/s`. -/
theorem survivalLN_hasDerivAt {S₀ μ K : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
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
  have h_eq : survivalLN S₀ μ v =ᶠ[𝓝 K]
      (fun s => ∫ x in Ioi (Real.log (s / S₀)), gaussianPDFReal μ v x) := by
    filter_upwards [eventually_gt_nhds hK] with s hs
    exact survivalLN_eq_integral hS₀ hv hs
  convert h_chain.congr_of_eventuallyEq h_eq using 1
  ring

open ProbabilityTheory in
/-- **Strict antitonicity of the lognormal survival.**  For `v ≠ 0`, the
    survival is *strictly* decreasing on `(0, ∞)`.  Refines
    `survivalLN_antitoneOn` (weak monotonicity). -/
theorem survivalLN_strictAntitoneOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictAntiOn (survivalLN S₀ μ v) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact survivalLN_continuousOn hS₀ hv
  · rw [interior_Ioi]
    intro K hK
    have hK_pos : 0 < K := hK
    have h_deriv : deriv (survivalLN S₀ μ v) K =
        -gaussianPDFReal μ v (Real.log (K / S₀)) / K :=
      (survivalLN_hasDerivAt hS₀ hv hK_pos).deriv
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
    exact (callPriceBS_hasDerivAt hS₀ hv hK).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro K hK
    have hK_pos : 0 < K := hK
    -- First derivative: -survivalLN.
    have h_eqLocal : deriv (callPriceBS S₀ μ v) =ᶠ[𝓝 K]
        fun K' : ℝ => -(survivalLN S₀ μ v K') := by
      filter_upwards [eventually_gt_nhds hK_pos] with K' hK'
      exact (callPriceBS_hasDerivAt hS₀ hv hK').deriv
    -- Second derivative: gaussianPDFReal / K > 0.
    have h_neg : HasDerivAt (fun K' : ℝ => -(survivalLN S₀ μ v K'))
        (gaussianPDFReal μ v (Real.log (K / S₀)) / K) K := by
      have h : HasDerivAt (survivalLN S₀ μ v)
          (-gaussianPDFReal μ v (Real.log (K / S₀)) / K) K :=
        survivalLN_hasDerivAt hS₀ hv hK_pos
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

open ProbabilityTheory in
/-- **Concrete BS-tail dominance for nonzero lognormal variance.**
    Specialising `BSC_tail_dominates_at_match` to the Black-Scholes risk-neutral
    lognormal distribution. -/
theorem BSC_lognormal_tail_dominates_at_match
    {l α S₀ μ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match : (∫ s in Set.Ioi K₁, survivalLN S₀ μ v s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ μ v s)
          ≥ 2 * callPrice l α K₁) :
    (l / K₁) ^ α ≤ survivalLN S₀ μ v K₁ := by
  refine BSC_tail_dominates_at_match hα hl hK₁ ha_lt
    (integrableOn_survivalLN hS₀ ha_pos) ?_ h_match h_butterfly
  exact (survivalLN_continuousOn hS₀ hv).mono (Set.Ioi_subset_Ioi ha_pos.le)

end TailOptionPricing
