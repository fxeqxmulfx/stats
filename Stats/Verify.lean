module

/-
  Sanity check: print axioms used by every formalized theorem. Each line below
  must show only `[propext, Classical.choice, Quot.sound]` (Lean's three core
  axioms).  No `sorryAx` means the proof is closed.
-/
public import Stats.TailOptionPricing

@[expose] public section

-- Result 1, Eq. (2)–(3)
/-
theorem callPrice_eq {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    callPrice l α K = l ^ α * K ^ (1 - α) / (α - 1)
-/
#print axioms TailOptionPricing.callPrice_eq
/-
theorem callPrice_ratio {l α K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK₁ : l ≤ K₁) (hK₂ : l ≤ K₂) :
    callPrice l α K₂ = (K₂ / K₁) ^ (1 - α) * callPrice l α K₁
-/
#print axioms TailOptionPricing.callPrice_ratio

-- Result 2, Eq. (5)–(6)
/-
theorem callPriceReturns_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) ≤ K) :
    callPriceReturns l α S₀ K = (l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1)
-/
#print axioms TailOptionPricing.callPriceReturns_eq
/-
theorem callPriceReturns_ratio {l α S₀ K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hS₀ : 0 < S₀) (hK₁ : S₀ * (1 + l) ≤ K₁) (hK₂ : S₀ * (1 + l) ≤ K₂) :
    callPriceReturns l α S₀ K₂ =
      ((K₂ - S₀) / (K₁ - S₀)) ^ (1 - α) * callPriceReturns l α S₀ K₁
-/
#print axioms TailOptionPricing.callPriceReturns_ratio

-- Calibration / fitting formula (Section II.B)
/-
theorem callPriceReturns_pow_eq {α S₀ K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) ≤ K)
    (h_match : Cm = callPriceReturns l α S₀ K) :
    (l * S₀) ^ α = (α - 1) * Cm * (K - S₀) ^ (α - 1)
-/
#print axioms TailOptionPricing.callPriceReturns_pow_eq
/-
theorem callPriceReturns_invert {α S₀ K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) ≤ K)
    (h_match : Cm = callPriceReturns l α S₀ K) :
    l * S₀ = (α - 1) ^ ((1 : ℝ) / α) * Cm ^ ((1 : ℝ) / α) *
             (K - S₀) ^ (1 - 1 / α)
-/
#print axioms TailOptionPricing.callPriceReturns_invert

-- Density normalisation and normalised put price
/-
theorem densityMass_eq {l α S₀ : ℝ} (hα : 1 < α) (hl : 0 < l) (hl_lt : l < 1)
    (hS₀ : 0 < S₀) :
    densityMass l α S₀ = 1 - l ^ α
-/
#print axioms TailOptionPricing.densityMass_eq
/-
theorem putPrice_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK_pos : 0 < K) (hK_lt : K ≤ (1 - l) * S₀) :
    putPrice l α S₀ K =
      (l * S₀) ^ α / ((α - 1) * (1 - l ^ α)) *
        ((S₀ - K) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K + S₀))
-/
#print axioms TailOptionPricing.putPrice_eq

-- Result 3, Eq. (7), corrected
/-
theorem putRaw_eq {l α S₀ K : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK_pos : 0 < K) (hK_lt : K ≤ (1 - l) * S₀) :
    putRaw l α S₀ K =
      (l * S₀) ^ α / (α - 1) *
        ((S₀ - K) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K + S₀))
-/
#print axioms TailOptionPricing.putRaw_eq
/-
theorem putRaw_ratio {l α S₀ K₁ K₂ : ℝ} (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK₁_pos : 0 < K₁) (hK₂_pos : 0 < K₂)
    (hK₁_lt : K₁ ≤ (1 - l) * S₀) (hK₂_lt : K₂ ≤ (1 - l) * S₀) :
    putRaw l α S₀ K₂ * ((S₀ - K₁) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K₁ + S₀))
      = putRaw l α S₀ K₁ * ((S₀ - K₂) ^ (1 - α) - S₀ ^ (-α) * ((α - 1) * K₂ + S₀))
-/
#print axioms TailOptionPricing.putRaw_ratio

-- Theorem 1
/-
theorem survivalLogReturn_not_regularlyVarying {l α s₀ : ℝ}
    (hl : 0 < l) (hs₀ : 0 < s₀) (hα : 0 < α) (ρ : ℝ) :
    ¬ IsRegularlyVarying (survivalLogReturn l α s₀) ρ
-/
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying

-- Breeden–Litzenberger
/-
theorem callPrice_hasDerivAt {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    HasDerivAt (callPrice l α) (-((l / K) ^ α)) K
-/
#print axioms TailOptionPricing.callPrice_hasDerivAt
/-
theorem callPrice_deriv_eq_neg_survival {l α K : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK : l < K) :
    HasDerivAt (callPrice l α) (-(survival l α K)) K
-/
#print axioms TailOptionPricing.callPrice_deriv_eq_neg_survival
/-
theorem callPrice_hasDerivAt_secondOrder {l α K : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK : l < K) :
    HasDerivAt (fun K' => -((l / K') ^ α)) (α * l ^ α / K ^ (α + 1)) K
-/
#print axioms TailOptionPricing.callPrice_hasDerivAt_secondOrder

-- Strict convexity (Eq. (8) backbone)
/-
theorem callPrice_strictConvexOn {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Ioi l) (callPrice l α)
-/
#print axioms TailOptionPricing.callPrice_strictConvexOn

-- Eq. (8) — pure-power-law butterfly bound
/-
theorem callPrice_butterfly {l α K₁ ΔK : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hΔK : 0 < ΔK) (hΔK_lt : ΔK < K₁ - l) :
    2 * callPrice l α K₁ < callPrice l α (K₁ + ΔK) + callPrice l α (K₁ - ΔK)
-/
#print axioms TailOptionPricing.callPrice_butterfly

-- Layer-cake bridge: callPrice = E[(S − K)⁺] under Pareto survival
/-
theorem expectation_max_eq_integral_survival
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} (K : ℝ)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = ∫ s in Ioi K, μ.real {ω | s < S ω}
-/
#print axioms TailOptionPricing.expectation_max_eq_integral_survival
/-
theorem callPrice_eq_expectation
    {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω)
    {S : Ω → ℝ} {l α K : ℝ}
    (h_survival : ∀ s ∈ Ioi K, μ.real {ω | s < S ω} = (l / s) ^ α)
    (h_int : Integrable (fun ω => max (S ω - K) 0) μ) :
    ∫ ω, max (S ω - K) 0 ∂μ = callPrice l α K
-/
#print axioms TailOptionPricing.callPrice_eq_expectation

-- Theorem 1, general (Karamata-constant) version
/-
theorem survivalLogReturn_not_regularlyVarying_general
    {L : ℝ → ℝ} {α s₀ Linf : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀) (hLinf : 0 < Linf)
    (h_lim : Tendsto L atTop (𝓝 Linf)) (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ
-/
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying_general

-- Theorem 1, bounded-L version (slowly varying L bounded above and away from 0)
/-
theorem survivalLogReturn_not_regularlyVarying_bdd
    {L : ℝ → ℝ} {α s₀ m M : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀) (hm : 0 < m)
    (hLb : ∀ᶠ s in atTop, m ≤ L s)
    (hLub : ∀ᶠ s in atTop, L s ≤ M)
    (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ
-/
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying_bdd

-- Theorem 1, full slowly-varying version (parameterised on Karamata bound)
/-
theorem survivalLogReturn_not_regularlyVarying_slow
    {L : ℝ → ℝ} {α s₀ : ℝ}
    (hα : 0 < α) (hs₀ : 0 < s₀)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (h_subexp :
      Tendsto (fun t : ℝ =>
        Real.log (L (s₀ * Real.exp (t * 2)) / L (s₀ * Real.exp t)) / t)
        atTop (𝓝 0))
    (ρ : ℝ) :
    ¬ IsRegularlyVarying
      (fun x => L (s₀ * Real.exp x) * (s₀ * Real.exp x) ^ (-α)) ρ
-/
#print axioms TailOptionPricing.survivalLogReturn_not_regularlyVarying_slow

-- Eqs. (9) and (10): derivative comparison and α lower bound
/-
theorem deriv_le_of_matched_butterfly {f g : ℝ → ℝ} {f' g' K₁ : ℝ}
    (hf : HasDerivAt f f' K₁) (hg : HasDerivAt g g' K₁) (h_match : f K₁ = g K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        f (K₁ + ΔK) + g (K₁ - ΔK) ≥ 2 * f K₁) :
    g' ≤ f'
-/
#print axioms TailOptionPricing.deriv_le_of_matched_butterfly
/-
theorem callPrice_dominates_BSC_deriv {l α K₁ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK₁ : l < K₁) {BSC : ℝ → ℝ} {bsc' : ℝ}
    (h_BSC : HasDerivAt BSC bsc' K₁)
    (h_match : BSC K₁ = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + BSC (K₁ - ΔK) ≥ 2 * callPrice l α K₁) :
    bsc' ≤ -((l / K₁) ^ α)
-/
#print axioms TailOptionPricing.callPrice_dominates_BSC_deriv
/-
theorem alpha_lower_bound {l α K₁ Q : ℝ} (hl : 0 < l) (hK₁ : l < K₁)
    (h_ineq : (l / K₁) ^ α ≤ Q) :
    Real.log Q / Real.log (l / K₁) ≤ α
-/
#print axioms TailOptionPricing.alpha_lower_bound

-- Existence of matched butterfly (Eq. 8 hypothesis discharged via convexity
-- + value-and-slope match — abstract, and specialised to `callPrice`)
/-
theorem matched_butterfly_of_convex {f g : ℝ → ℝ} {m K₁ : ℝ} {S : Set ℝ}
    (hf_conv : ConvexOn ℝ S f) (hg_conv : ConvexOn ℝ S g)
    (hf : HasDerivAt f m K₁) (hg : HasDerivAt g m K₁)
    (hK₁ : K₁ ∈ S) (h_match : f K₁ = g K₁) :
    ∀ {ΔK : ℝ}, K₁ + ΔK ∈ S → K₁ - ΔK ∈ S →
      f (K₁ + ΔK) + g (K₁ - ΔK) ≥ 2 * f K₁
-/
#print axioms TailOptionPricing.matched_butterfly_of_convex
/-
theorem callPrice_matched_butterfly_of_BSC_convex {l α K₁ : ℝ} (hα : 1 < α)
    (hl : 0 < l) (hK₁ : l < K₁) {BSC : ℝ → ℝ}
    (hBSC_conv : ConvexOn ℝ (Set.Ioi l) BSC)
    (hBSC_deriv : HasDerivAt BSC (-((l / K₁) ^ α)) K₁)
    (h_match : BSC K₁ = callPrice l α K₁) :
    ∀ {ΔK : ℝ}, K₁ + ΔK ∈ Set.Ioi l → K₁ - ΔK ∈ Set.Ioi l →
      callPrice l α (K₁ + ΔK) + BSC (K₁ - ΔK) ≥ 2 * callPrice l α K₁
-/
#print axioms TailOptionPricing.callPrice_matched_butterfly_of_BSC_convex

-- Generic Breeden–Litzenberger and BSC tail dominance
/-
theorem hasDerivAt_integral_Ioi
    {F : ℝ → ℝ} {a K : ℝ} (haK : a < K)
    (hF_int : IntegrableOn F (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F (Set.Ioi a)) :
    HasDerivAt (fun K' => ∫ s in Set.Ioi K', F s) (-F K) K
-/
#print axioms TailOptionPricing.hasDerivAt_integral_Ioi
/-
theorem continuousOn_integral_Ioi
    {F : ℝ → ℝ} {a : ℝ}
    (hF_int : IntegrableOn F (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F (Set.Ioi a)) :
    ContinuousOn (fun K => ∫ s in Set.Ioi K, F s) (Set.Ioi a)
-/
#print axioms TailOptionPricing.continuousOn_integral_Ioi
/-
theorem callPrice_continuousOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    ContinuousOn (callPrice l α) (Set.Ici l)
-/
#print axioms TailOptionPricing.callPrice_continuousOn_Ici
/-
theorem callPrice_strictConvexOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Set.Ici l) (callPrice l α)
-/
#print axioms TailOptionPricing.callPrice_strictConvexOn_Ici
/-
theorem BSC_tail_dominates_at_match {l α K₁ : ℝ} (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    {F_BS : ℝ → ℝ} {a : ℝ} (ha : a < K₁)
    (hF_int : IntegrableOn F_BS (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F_BS (Set.Ioi a))
    (h_match : (∫ s in Set.Ioi K₁, F_BS s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + (∫ s in Set.Ioi (K₁ - ΔK), F_BS s)
          ≥ 2 * callPrice l α K₁) :
    (l / K₁) ^ α ≤ F_BS K₁
-/
#print axioms TailOptionPricing.BSC_tail_dominates_at_match
/-
theorem survival_isRegularlyVarying {l α : ℝ} (hl : 0 < l) :
    IsRegularlyVarying (survival l α) (-α)
-/
#print axioms TailOptionPricing.survival_isRegularlyVarying

-- Concrete lognormal Black–Scholes survival
-- Continuity requires positive spot and nonzero variance; see the actual-law regression.
#print axioms TailOptionPricing.survivalLN_continuousOn
/-
theorem survivalLN_nonneg (S₀ μ : ℝ) (v : ℝ≥0) (s : ℝ) :
    0 ≤ survivalLN S₀ μ v s
-/
#print axioms TailOptionPricing.survivalLN_nonneg
-- The actual survival is at most one for every variance, including zero.
#print axioms TailOptionPricing.survivalLN_le_one
-- The actual survival is antitone, with no spot or variance restriction.
#print axioms TailOptionPricing.survivalLN_antitoneOn
/-
theorem survivalLN_le_quadratic {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀)
    {s : ℝ} (hs : 0 < s) :
    survivalLN S₀ μ v s ≤ S₀ ^ 2 * Real.exp (2 * μ + 2 * (v : ℝ)) / s ^ 2
-/
#print axioms TailOptionPricing.survivalLN_le_quadratic
/-
theorem integrableOn_survivalLN {S₀ μ a : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (ha : 0 < a) :
    IntegrableOn (survivalLN S₀ μ v) (Set.Ioi a) volume
-/
#print axioms TailOptionPricing.integrableOn_survivalLN
-- The density-based comparison assumes positive spot and nonzero variance.
#print axioms TailOptionPricing.BSC_lognormal_tail_dominates_at_match

-- Standard normal CDF and connection to lognormal survival
/-
theorem stdNormalCdf_nonneg (x : ℝ) : 0 ≤ stdNormalCdf x
-/
#print axioms TailOptionPricing.stdNormalCdf_nonneg
/-
theorem stdNormalCdf_le_one (x : ℝ) : stdNormalCdf x ≤ 1
-/
#print axioms TailOptionPricing.stdNormalCdf_le_one
/-
theorem stdNormalCdf_monotone : Monotone stdNormalCdf
-/
#print axioms TailOptionPricing.stdNormalCdf_monotone
/-
theorem one_sub_stdNormalCdf (c : ℝ) :
    1 - stdNormalCdf c = (gaussianReal 0 1).real (Set.Ioi c)
-/
#print axioms TailOptionPricing.one_sub_stdNormalCdf
/-
theorem gaussianReal_map_locScale {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z + μ) =
    gaussianReal μ v
-/
#print axioms TailOptionPricing.gaussianReal_map_locScale
/-
theorem gaussianReal_real_Ioi_eq {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    (gaussianReal μ v).real (Set.Ioi c) =
    (gaussianReal 0 1).real (Set.Ioi ((c - μ) / Real.sqrt (v : ℝ)))
-/
#print axioms TailOptionPricing.gaussianReal_real_Ioi_eq
-- The CDF formula assumes positive spot, threshold and variance.
#print axioms TailOptionPricing.survivalLN_eq_one_sub_stdNormalCdf

-- Black–Scholes call price as integral and its derivative
-- The smooth call derivative assumes positive spot, strike and variance.
#print axioms TailOptionPricing.callPriceBS_hasDerivAt
/-
theorem callPriceBS_continuousOn {S₀ μ : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) :
    ContinuousOn (callPriceBS S₀ μ v) (Set.Ioi 0)
-/
#print axioms TailOptionPricing.callPriceBS_continuousOn
-- The density derivative assumes positive spot, strike and variance.
#print axioms TailOptionPricing.survivalLN_hasDerivAt
/-
theorem callPriceBS_strictConvexOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (callPriceBS S₀ μ v)
-/
#print axioms TailOptionPricing.callPriceBS_strictConvexOn
/-
theorem survivalLN_strictAntitoneOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictAntiOn (survivalLN S₀ μ v) (Set.Ioi 0)
-/
#print axioms TailOptionPricing.survivalLN_strictAntitoneOn
/-
theorem putPriceBS_strictConvexOn {S₀ μ : ℝ} {v : ℝ≥0}
    (hS₀ : 0 < S₀) (hv : v ≠ 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (putPriceBS S₀ μ v)
-/
#print axioms TailOptionPricing.putPriceBS_strictConvexOn

-- Smile correction (Eq. 10): σ-parametric BSC + total K-derivative chain rule
/-
theorem bs_pdf_identity_σ {S₀ K σ : ℝ}
    (hS₀ : 0 < S₀) (hσ : 0 < σ) (hK : 0 < K) :
    S₀ * gaussianPDFReal 0 1 ((Real.log (S₀ / K) + σ^2 / 2) / σ) =
    K * gaussianPDFReal 0 1 ((Real.log (S₀ / K) - σ^2 / 2) / σ)
-/
#print axioms TailOptionPricing.bs_pdf_identity_σ
/-
theorem callPriceBS_σ_smile_hasDerivAt
    {S₀ K₀ : ℝ} (hS₀ : 0 < S₀) (hK : 0 < K₀)
    {σ : ℝ → ℝ} {σ' : ℝ} (hσ_pos : 0 < σ K₀)
    (hσ_deriv : HasDerivAt σ σ' K₀) :
    HasDerivAt (fun K => callPriceBS_σ S₀ (σ K) K)
      (-stdNormalCdf ((Real.log (S₀ / K₀) - (σ K₀)^2 / 2) / σ K₀) +
       S₀ * gaussianPDFReal 0 1
         ((Real.log (S₀ / K₀) + (σ K₀)^2 / 2) / σ K₀) * σ') K₀
-/
#print axioms TailOptionPricing.callPriceBS_σ_smile_hasDerivAt
-- The law transformation assumes positive spot and threshold, including zero variance.
#print axioms TailOptionPricing.survivalLN_eq_gaussianReal_real_Ioi
-- The genuine payoff expectation bridge holds for every scale, strike, mean and variance.
#print axioms TailOptionPricing.callPriceBS_eq_expectation

-- Mills' ratio (Gaussian one-sided tail bound)
/-
theorem hasDerivAt_neg_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y)
               (x * gaussianPDFReal 0 1 x) x
-/
#print axioms TailOptionPricing.hasDerivAt_neg_gaussianPDFReal_std
/-
theorem tendsto_gaussianPDFReal_std_atTop :
    Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x) atTop (𝓝 0)
-/
#print axioms TailOptionPricing.tendsto_gaussianPDFReal_std_atTop
/-
theorem stdNormal_mills_ratio {c : ℝ} (hc : 0 < c) :
    1 - stdNormalCdf c ≤ gaussianPDFReal 0 1 c / c
-/
#print axioms TailOptionPricing.stdNormal_mills_ratio

-- Standard normal symmetry and Gaussian exponential tilt (BS closed-form scaffolding)
/-
theorem stdNormalCdf_neg (c : ℝ) : stdNormalCdf (-c) = 1 - stdNormalCdf c
-/
#print axioms TailOptionPricing.stdNormalCdf_neg
/-
theorem gaussianPDFReal_exp_tilt {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (t x : ℝ) :
    Real.exp (t * x) * gaussianPDFReal μ v x =
    Real.exp (μ * t + (v : ℝ) * t^2 / 2) *
      gaussianPDFReal (μ + (v : ℝ) * t) v x
-/
#print axioms TailOptionPricing.gaussianPDFReal_exp_tilt

-- Black–Scholes closed form via Gaussian completing-the-square
/-
theorem setIntegral_gaussianReal_eq_setIntegral_pdf_mul {μ : ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(gaussianReal μ v) =
    ∫ x in s, gaussianPDFReal μ v x * g x ∂volume
-/
#print axioms TailOptionPricing.setIntegral_gaussianReal_eq_setIntegral_pdf_mul
/-
theorem setIntegral_Ioi_exp_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    ∫ x in Set.Ioi c, Real.exp x ∂(gaussianReal μ v) =
    Real.exp (μ + (v : ℝ) / 2) *
      (gaussianReal (μ + (v : ℝ)) v).real (Set.Ioi c)
-/
#print axioms TailOptionPricing.setIntegral_Ioi_exp_gaussianReal
/-
theorem callPriceBS_decompose
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ μ v K =
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      (gaussianReal (μ + (v : ℝ)) v).real
        (Set.Ioi (Real.log (K / S₀))) -
    K * (gaussianReal μ v).real (Set.Ioi (Real.log (K / S₀)))
-/
#print axioms TailOptionPricing.callPriceBS_decompose
/-
theorem callPriceBS_closed_form_general
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ μ v K =
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      (1 - stdNormalCdf
        ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ))) -
    K * (1 - stdNormalCdf
      ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ)))
-/
#print axioms TailOptionPricing.callPriceBS_closed_form_general
/-
theorem callPriceBS_closed_form_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ (-((v : ℝ) / 2)) v K =
    S₀ * stdNormalCdf
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) -
    K * stdNormalCdf
      ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))
-/
#print axioms TailOptionPricing.callPriceBS_closed_form_riskNeutral

-- Risk-neutral survival in Φ(d₂) and erfc forms
-- The risk-neutral CDF formula assumes positive spot, strike and variance.
#print axioms TailOptionPricing.survivalLN_riskNeutral_eq_stdNormalCdf
/-
theorem one_sub_stdNormalCdf_eq_half_erfc (c : ℝ) :
    1 - stdNormalCdf c = (1/2) * erfc (c / Real.sqrt 2)
-/
#print axioms TailOptionPricing.one_sub_stdNormalCdf_eq_half_erfc
-- The erfc formula assumes positive spot, threshold and variance.
#print axioms TailOptionPricing.survivalLN_eq_half_erfc
/-
theorem alpha_lower_bound_erfc
    {l α S₀ μ K₁ a : ℝ} {v : ℝ≥0}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    (hS₀ : 0 < S₀) (hv : v ≠ 0) (ha_pos : 0 < a) (ha_lt : a < K₁)
    (h_match : (∫ s in Set.Ioi K₁, survivalLN S₀ μ v s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) +
          (∫ s in Set.Ioi (K₁ - ΔK), survivalLN S₀ μ v s)
          ≥ 2 * callPrice l α K₁) :
    Real.log ((1/2) *
        erfc ((Real.log (K₁ / S₀) - μ) /
          (Real.sqrt (v : ℝ) * Real.sqrt 2))) /
      Real.log (l / K₁) ≤ α
-/
#print axioms TailOptionPricing.alpha_lower_bound_erfc
/-
theorem callPriceBS_riskNeutral_hasDerivAt_stdNormalCdf
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt (callPriceBS S₀ (-((v : ℝ) / 2)) v)
      (-stdNormalCdf
        ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) K
-/
#print axioms TailOptionPricing.callPriceBS_riskNeutral_hasDerivAt_stdNormalCdf
/-
theorem integral_exp_gaussianReal_riskNeutral {v : ℝ≥0} :
    ∫ x, Real.exp x ∂(gaussianReal (-((v : ℝ) / 2)) v) = 1
-/
#print axioms TailOptionPricing.integral_exp_gaussianReal_riskNeutral
/-
theorem callPriceBS_riskNeutral_putForm
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS S₀ (-((v : ℝ) / 2)) v K - S₀ + K =
    K * stdNormalCdf
        (-((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) -
    S₀ * stdNormalCdf
      (-((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)))
-/
#print axioms TailOptionPricing.callPriceBS_riskNeutral_putForm
/-
theorem bs_pdf_identity
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) =
    K * gaussianPDFReal 0 1
      ((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))
-/
#print axioms TailOptionPricing.bs_pdf_identity
/-
theorem stdNormalCdf_hasDerivAt (x : ℝ) :
    HasDerivAt stdNormalCdf (gaussianPDFReal 0 1 x) x
-/
#print axioms TailOptionPricing.stdNormalCdf_hasDerivAt
/-
theorem callPriceBS_riskNeutral_hasDerivAt_S₀
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt (fun S => callPriceBS S (-((v : ℝ) / 2)) v K)
      (stdNormalCdf
        ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ))) S₀
-/
#print axioms TailOptionPricing.callPriceBS_riskNeutral_hasDerivAt_S₀
/-
theorem callPriceBS_riskNeutral_gamma
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    HasDerivAt
      (fun S => stdNormalCdf
        ((Real.log (S / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)))
      (gaussianPDFReal 0 1
          ((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)) /
        (S₀ * Real.sqrt (v : ℝ))) S₀
-/
#print axioms TailOptionPricing.callPriceBS_riskNeutral_gamma
/-
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
      ((Real.log (S₀ / K₁) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))
-/
#print axioms TailOptionPricing.BSC_riskNeutral_tail_dominates_at_match

-- Put–call parity and BS put closed form
/-
theorem integral_exp_gaussianReal {μ : ℝ} {v : ℝ≥0} :
    ∫ x, Real.exp x ∂(gaussianReal μ v) =
    Real.exp (μ + (v : ℝ) / 2)
-/
#print axioms TailOptionPricing.integral_exp_gaussianReal
-- Put-call parity holds for every scale, strike, mean and variance.
#print axioms TailOptionPricing.putCallParity_BS
/-
theorem putPriceBS_closed_form_general
    {S₀ μ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    putPriceBS S₀ μ v K =
    K * stdNormalCdf
        ((Real.log (K / S₀) - μ) / Real.sqrt (v : ℝ)) -
    S₀ * Real.exp (μ + (v : ℝ) / 2) *
      stdNormalCdf
        ((Real.log (K / S₀) - μ - (v : ℝ)) / Real.sqrt (v : ℝ))
-/
#print axioms TailOptionPricing.putPriceBS_closed_form_general
/-
theorem putPriceBS_closed_form_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    putPriceBS S₀ (-((v : ℝ) / 2)) v K =
    K * stdNormalCdf
        (-((Real.log (S₀ / K) - (v : ℝ) / 2) / Real.sqrt (v : ℝ))) -
    S₀ * stdNormalCdf
      (-((Real.log (S₀ / K) + (v : ℝ) / 2) / Real.sqrt (v : ℝ)))
-/
#print axioms TailOptionPricing.putPriceBS_closed_form_riskNeutral

-- BS Vega (σ-parametric)
/-
theorem callPriceBS_σ_vega_hasDerivAt
    {S₀ K σ₀ : ℝ} (hS₀ : 0 < S₀) (hσ : 0 < σ₀) (hK : 0 < K) :
    HasDerivAt (fun σ => callPriceBS_σ S₀ σ K)
      (S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + σ₀^2 / 2) / σ₀)) σ₀
-/
#print axioms TailOptionPricing.callPriceBS_σ_vega_hasDerivAt

-- Strong-Pareto calibration inversion (Section II.A)
/-
theorem callPrice_invert {α K Cm l : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K)
    (h_match : Cm = callPrice l α K) :
    l = ((α - 1) * Cm * K ^ (α - 1)) ^ ((1 : ℝ) / α)
-/
#print axioms TailOptionPricing.callPrice_invert

-- Higher Pareto moments (integrability of `s^k · survival l α s`)
/-
theorem integrableOn_rpow_mul_survival {l k α : ℝ}
    (hl : 0 < l) (hk : k < α - 1) :
    IntegrableOn (fun s => s ^ k * survival l α s) (Set.Ioi l)
-/
#print axioms TailOptionPricing.integrableOn_rpow_mul_survival

-- Connection between σ-form and abstract `callPriceBS` (risk-neutral)
/-
theorem callPriceBS_σ_eq_callPriceBS_riskNeutral
    {S₀ K : ℝ} {v : ℝ≥0} (hS₀ : 0 < S₀) (hv : v ≠ 0) (hK : 0 < K) :
    callPriceBS_σ S₀ (Real.sqrt (v : ℝ)) K =
      callPriceBS S₀ (-((v : ℝ) / 2)) v K
-/
#print axioms TailOptionPricing.callPriceBS_σ_eq_callPriceBS_riskNeutral

-- Eq. (10) assembled with smile correction
/-
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
      Real.log (l / K₁) ≤ α
-/
#print axioms TailOptionPricing.alpha_lower_bound_smile_erfc

-- Tier 1: closure of call/put development
-- Breeden–Litzenberger for the upside-returns shadow put (Result 2)
/-
theorem putShadowReturns_hasDerivAt {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) < K) :
    HasDerivAt (putShadowReturns l α S₀)
      (1 - ((l * S₀) / (K - S₀)) ^ α) K
-/
#print axioms TailOptionPricing.putShadowReturns_hasDerivAt
/-
theorem putShadowReturns_hasDerivAt_secondOrder {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) < K) :
    HasDerivAt (fun K' => 1 - ((l * S₀) / (K' - S₀)) ^ α)
      (α * (l * S₀) ^ α / (K - S₀) ^ (α + 1)) K
-/
#print axioms TailOptionPricing.putShadowReturns_hasDerivAt_secondOrder

-- Strict convexity of the shadow puts
/-
theorem putShadow_strictConvexOn {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Ioi l) (putShadow l α)
-/
#print axioms TailOptionPricing.putShadow_strictConvexOn
/-
theorem putShadowReturns_strictConvexOn {l α S₀ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) :
    StrictConvexOn ℝ (Ioi (S₀ * (1 + l))) (putShadowReturns l α S₀)
-/
#print axioms TailOptionPricing.putShadowReturns_strictConvexOn

-- Boundary continuity of the shadow put on the closed half-line
/-
theorem putShadow_continuousOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    ContinuousOn (putShadow l α) (Set.Ici l)
-/
#print axioms TailOptionPricing.putShadow_continuousOn_Ici

-- Pareto Greeks: parametric sensitivities
/-
theorem callPrice_hasDerivAt_l {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hlK : l < K) :
    HasDerivAt (fun l' => callPrice l' α K)
      (α * l ^ (α - 1) * K ^ (1 - α) / (α - 1)) l
-/
#print axioms TailOptionPricing.callPrice_hasDerivAt_l
/-
theorem putShadow_hasDerivAt_l {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hlK : l < K) :
    HasDerivAt (fun l' => putShadow l' α K)
      (α * l ^ (α - 1) * K ^ (1 - α) / (α - 1) - α / (α - 1)) l
-/
#print axioms TailOptionPricing.putShadow_hasDerivAt_l
/-
theorem callPrice_hasDerivAt_alpha {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    HasDerivAt (fun α' => callPrice l α' K)
      (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) / (α - 1) ^ 2)
      α
-/
#print axioms TailOptionPricing.callPrice_hasDerivAt_alpha
/-
theorem putShadow_hasDerivAt_alpha {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    HasDerivAt (fun α' => putShadow l α' K)
      (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) / (α - 1) ^ 2
        + l / (α - 1) ^ 2) α
-/
#print axioms TailOptionPricing.putShadow_hasDerivAt_alpha

-- Tier 3 Item 1: CVaR risk-measure properties
/-
theorem paretoVaR_mono_p {l α p q : ℝ}
    (hα_pos : 0 < α) (hl : 0 ≤ l) (_hp : 0 ≤ p) (hq_lt : q < 1)
    (hpq : p ≤ q) :
    paretoVaR l α p ≤ paretoVaR l α q
-/
#print axioms TailOptionPricing.paretoVaR_mono_p
/-
theorem paretoVaR_mono_l {l₁ l₂ α p : ℝ}
    (_hα_pos : 0 < α) (hp_lt : p < 1) (hl : l₁ ≤ l₂) :
    paretoVaR l₁ α p ≤ paretoVaR l₂ α p
-/
#print axioms TailOptionPricing.paretoVaR_mono_l
/-
theorem paretoVaR_scale (c l α p : ℝ) :
    paretoVaR (c * l) α p = c * paretoVaR l α p
-/
#print axioms TailOptionPricing.paretoVaR_scale
/-
theorem paretoCVaR_mono_p {l α p q : ℝ}
    (hα : 1 < α) (hl : 0 ≤ l) (hp : 0 ≤ p) (hq_lt : q < 1) (hpq : p ≤ q) :
    paretoCVaR l α p ≤ paretoCVaR l α q
-/
#print axioms TailOptionPricing.paretoCVaR_mono_p
/-
theorem paretoCVaR_mono_l {l₁ l₂ α p : ℝ}
    (hα : 1 < α) (hp_lt : p < 1) (hl : l₁ ≤ l₂) :
    paretoCVaR l₁ α p ≤ paretoCVaR l₂ α p
-/
#print axioms TailOptionPricing.paretoCVaR_mono_l
/-
theorem paretoCVaR_scale (c l α p : ℝ) :
    paretoCVaR (c * l) α p = c * paretoCVaR l α p
-/
#print axioms TailOptionPricing.paretoCVaR_scale
/-
theorem paretoCVaR_ge_paretoVaR {l α p : ℝ}
    (hα : 1 < α) (hl : 0 ≤ l) (hp : 0 ≤ p) (hp_lt : p < 1) :
    paretoVaR l α p ≤ paretoCVaR l α p
-/
#print axioms TailOptionPricing.paretoCVaR_ge_paretoVaR

-- Tier 3 Item 2: spectral risk measures
/-
theorem spectralRiskMeasure_const_one {l α : ℝ}
    (hα : 1 < α) :
    spectralRiskMeasure (fun _ => 1) l α = α * l / (α - 1)
-/
#print axioms TailOptionPricing.spectralRiskMeasure_const_one
/-
theorem spectralRiskMeasure_cvar_recovery {l α t : ℝ}
    (hα : 1 < α) (ht_lt : t < 1) :
    (1 - t)⁻¹ * (∫ p in t..1, paretoVaR l α p) = paretoCVaR l α t
-/
#print axioms TailOptionPricing.spectralRiskMeasure_cvar_recovery
/-
theorem spectralRiskMeasure_scale (c l α : ℝ) (φ : ℝ → ℝ) :
    spectralRiskMeasure φ (c * l) α = c * spectralRiskMeasure φ l α
-/
#print axioms TailOptionPricing.spectralRiskMeasure_scale

-- Tier 3 Item 3: moment-finiteness biconditional
/-
theorem paretoMomentIntegrand_integrableOn_iff {l α k : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α k) (Ioi l) volume ↔ k < α
-/
#print axioms TailOptionPricing.paretoMomentIntegrand_integrableOn_iff
/-
theorem paretoMoment_eq {l α k : ℝ}
    (hα : k < α) (hl : 0 < l) (hk : 0 ≤ k) :
    paretoMoment l α k = α * l ^ k / (α - k)
-/
#print axioms TailOptionPricing.paretoMoment_eq
/-
theorem paretoSecondMoment_integrableOn_iff {l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α 2) (Ioi l) volume ↔ 2 < α
-/
#print axioms TailOptionPricing.paretoSecondMoment_integrableOn_iff
/-
theorem paretoSecondMoment_eq {l α : ℝ} (hα : 2 < α) (hl : 0 < l) :
    paretoMoment l α 2 = α * l ^ (2:ℝ) / (α - 2)
-/
#print axioms TailOptionPricing.paretoSecondMoment_eq

-- Tier 3 Item 4: Markowitz failure / Mean-CVaR frontier
/-
theorem markowitz_objective_ill_defined {l α : ℝ}
    (hα_le : α ≤ 2) (hl : 0 < l) :
    ¬ IntegrableOn (fun s => s * survival l α s) (Ioi l) volume
-/
#print axioms TailOptionPricing.markowitz_objective_ill_defined
/-
theorem paretoPortfolioCVaR_eq_rescaled {w₁ w₂ c₁ c₂ l α p : ℝ} :
    paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = paretoCVaR ((w₁ * c₁ + w₂ * c₂) * l) α p
-/
#print axioms TailOptionPricing.paretoPortfolioCVaR_eq_rescaled
/-
theorem paretoPortfolio_meanCVaR_ratio {w₁ w₂ c₁ c₂ l α p : ℝ}
    (h_pos : 0 < w₁ * c₁ + w₂ * c₂) (hcvar_ne : paretoCVaR l α p ≠ 0) :
    paretoPortfolioMean w₁ w₂ c₁ c₂ l α / paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = (α * l / (α - 1)) / paretoCVaR l α p
-/
#print axioms TailOptionPricing.paretoPortfolio_meanCVaR_ratio
/-
theorem paretoPortfolioMean_scale (lam w₁ w₂ c₁ c₂ l α : ℝ) :
    paretoPortfolioMean (lam * w₁) (lam * w₂) c₁ c₂ l α
      = lam * paretoPortfolioMean w₁ w₂ c₁ c₂ l α
-/
#print axioms TailOptionPricing.paretoPortfolioMean_scale
/-
theorem paretoPortfolioCVaR_scale (lam w₁ w₂ c₁ c₂ l α p : ℝ) :
    paretoPortfolioCVaR (lam * w₁) (lam * w₂) c₁ c₂ l α p
      = lam * paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
-/
#print axioms TailOptionPricing.paretoPortfolioCVaR_scale
/-
theorem paretoPortfolio_frontier_degenerate {l α p : ℝ}
    {w₁ w₂ c₁ c₂ w₁' w₂' c₁' c₂' : ℝ}
    (h_pos : 0 < w₁ * c₁ + w₂ * c₂)
    (h_pos' : 0 < w₁' * c₁' + w₂' * c₂')
    (hcvar_ne : paretoCVaR l α p ≠ 0) :
    paretoPortfolioMean w₁ w₂ c₁ c₂ l α / paretoPortfolioCVaR w₁ w₂ c₁ c₂ l α p
      = paretoPortfolioMean w₁' w₂' c₁' c₂' l α
        / paretoPortfolioCVaR w₁' w₂' c₁' c₂' l α p
-/
#print axioms TailOptionPricing.paretoPortfolio_frontier_degenerate

-- Tier 3 Item 5: drawdown distribution under Pareto returns
/-
theorem paretoSampleMaxSurvival_eq_one_sub_pow {n : ℕ} {l α x : ℝ} :
    paretoSampleMaxSurvival n l α x = 1 - (1 - survival l α x) ^ n
-/
#print axioms TailOptionPricing.paretoSampleMaxSurvival_eq_one_sub_pow
/-
theorem paretoSampleMaxSurvival_at_l {n : ℕ} {l α : ℝ}
    (hl : 0 < l) (_hα_pos : 0 < α) (hn : 1 ≤ n) :
    paretoSampleMaxSurvival n l α l = 1
-/
#print axioms TailOptionPricing.paretoSampleMaxSurvival_at_l
/-
theorem paretoSampleMaxSurvival_union_bound {n : ℕ} {l α x : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hx : l ≤ x) :
    paretoSampleMaxSurvival n l α x ≤ n * survival l α x
-/
#print axioms TailOptionPricing.paretoSampleMaxSurvival_union_bound
/-
theorem paretoSampleMaxSurvival_le_n_survival {n : ℕ} {l α x : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hx : l ≤ x) :
    paretoSampleMaxSurvival n l α x ≤ n * (l / x) ^ α
-/
#print axioms TailOptionPricing.paretoSampleMaxSurvival_le_n_survival
/-
theorem paretoMaxDrawdownVaR_eq (n : ℕ) (l α p : ℝ) :
    paretoMaxDrawdownVaR n l α p = (n : ℝ) ^ ((1:ℝ) / α) * paretoVaR l α p
-/
#print axioms TailOptionPricing.paretoMaxDrawdownVaR_eq

-- Tier 3 Item 6: Kelly criterion derivative ingredients
/-
theorem kelly_log_hasDerivAt {f s : ℝ} (h : 0 < 1 + f * s) :
    HasDerivAt (fun f => Real.log (1 + f * s)) (s / (1 + f * s)) f
-/
#print axioms TailOptionPricing.kelly_log_hasDerivAt
/-
theorem kelly_log_hasDerivAt_second {f s : ℝ} (h : 0 < 1 + f * s) :
    HasDerivAt (fun f => s / (1 + f * s)) (-(s ^ 2) / (1 + f * s) ^ 2) f
-/
#print axioms TailOptionPricing.kelly_log_hasDerivAt_second
/-
theorem kelly_log_second_deriv_nonpos {f s : ℝ} (h : 0 < 1 + f * s) :
    -(s ^ 2) / (1 + f * s) ^ 2 ≤ 0
-/
#print axioms TailOptionPricing.kelly_log_second_deriv_nonpos
/-
theorem kelly_marginal_at_zero {s : ℝ} (_hs_pos : 0 < s) :
    s / (1 + 0 * s) = s
-/
#print axioms TailOptionPricing.kelly_marginal_at_zero

-- Tier 3 Item 7: MLE confidence intervals for α̂
/-
theorem paretoMLE_mul_inv {S : ℝ} {n : ℕ}
    (hS : S ≠ 0) (hn : n ≠ 0) :
    paretoMLE S n * paretoMLE_inv S n = 1
-/
#print axioms TailOptionPricing.paretoMLE_mul_inv
/-
theorem survival_eq_exp_neg_α_log_ratio {l α x : ℝ} (hl : 0 < l) (hx : 0 < x) :
    survival l α x = Real.exp (-(α * Real.log (x / l)))
-/
#print axioms TailOptionPricing.survival_eq_exp_neg_α_log_ratio
/-
theorem paretoMLE_at_expected {α : ℝ} {n : ℕ} (hα_pos : 0 < α) (hn : n ≠ 0) :
    paretoMLE ((n : ℝ) / α) n = α
-/
#print axioms TailOptionPricing.paretoMLE_at_expected
/-
theorem paretoMLE_asymptoticVariance_pos {α : ℝ} {n : ℕ}
    (hα_pos : 0 < α) (hn : 0 < n) :
    0 < paretoMLE_asymptoticVariance α n
-/
#print axioms TailOptionPricing.paretoMLE_asymptoticVariance_pos
/-
theorem paretoMLE_asymptoticVariance_scaling {α : ℝ} {n : ℕ}
    (_hα_pos : 0 < α) (hn : 0 < n) :
    paretoMLE_asymptoticVariance α n * n = α ^ 2
-/
#print axioms TailOptionPricing.paretoMLE_asymptoticVariance_scaling
/-
theorem paretoCIBound_nonneg {z α : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hα : 0 ≤ α) :
    0 ≤ paretoCIBound z α n
-/
#print axioms TailOptionPricing.paretoCIBound_nonneg
/-
theorem paretoCIBound_sq {z α : ℝ} {n : ℕ} (hn : 0 < n) :
    paretoCIBound z α n ^ 2 = z ^ 2 * paretoMLE_asymptoticVariance α n
-/
#print axioms TailOptionPricing.paretoCIBound_sq
/-
theorem paretoCIBound_scaling {z α : ℝ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) :
    paretoCIBound z α n * Real.sqrt n = paretoCIBound z α m * Real.sqrt m
-/
#print axioms TailOptionPricing.paretoCIBound_scaling

-- Tier 4 Item 1: Dynamic-hedging P&L distribution
/-
theorem squaredReturn_survival_eq {l α x : ℝ}
    (hl : 0 < l) (hx : 0 < x) :
    (l / Real.sqrt x) ^ α = (l ^ (2:ℝ) / x) ^ (α / 2)
-/
#print axioms TailOptionPricing.squaredReturn_survival_eq
/-
theorem squaredReturn_survival_eq_survival {l α x : ℝ}
    (hl : 0 < l) (hx : 0 < x) :
    survival l α (Real.sqrt x) = survival (l ^ (2:ℝ)) (α / 2) x
-/
#print axioms TailOptionPricing.squaredReturn_survival_eq_survival
/-
theorem gammaPnL_constant_eq {c l α : ℝ}
    (_hα : 2 < α) (_hl : 0 < l) :
    ∫ s in Ioi l, gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s
      = (1 / 2) * c * paretoMoment l α 2
-/
#print axioms TailOptionPricing.gammaPnL_constant_eq
/-
theorem gammaPnL_constant_integrableOn_iff {c l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) (hc : c ≠ 0) :
    IntegrableOn
        (fun s => gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s)
        (Ioi l) volume ↔ 2 < α
-/
#print axioms TailOptionPricing.gammaPnL_constant_integrableOn_iff
/-
theorem gammaPnL_constant_not_integrable {c l α : ℝ}
    (hl : 0 < l) (hα : 1 < α) (hα_le : α ≤ 2) (hc : c ≠ 0) :
    ¬ IntegrableOn
        (fun s => gammaPnLIntegrand (fun _ => c) s * paretoDensity l α s)
        (Ioi l) volume
-/
#print axioms TailOptionPricing.gammaPnL_constant_not_integrable
/-
theorem squaredReturn_variance_integrableOn_iff {l α : ℝ}
    (hl : 0 < l) (hα_pos : 0 < α) :
    IntegrableOn (paretoMomentIntegrand l α 4) (Ioi l) volume ↔ 4 < α
-/
#print axioms TailOptionPricing.squaredReturn_variance_integrableOn_iff

-- Tier 4 Item 2: Static replication under Pareto-priced calls
/-
theorem paretoCallStripCost_eq {g'' : ℝ → ℝ} {l α F b : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hF : l ≤ F) (hFb : F ≤ b) :
    ∫ K in F..b, g'' K * callPrice l α K
      = ∫ K in F..b, g'' K * (l ^ α * K ^ (1 - α) / (α - 1))
-/
#print axioms TailOptionPricing.paretoCallStripCost_eq
/-
theorem paretoPutStripCost_eq {g'' : ℝ → ℝ} {l α a F : ℝ}
    (hα : 1 < α) (hl : 0 < l) (ha : l ≤ a) (haF : a ≤ F) :
    ∫ K in a..F, g'' K * putShadow l α K
      = ∫ K in a..F, g'' K *
          (l ^ α * K ^ (1 - α) / (α - 1) + K - α * l / (α - 1))
-/
#print axioms TailOptionPricing.paretoPutStripCost_eq
/-
theorem paretoCarrMadan {g g' g'' : ℝ → ℝ} {l α a b F S : ℝ}
    (_hα : 1 < α) (_hl : 0 < l) (_ha : l ≤ a)
    (hF : F ∈ Set.Icc a b) (hS : S ∈ Set.Icc a b)
    (hg_cont   : ContinuousOn g (Set.Icc a b))
    (hg'_cont  : ContinuousOn g' (Set.Icc a b))
    (hg''_cont : ContinuousOn g'' (Set.Icc a b))
    (hg_deriv  : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt g' (g'' x) x) :
    g S = g F + g' F * (S - F)
        + (∫ K in a..F, max (K - S) 0 * g'' K)
        + (∫ K in F..b, max (S - K) 0 * g'' K)
-/
#print axioms TailOptionPricing.paretoCarrMadan

-- Tier 4 Item 3: K-decay rates of Greeks (Pareto vs BS)
/-
theorem paretoVega_relative_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) /
        (α - 1) ^ 2) / callPrice l α K
      = Real.log (l / K) - 1 / (α - 1)
-/
#print axioms TailOptionPricing.paretoVega_relative_eq
/-
theorem paretoVega_relative_tendsto_atBot {l α : ℝ}
    (_hα : 1 < α) (hl : 0 < l) :
    Tendsto (fun K : ℝ => Real.log (l / K) - 1 / (α - 1)) atTop atBot
-/
#print axioms TailOptionPricing.paretoVega_relative_tendsto_atBot
/-
theorem bsVega_tendsto_zero_atTop {S₀ σ : ℝ} (hS₀ : 0 < S₀) (hσ : 0 < σ) :
    Tendsto
      (fun K : ℝ => S₀ * gaussianPDFReal 0 1
        ((Real.log (S₀ / K) + σ ^ 2 / 2) / σ))
      atTop (𝓝 0)
-/
#print axioms TailOptionPricing.bsVega_tendsto_zero_atTop

-- Taleb's κ-metric for pre-asymptotic fat-tailedness (arXiv:1802.05495v3)
/-
theorem kappa_eq_ratio {M : ℕ → ℝ} {n₀ n : ℕ}
    (hn₀ : 0 < n₀) (hn : 0 < n)
    (hM₀ : 0 < M n₀) (hMn : 0 < M n) :
    kappa M n₀ n = 2 - Real.log ((n:ℝ)/(n₀:ℝ)) / Real.log ((M n)/(M n₀))
-/
#print axioms TailOptionPricing.kappa_eq_ratio
/-
theorem kappa_stable_invariance {M : ℕ → ℝ} {c ᾱ : ℝ}
    (hc : 0 < c) (hᾱ : 0 < ᾱ)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / ᾱ))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - ᾱ
-/
#print axioms TailOptionPricing.kappa_stable_invariance
/-
theorem kappa_gaussian {M : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hM_form : ∀ k : ℕ, 0 < k → M k = c * Real.sqrt k)
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 0
-/
#print axioms TailOptionPricing.kappa_gaussian
/-
theorem kappa_cauchy {M : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 1
-/
#print axioms TailOptionPricing.kappa_cauchy
/-
theorem n_nu_gaussian (n_g : ℕ) (_hn_g : 0 < n_g) :
    n_nu n_g 0 = (n_g : ℝ)
-/
#print axioms TailOptionPricing.n_nu_gaussian
/-
theorem n_nu_gt_n_g {n_g : ℕ} {κ_g : ℝ}
    (hn_g : 1 < n_g) (hκ_pos : 0 < κ_g) (hκ_lt : κ_g < 1) :
    (n_g : ℝ) < n_nu n_g κ_g
-/
#print axioms TailOptionPricing.n_nu_gt_n_g
/-
theorem log_MAD_telescope {M : ℕ → ℝ} {n₀ n : ℕ} (h_le : n₀ ≤ n) :
    Real.log (M n) - Real.log (M n₀)
      = ∑ i ∈ Finset.range (n - n₀),
          (Real.log (M (n₀ + i + 1)) - Real.log (M (n₀ + i)))
-/
#print axioms TailOptionPricing.log_MAD_telescope
/-
theorem kappa_decomposition {M : ℕ → ℝ} {n₀ n : ℕ}
    (_hn₀ : 0 < n₀) (h_le : n₀ ≤ n) :
    kappa M n₀ n
      = 2 - (Real.log n - Real.log n₀) /
          (∑ i ∈ Finset.range (n - n₀),
              (Real.log (M (n₀ + i + 1)) - Real.log (M (n₀ + i))))
-/
#print axioms TailOptionPricing.kappa_decomposition
/-
theorem kappa_decomposition_local {M : ℕ → ℝ} {n₀ n : ℕ}
    (hn₀ : 0 < n₀) (h_le : n₀ ≤ n)
    (h_log_ne : ∀ i, n₀ ≤ i → i < n →
        Real.log (M (i + 1)) - Real.log (M i) ≠ 0) :
    kappa M n₀ n
      = 2 - (Real.log n - Real.log n₀) /
          (∑ i ∈ Finset.range (n - n₀),
              (Real.log ((n₀ + i + 1 : ℕ) : ℝ) - Real.log ((n₀ + i : ℕ) : ℝ)) /
                (2 - kappa M (n₀ + i) (n₀ + i + 1)))
-/
#print axioms TailOptionPricing.kappa_decomposition_local
/-
theorem kappa_upper_bound_subadditive {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1) (hM_grow : M 1 < M n)
    (h_subadditive : M n ≤ (n:ℝ) * M 1) :
    kappa M 1 n ≤ 1
-/
#print axioms TailOptionPricing.kappa_upper_bound_subadditive
/-
theorem kappa_exponential {lam : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hn : 2 ≤ n) :
    kappa (expSumMAD lam) 1 n
      = 2 - Real.log n /
          ((n:ℝ) * Real.log n - (n:ℝ) - Real.log (Real.Gamma n) + 1)
-/
#print axioms TailOptionPricing.kappa_exponential
/-
theorem cubicStudentSumMAD_one : cubicStudentSumMAD 1 = 2 * Real.sqrt 3 / Real.pi
-/
#print axioms TailOptionPricing.cubicStudentSumMAD_one
/-
theorem cubicStudentSumMAD_succ {n : ℕ} (hn : 2 ≤ n) :
    cubicStudentSumMAD n = 2 * Real.sqrt 3 / Real.pi *
      (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1)
-/
#print axioms TailOptionPricing.cubicStudentSumMAD_succ
/-
theorem kappa_cubicStudent {n : ℕ} (hn : 2 ≤ n)
    (h_pos : 0 < Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1) :
    kappa cubicStudentSumMAD 1 n = 2 - Real.log n /
      Real.log (Real.exp n * (n:ℝ) ^ (-(n:ℝ)) * incompleteGamma (n + 1) n - 1)
-/
#print axioms TailOptionPricing.kappa_cubicStudent
/-
theorem kappa_loulakis_lower_bound {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1)
    (h_bound : (n:ℝ) * M 1 ≤ M n) :
    1 ≤ kappa M 1 n
-/
#print axioms TailOptionPricing.kappa_loulakis_lower_bound
/-
theorem kappa_loulakis_eq_one {M : ℕ → ℝ} {n : ℕ}
    (hn : 1 < n) (hM1_pos : 0 < M 1)
    (h_eq : M n = (n:ℝ) * M 1) :
    kappa M 1 n = 1
-/
#print axioms TailOptionPricing.kappa_loulakis_eq_one
/-
theorem kappa_exponential_asymptotic {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => Real.log n * kappa (expSumMAD lam) 1 n)
      atTop (𝓝 (4 - 2 * Real.log (2 * Real.pi)))
-/
#print axioms TailOptionPricing.kappa_exponential_asymptotic
/-
theorem kappa_cubicStudent_asymptotic :
    Tendsto (fun n : ℕ => Real.log n * kappa cubicStudentSumMAD 1 n)
      atTop (𝓝 (Real.log (Real.pi ^ 2 / 4)))
-- formerly depended on axiom `incompleteGamma_laplace_asymptotic`; now discharged
-- in `Stats.Kappa.CubicStudentLaplace`.
-- Paper claims limit `π²/4`; that is a typo, correct is `log(π²/4)`.
-/
#print axioms TailOptionPricing.kappa_cubicStudent_asymptotic
/-
theorem poisson_cdf_at_mean_tendsto_half :
    Tendsto (fun n : ℕ =>
        Real.exp (-(n:ℝ)) *
          ∑ k ∈ Finset.range n, (n:ℝ)^k / (k.factorial:ℝ))
      atTop (𝓝 (1/2))
-- todo3.md C.3, route (b).  Combines the Loulakis identity
-- (`incompleteGamma_loulakis`, `Stats.Kappa.CubicStudent`), the Laplace
-- asymptotic for `Γ(n+1, n)` (`Stats.Kappa.CubicStudentLaplace`), and
-- Mathlib's Stirling formula.
-/
#print axioms TailOptionPricing.PoissonCDF.poisson_cdf_at_mean_tendsto_half
/-
theorem stableAlphaBar_of_lt {α : ℝ} (h : α < 2) : stableAlphaBar α = α
-/
#print axioms TailOptionPricing.stableAlphaBar_of_lt
/-
theorem stableAlphaBar_of_ge {α : ℝ} (h : 2 ≤ α) : stableAlphaBar α = 2
-/
#print axioms TailOptionPricing.stableAlphaBar_of_ge
/-
theorem stableAlphaBar_le_two (α : ℝ) : stableAlphaBar α ≤ 2
-/
#print axioms TailOptionPricing.stableAlphaBar_le_two
/-
theorem stableAlphaBar_pos {α : ℝ} (hα : 0 < α) : 0 < stableAlphaBar α
-/
#print axioms TailOptionPricing.stableAlphaBar_pos
/-
theorem kappa_stable_invariance_alphaBar {M : ℕ → ℝ} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k:ℝ) ^ ((1:ℝ) / stableAlphaBar α))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - stableAlphaBar α
-/
#print axioms TailOptionPricing.kappa_stable_invariance_alphaBar
/-
theorem cubicStudentDensity_pos (x : ℝ) : 0 < cubicStudentDensity x
-/
#print axioms TailOptionPricing.cubicStudentDensity_pos
/-
theorem cubicStudentDensity_neg (x : ℝ) :
    cubicStudentDensity (-x) = cubicStudentDensity x
-/
#print axioms TailOptionPricing.cubicStudentDensity_neg
/-
theorem gammaSumDensity_eq_gammaPDFReal {lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n) {z : ℝ} (hz : 0 ≤ z) :
    gammaSumDensity lam n z = ProbabilityTheory.gammaPDFReal (n:ℝ) lam z
-/
#print axioms TailOptionPricing.gammaSumDensity_eq_gammaPDFReal
/-
theorem gaussianMixtureKurtosis_ge_three_iff_poly
    {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h_pos : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureKurtosis μ₁ μ₂ σ₁ σ₂ ↔
    (μ₁ - μ₂) ^ 4 ≤ 6 * (σ₁ ^ 2 - σ₂ ^ 2) ^ 2
-/
#print axioms TailOptionPricing.gaussianMixtureKurtosis_ge_three_iff_poly
/-
theorem gaussianMixtureKurtosis_ge_three_iff
    {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (h_pos : 0 < (μ₁ - μ₂) ^ 2 + 2 * (σ₁ ^ 2 + σ₂ ^ 2)) :
    3 ≤ gaussianMixtureKurtosis μ₁ μ₂ σ₁ σ₂ ↔
    |μ₁ - μ₂| ≤ (6 : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt |σ₁ ^ 2 - σ₂ ^ 2|
-/
#print axioms TailOptionPricing.gaussianMixtureKurtosis_ge_three_iff
/-
theorem paretoSurvival_isRegularlyVarying {l α : ℝ} (hl : 0 < l) :
    IsRegularlyVarying (survival l α) (-α)
-/
#print axioms TailOptionPricing.paretoSurvival_isRegularlyVarying

-- Binary forecasts vs real-world payoffs (arXiv:1907.11162v3)
/-
theorem characteristicScale_pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / (K * survival l α K) = α / (α - 1)
-/
#print axioms TailOptionPricing.characteristicScale_pareto
/-
theorem characteristicScale_pareto_gt_one {α : ℝ} (hα : 1 < α) :
    1 < α / (α - 1)
-/
#print axioms TailOptionPricing.characteristicScale_pareto_gt_one
/-
theorem I1_eq_I2_of_constantOn {g f : ℝ → ℝ} {K : ℝ}
    (h_const : ∀ᵐ x ∂(volume.restrict (Ioi K)), g x = g K) :
    I1 g f K = I2 g f K
-/
#print axioms TailOptionPricing.I1_eq_I2_of_constantOn
/-
theorem I1_eq_I2_heaviside {f : ℝ → ℝ} {K : ℝ} :
    I1 (heaviside K) f K = I2 (heaviside K) f K
-/
#print axioms TailOptionPricing.I1_eq_I2_heaviside
/-
theorem I1_pareto_id_eq {l α K : ℝ}
    (_hα : 1 < α) (_hl : 0 < l) (_hK : l ≤ K) :
    I1 id (paretoDensity l α) K = paretoTailExpectation l α K
-/
#print axioms TailOptionPricing.I1_pareto_id_eq
/-
theorem I2_pareto_id_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    I2 id (paretoDensity l α) K = K * survival l α K
-/
#print axioms TailOptionPricing.I2_pareto_id_eq
/-
theorem pareto_I1_div_I2_eq {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    I1 id (paretoDensity l α) K / I2 id (paretoDensity l α) K = α / (α - 1)
-/
#print axioms TailOptionPricing.pareto_I1_div_I2_eq
/-
theorem gaussian_I1_id_eq {K : ℝ} (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 K
-/
#print axioms TailOptionPricing.gaussian_I1_id_eq
/-
theorem correctedProbability_pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailExpectation l α K / K = (α / (α - 1)) * survival l α K
-/
#print axioms TailOptionPricing.correctedProbability_pareto
/-
theorem paretoTailMean_hasDerivAt_alpha {α K : ℝ} (hα : 1 < α) :
    HasDerivAt (fun a => a * K / (a - 1)) (-K / (α - 1) ^ 2) α
-/
#print axioms TailOptionPricing.paretoTailMean_hasDerivAt_alpha
/-
theorem paretoTailMean_hasDerivAt_alpha_second {α K : ℝ} (hα : 1 < α) :
    HasDerivAt (fun a : ℝ => -K / (a - 1) ^ 2) (2 * K / (α - 1) ^ 3) α
-/
#print axioms TailOptionPricing.paretoTailMean_hasDerivAt_alpha_second
/-
theorem paretoTailMean_secondDeriv_alpha_pos {α K : ℝ}
    (hα : 1 < α) (hK : 0 < K) :
    0 < 2 * K / (α - 1) ^ 3
-/
#print axioms TailOptionPricing.paretoTailMean_secondDeriv_alpha_pos
/-
theorem inseparability_const {f : ℝ → ℝ} {K c : ℝ} :
    ∫ x in Ioi K, c * f x = c * ∫ x in Ioi K, f x
-/
#print axioms TailOptionPricing.inseparability_const
/-
theorem inseparability_affine_linearity {f : ℝ → ℝ} {K a b : ℝ}
    (hf_int : IntegrableOn f (Ioi K))
    (hxf_int : IntegrableOn (fun x : ℝ => x * f x) (Ioi K)) :
    ∫ x in Ioi K, (a * x + b) * f x
      = a * (∫ x in Ioi K, x * f x) + b * (∫ x in Ioi K, f x)
-/
#print axioms TailOptionPricing.inseparability_affine_linearity
/-
theorem brierTerm_bounded {f y : ℝ}
    (hf_lb : 0 ≤ f) (hf_ub : f ≤ 1) (hy_lb : 0 ≤ y) (hy_ub : y ≤ 1) :
    0 ≤ (f - y) ^ 2 ∧ (f - y) ^ 2 ≤ 1
-/
#print axioms TailOptionPricing.brierTerm_bounded
/-
theorem brierScore_moment_bounded {lam q : ℝ}
    (h_lb : 0 ≤ lam) (h_ub : lam ≤ 1) (hq : 0 ≤ q) :
    lam ^ q ≤ 1
-/
#print axioms TailOptionPricing.brierScore_moment_bounded
/-
theorem brierScore_moment_in_unit_interval {lam q : ℝ}
    (h_lb : 0 ≤ lam) (h_ub : lam ≤ 1) (hq : 0 ≤ q) :
    0 ≤ lam ^ q ∧ lam ^ q ≤ 1
-/
#print axioms TailOptionPricing.brierScore_moment_in_unit_interval
/-
theorem bernoulliCGF_inner_pos {p t : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    0 < 1 - p + p * Real.exp t
-/
#print axioms TailOptionPricing.bernoulliCGF_inner_pos
/-
theorem bernoulliCGF_hasDerivAt_zero (p : ℝ) :
    HasDerivAt (bernoulliCGF p) p 0
-/
#print axioms TailOptionPricing.bernoulliCGF_hasDerivAt_zero
/-
theorem bernoulliCGF_zero {p : ℝ} :
    bernoulliCGF p 0 = 0
-/
#print axioms TailOptionPricing.bernoulliCGF_zero
/-
theorem bernoulli_kappa1 (p : ℝ) :
    deriv (bernoulliCGF p) 0 = p
-/
#print axioms TailOptionPricing.bernoulli_kappa1
/-
theorem pareto_I1_div_I2_tendsto {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    Tendsto (fun K : ℝ =>
        I1 id (paretoDensity l α) K / I2 id (paretoDensity l α) K)
      atTop (𝓝 (α / (α - 1)))
-/
#print axioms TailOptionPricing.pareto_I1_div_I2_tendsto
/-
theorem paretoTailMean_iteratedDeriv_two {α K : ℝ} (hα : 1 < α) :
    deriv (deriv (fun a : ℝ => a * K / (a - 1))) α = 2 * K / (α - 1) ^ 3
-/
#print axioms TailOptionPricing.paretoTailMean_iteratedDeriv_two
/-
theorem bernoulliCGF_hasDerivAt {p t : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF p)
      (p * Real.exp t / (1 - p + p * Real.exp t)) t
-/
#print axioms TailOptionPricing.bernoulliCGF_hasDerivAt
/-
theorem bernoulli_kappa2 {p : ℝ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (fun t : ℝ => p * Real.exp t / (1 - p + p * Real.exp t))
      (p * (1 - p)) 0
-/
#print axioms TailOptionPricing.bernoulli_kappa2
/-
theorem inseparability_jensen_strict {g : ℝ → ℝ}
    (hg : StrictConvexOn ℝ Set.univ g) {x y a b : ℝ}
    (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    g (a * x + b * y) < a * g x + b * g y
-/
#print axioms TailOptionPricing.inseparability_jensen_strict
/-
theorem exp_survival_eq {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    ∫ x in Ioi K, expDensity lam x = Real.exp (-(lam * K))
-/
#print axioms TailOptionPricing.exp_survival_eq
/-
theorem exp_tail_expectation_eq {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * expDensity lam x
      = (K + 1 / lam) * Real.exp (-(lam * K))
-/
#print axioms TailOptionPricing.exp_tail_expectation_eq
/-
theorem exp_conditional_excess {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    (∫ x in Ioi K, x * expDensity lam x) / (∫ x in Ioi K, expDensity lam x) - K
      = 1 / lam
-/
#print axioms TailOptionPricing.exp_conditional_excess
/-
theorem bernoulli_kappa3 {p : ℝ} (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF_secondDeriv p)
      (p * (1 - p) * (1 - 2 * p)) 0
-/
#print axioms TailOptionPricing.bernoulli_kappa3
/-
theorem bernoulli_kappa4 {p : ℝ} (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    HasDerivAt (bernoulliCGF_thirdDeriv p)
      (p * (1 - p) * (1 - 6 * p * (1 - p))) 0
-/
#print axioms TailOptionPricing.bernoulli_kappa4
/-
theorem gaussian_eq8_polynomial_pos {K : ℝ} (hK : 0 < K) :
    0 < K ^ 4 - K ^ 3 - K ^ 2 + 2 * K
-/
#print axioms TailOptionPricing.gaussian_eq8_polynomial_pos
/-
theorem gaussianEq8_sigmaSensitivity_eq_phi {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ =>
        gaussianPDFReal 0 1 (K / s) * (1 + K ^ 2 / s ^ 2)
          - K / s ^ 2 * gaussianPDFReal 0 1 (K / s))
      (((K - 1) * K ^ 3 - (K - 2) * K * σ ^ 2) / σ ^ 5
        * gaussianPDFReal 0 1 (K / σ)) σ
-/
#print axioms TailOptionPricing.gaussianEq8_sigmaSensitivity_eq_phi
/-
theorem gaussianEq8_sigmaSensitivity_eq {K σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt
      (fun s : ℝ =>
        gaussianPDFReal 0 1 (K / s) * (1 + K ^ 2 / s ^ 2)
          - K / s ^ 2 * gaussianPDFReal 0 1 (K / s))
      (Real.exp (-K ^ 2 / (2 * σ ^ 2))
        * ((K - 1) * K ^ 3 - (K - 2) * K * σ ^ 2)
        / (Real.sqrt (2 * Real.pi) * σ ^ 5)) σ
-/
#print axioms TailOptionPricing.gaussianEq8_sigmaSensitivity_eq
/-
theorem integral_x_gaussianPDF_σ {K σ : ℝ} (hσ : 0 < σ) (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * gaussianPDF_σ σ x =
      σ * gaussianPDFReal 0 1 (K / σ)
-/
#print axioms TailOptionPricing.integral_x_gaussianPDF_σ
/-
theorem integral_gaussianPDF_σ {K σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi K, gaussianPDF_σ σ x = 1 - stdNormalCdf (K / σ)
-/
#print axioms TailOptionPricing.integral_gaussianPDF_σ

-- Branching epistemic uncertainty (arXiv:1912.00277v2)
/-
theorem epistemicMomentFactor_two (ε : ℝ) :
    epistemicMomentFactor 2 ε = 1 + ε^2
-/
#print axioms TailOptionPricing.epistemicMomentFactor_two
/-
theorem epistemicMomentFactor_four (ε : ℝ) :
    epistemicMomentFactor 4 ε = 1 + 6 * ε^2 + ε^4
-/
#print axioms TailOptionPricing.epistemicMomentFactor_four
/-
theorem epistemicSigmaMoment_eq (n k : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n k σ ε
      = σ^k * (epistemicMomentFactor k ε)^n
-/
#print axioms TailOptionPricing.epistemicSigmaMoment_eq
/-
theorem epistemicVariance_eq (n : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n 2 σ ε = σ^2 * (1 + ε^2)^n
-/
#print axioms TailOptionPricing.epistemicVariance_eq
/-
theorem epistemicSigmaFourthMoment_eq (n : ℕ) (σ ε : ℝ) :
    epistemicSigmaMoment n 4 σ ε = σ^4 * (1 + 6 * ε^2 + ε^4)^n
-/
#print axioms TailOptionPricing.epistemicSigmaFourthMoment_eq
/-
theorem epistemicKurtosis_eq (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicKurtosis n σ ε
      = 3 * (1 + 6 * ε^2 + ε^4)^n / (1 + ε^2)^(2 * n)
-/
#print axioms TailOptionPricing.epistemicKurtosis_eq
/-
theorem epistemicMomentFactor_four_ge_two_sq (ε : ℝ) :
    (1 + ε^2)^2 ≤ 1 + 6 * ε^2 + ε^4
-/
#print axioms TailOptionPricing.epistemicMomentFactor_four_ge_two_sq
/-
theorem epistemicMomentFactor_four_strict {ε : ℝ} (hε : ε ≠ 0) :
    (1 + ε^2)^2 < 1 + 6 * ε^2 + ε^4
-/
#print axioms TailOptionPricing.epistemicMomentFactor_four_strict
/-
theorem epistemicKurtosis_ge_three (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    3 ≤ epistemicKurtosis n σ ε
-/
#print axioms TailOptionPricing.epistemicKurtosis_ge_three
/-
theorem epistemicKurtosis_gt_three {n : ℕ} {σ ε : ℝ}
    (hn : 1 ≤ n) (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    3 < epistemicKurtosis n σ ε
-/
#print axioms TailOptionPricing.epistemicKurtosis_gt_three
/-
theorem epistemicExcessKurtosis_eq (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    epistemicExcessKurtosis n σ ε
      = 3 * ((1 + 6 * ε^2 + ε^4)^n / (1 + ε^2)^(2 * n) - 1)
-/
#print axioms TailOptionPricing.epistemicExcessKurtosis_eq
/-
theorem epistemicExcessKurtosis_nonneg (n : ℕ) (σ ε : ℝ) (hσ : σ ≠ 0) :
    0 ≤ epistemicExcessKurtosis n σ ε
-/
#print axioms TailOptionPricing.epistemicExcessKurtosis_nonneg

-- Hidden moments of a probability distribution (arXiv:2004.05894v1)
/-
theorem paretoTailMoment_eq {l α p K : ℝ}
    (hα : 0 < α) (hl : 0 < l) (hp : p < α) (hK : l ≤ K) :
    paretoTailMoment l α p K = α * l ^ α * K ^ (p - α) / (α - p)
-/
#print axioms TailOptionPricing.paretoTailMoment_eq
/-
theorem paretoTailMoment_at_zero {l α K : ℝ}
    (hα : 0 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 0 K = survival l α K
-/
#print axioms TailOptionPricing.paretoTailMoment_at_zero
/-
theorem paretoTailMoment_at_one {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    paretoTailMoment l α 1 K = paretoTailExpectation l α K
-/
#print axioms TailOptionPricing.paretoTailMoment_at_one
/-
theorem paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF
    {l α y : ℝ} {n : ℕ}
    (hl : 0 < l) (hα_pos : 0 < α) (hy_pos : 0 < y) :
    paretoSampleSurvivalRatioCDF n y
      = 1 - paretoSampleMaxCDF n l α (l * y ^ (-(1 : ℝ) / α))
-/
#print axioms TailOptionPricing.paretoSampleSurvivalRatioCDF_eq_one_sub_maxCDF
/-
theorem paretoSampleSurvivalRatioPDF_eq_deriv (n : ℕ) (y : ℝ) :
    HasDerivAt (paretoSampleSurvivalRatioCDF n)
      (paretoSampleSurvivalRatioPDF n y) y
-/
#print axioms TailOptionPricing.paretoSampleSurvivalRatioPDF_eq_deriv
/-
theorem paretoSampleSurvivalRatio_mean (n : ℕ) (hn : 1 ≤ n) :
    ∫ y in (0:ℝ)..1, y * paretoSampleSurvivalRatioPDF n y
      = 1 / ((n : ℝ) + 1)
-/
#print axioms TailOptionPricing.paretoSampleSurvivalRatio_mean
/-
theorem paretoSampleSurvivalRatio_mean_asymptotic_gap (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1))
-/
#print axioms TailOptionPricing.paretoSampleSurvivalRatio_mean_asymptotic_gap

-- Single-point forecasts for fat-tailed variables (arXiv:2007.16096v1)
/-
theorem exp_growth_density_eq_pareto {X₀ t lam x : ℝ}
    (hX₀ : 0 < X₀) (ht : 0 < t) (hlam : 0 < lam) (hx : 0 < x) :
    lam / (t * x) * (X₀ / x) ^ (lam / t)
      = paretoDensity X₀ (lam / t) x
-/
#print axioms TailOptionPricing.exp_growth_density_eq_pareto
/-
theorem exp_growth_tail_index_variance_relation {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    (lam / t) * t * Real.sqrt (1 / lam ^ 2) = 1
-/
#print axioms TailOptionPricing.exp_growth_tail_index_variance_relation
/-
theorem bernoulli_variance_bound {p : ℝ} (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) :
    p * (1 - p) ≤ 1 / 4
-/
#print axioms TailOptionPricing.bernoulli_variance_bound
/-
theorem empirical_survival_variance_bound {p : ℝ} {n : ℕ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (hn_pos : 0 < n) :
    p * (1 - p) / n ≤ 1 / (4 * n)
-/
#print axioms TailOptionPricing.empirical_survival_variance_bound
/-
theorem empirical_survival_std_bound {p : ℝ} {n : ℕ}
    (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (hn_pos : 0 < n) :
    Real.sqrt (p * (1 - p) / n) ≤ 1 / (2 * Real.sqrt n)
-/
#print axioms TailOptionPricing.empirical_survival_std_bound
/-
theorem paretoMean_not_integrable_when_alpha_le_one {l α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1) (hl : 0 < l) :
    ¬ IntegrableOn (paretoMomentIntegrand l α 1) (Ioi l) volume
-/
#print axioms TailOptionPricing.paretoMean_not_integrable_when_alpha_le_one
/-
theorem paretoMean_not_integrable_at_alpha_one {l : ℝ} (hl : 0 < l) :
    ¬ IntegrableOn (paretoMomentIntegrand l 1 1) (Ioi l) volume
-/
#print axioms TailOptionPricing.paretoMean_not_integrable_at_alpha_one
/-
theorem decayingErrorVariance_ge_base (n : ℕ) (σ ε₁ κ : ℝ) (hσ : 0 ≤ σ^2) :
    σ^2 ≤ decayingErrorVariance n σ ε₁ κ
-/
#print axioms TailOptionPricing.decayingErrorVariance_ge_base
/-
theorem decayingErrorVariance_mono (σ ε₁ κ : ℝ) {n m : ℕ} (hnm : n ≤ m)
    (hσ : 0 ≤ σ^2) :
    decayingErrorVariance n σ ε₁ κ ≤ decayingErrorVariance m σ ε₁ κ
-/
#print axioms TailOptionPricing.decayingErrorVariance_mono
/-
theorem log_multiplicative_error {n : ℕ} (lamHat : ℝ) (ε : ℕ → ℝ)
    (hLam : 0 < lamHat) (hε : ∀ i ∈ Finset.range n, 0 < 1 + ε i) :
    Real.log (lamHat * ∏ i ∈ Finset.range n, (1 + ε i))
      = Real.log lamHat + ∑ i ∈ Finset.range n, Real.log (1 + ε i)
-/
#print axioms TailOptionPricing.log_multiplicative_error
/-
theorem log_one_add_le_self {ε : ℝ} (hε : -1 < ε) :
    Real.log (1 + ε) ≤ ε
-/
#print axioms TailOptionPricing.log_one_add_le_self

-- Lognormal cumulants closed forms (paper Appendix B)
/-
theorem lognormalCumulant_one (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_one n μ σ = (n : ℝ) * Real.exp (μ + σ^2 / 2)
-/
#print axioms TailOptionPricing.lognormalCumulant_one
/-
theorem lognormalCumulant_two (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_two n μ σ
      = (n : ℝ) * (Real.exp (σ^2) - 1) * Real.exp (2 * μ + σ^2)
-/
#print axioms TailOptionPricing.lognormalCumulant_two
/-
theorem lognormalCumulant_three (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_three n μ σ
      = (n : ℝ) * (Real.exp (σ^2) - 1)^2 * (Real.exp (σ^2) + 2)
          * Real.exp (3 * μ + 3 * σ^2 / 2)
-/
#print axioms TailOptionPricing.lognormalCumulant_three
/-
theorem lognormalCumulant_four (n : ℕ) (μ σ : ℝ) :
    lognormalCumulantSum_four n μ σ
      = (n : ℝ) * Real.exp (4 * μ + 2 * σ^2) * (Real.exp (σ^2) - 1)^2
          * (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
             + 3 * Real.exp (2 * σ^2) - 6)
-/
#print axioms TailOptionPricing.lognormalCumulant_four
/-
theorem lognormalSkewness (n : ℕ) (μ σ : ℝ) (hn : 0 < n) (hσ : σ ≠ 0) :
    lognormalSkewnessSum n μ σ
      = Real.sqrt (Real.exp (σ^2) - 1) * (Real.exp (σ^2) + 2) / Real.sqrt n
-/
#print axioms TailOptionPricing.lognormalSkewness
/-
theorem lognormalKurtosis (n : ℕ) (μ σ : ℝ) (hn : 0 < n) (hσ : σ ≠ 0) :
    lognormalKurtosisSum n μ σ
      = 3 + (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
             + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ)
-/
#print axioms TailOptionPricing.lognormalKurtosis
/-
theorem lognormal_kappa_tendsto_zero_as_sigma_to_zero
    (n : ℕ) (μ : ℝ) (hn : 0 < n) :
    Tendsto (fun σ => lognormalKappaProxy n μ σ) (𝓝 0) (𝓝 0)
-/
#print axioms TailOptionPricing.lognormal_kappa_tendsto_zero_as_sigma_to_zero
/-
theorem lognormal_kappa_tendsto_zero_as_n_to_infty
    (μ σ : ℝ) (hσ : σ ≠ 0) :
    Tendsto (fun n : ℕ => lognormalKappaProxy n μ σ) atTop (𝓝 0)
-- Discharged via the closed-form `C(σ) / n → 0`; no CLT needed.
-/
#print axioms TailOptionPricing.lognormal_kappa_tendsto_zero_as_n_to_infty

-- General cumulant infrastructure (todo3.md C.4 / todo4.md §4.1)
/-
theorem cumulant_zero [IsProbabilityMeasure μ] : cumulant 0 X μ = 0
-/
#print axioms TailOptionPricing.cumulant_zero
/-
theorem cumulant_one_eq_mean [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 1 X μ = μ[X]
-/
#print axioms TailOptionPricing.cumulant_one_eq_mean
/-
theorem cumulant_two_eq_variance [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 2 X μ = Var[X; μ]
-/
#print axioms TailOptionPricing.cumulant_two_eq_variance
/-
theorem cumulant_iid_sum {N : ℕ} {Y : Ω → ℝ} {X : Fin N → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (h_indep : iIndepFun X μ)
    (h_id : ∀ i, IdentDistrib (X i) Y μ μ)
    (h_int : 0 ∈ interior (integrableExpSet Y μ))
    (n : ℕ) :
    cumulant n (∑ i, X i) μ = (N : ℝ) * cumulant n Y μ
-/
#print axioms TailOptionPricing.cumulant_iid_sum
/-
theorem cumulant_three_eq_centralMoment_three
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant 3 X μ = centralMoment X 3 μ
-/
#print axioms TailOptionPricing.cumulant_three_eq_centralMoment_three
/-
theorem cumulantSkewness_eq_centralMoment_ratio
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    cumulantSkewness X μ = centralMoment X 3 μ / Var[X; μ] ^ ((3 : ℝ) / 2)
-/
#print axioms TailOptionPricing.cumulantSkewness_eq_centralMoment_ratio
/-
theorem cumulantKurtosis_eq_centralMoment_ratio
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ))
    (hVar : Var[X; μ] ≠ 0) :
    cumulantKurtosis X μ = centralMoment X 4 μ / Var[X; μ] ^ 2
-/
#print axioms TailOptionPricing.cumulantKurtosis_eq_centralMoment_ratio

-- iid triangle inequality on MAD (todo5.md Phase A): discharges the
-- structural shell of `kappa_upper_bound_subadditive`.
/-
theorem madSum_le_n_madSum_one
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ)
    (n : ℕ) :
    madSum μ X n ≤ (n : ℝ) * madSum μ X 1
-/
#print axioms TailOptionPricing.IIdTriangle.madSum_le_n_madSum_one
/-
theorem kappa_upper_bound_iid
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (h_id : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX0 : Integrable (X 0) μ)
    {n : ℕ} (hn : 1 < n)
    (hM1_pos : 0 < madSum μ X 1)
    (hM_grow : madSum μ X 1 < madSum μ X n) :
    kappa (madSum μ X) 1 n ≤ 1
-/
#print axioms TailOptionPricing.IIdTriangle.kappa_upper_bound_iid

-- Lognormal as a measure (todo5.md Phase B.1–B.4)
/-
theorem lognormalReal_Ioi_zero_eq_one (μ : ℝ) (v : ℝ≥0) :
    (lognormalReal μ v).real (Set.Ioi (0 : ℝ)) = 1
-/
#print axioms TailOptionPricing.LognormalMeasure.lognormalReal_Ioi_zero_eq_one
/-
theorem lognormalReal_real_Ioi {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    (lognormalReal μ v).real (Set.Ioi x)
      = 1 - stdNormalCdf ((Real.log x - μ) / Real.sqrt (v : ℝ))
-/
#print axioms TailOptionPricing.LognormalMeasure.lognormalReal_real_Ioi

-- Loulakis inclusion-exclusion lower bound (todo5.md Phase C.1).
/-
theorem one_sub_one_sub_pow_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≥ (n : ℝ) * p - (n.choose 2 : ℝ) * p ^ 2
-/
#print axioms TailOptionPricing.MaxIIdBound.one_sub_one_sub_pow_ge
/-
theorem prob_all_le_iid ... iid X with representative law Y ...
    μ.real {ω | ∀ i, X i ω ≤ t} = (ν.real {ω' | Y ω' ≤ t}) ^ n
-/
#print axioms TailOptionPricing.MaxIIdBound.prob_all_le_iid
/-
theorem prob_max_iid_gt ... :
    μ.real {ω | ∃ i, X i ω > t} = 1 - (ν.real {ω' | Y ω' ≤ t}) ^ n
-/
#print axioms TailOptionPricing.MaxIIdBound.prob_max_iid_gt
/-
theorem prob_max_iid_ge ... iid X with representative law Y, t real :
    (n : ℝ) * ν.real {ω' | Y ω' > t}
        - (n.choose 2 : ℝ) * (ν.real {ω' | Y ω' > t}) ^ 2
      ≤ μ.real {ω | ∃ i, X i ω > t}
-/
#print axioms TailOptionPricing.MaxIIdBound.prob_max_iid_ge

-- Sum ≥ max for nonneg iid (todo5.md Phase C.2).
/-
theorem prob_sum_ge_prob_max [IsFiniteMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_nonneg : ∀ i ω, 0 ≤ X i ω) (t : ℝ) :
    μ.real {ω | ∃ i, X i ω > t} ≤ μ.real {ω | ∑ i, X i ω > t}
-/
#print axioms TailOptionPricing.SumMaxBound.prob_sum_ge_prob_max

-- MAD layer cake (todo5.md Phase B.6).
/-
theorem mad_eq_two_tail_integral
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (m : ℝ)
    (h_mean : (∫ ω, X ω ∂μ) = m) :
    ∫ ω, |X ω - m| ∂μ
      = 2 * ∫ t in Set.Ioi (0 : ℝ), μ.real {ω | X ω > m + t}
-/
#print axioms TailOptionPricing.MadLayerCake.mad_eq_two_tail_integral

-- Lognormal Markov / Hölder bound (todo5.md Phase B.5).
/-
theorem gaussianReal_real_Ici_le (μ : ℝ) (v : ℝ≥0)
    (ε : ℝ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (gaussianReal μ v).real {x | ε ≤ x}
      ≤ Real.exp (-γ * ε + γ * μ + (v : ℝ) * γ ^ 2 / 2)
-/
#print axioms TailOptionPricing.LognormalMarkov.gaussianReal_real_Ici_le
/-
theorem lognormalReal_real_Ioi_le {μ : ℝ} {v : ℝ≥0}
    {t : ℝ} (ht : 0 < t) {γ : ℝ} (hγ : 0 ≤ γ) :
    (lognormalReal μ v).real (Set.Ioi t)
      ≤ t ^ (-γ) * Real.exp (γ * μ + (v : ℝ) * γ ^ 2 / 2)
-/
#print axioms TailOptionPricing.LognormalMarkov.lognormalReal_real_Ioi_le

-- Loulakis algebraic lower bound (todo5.md Phase C.3a).
/-
theorem M_n_lower_bound ... iid nonneg X with representative law Y₀ of mean m ... :
    2 * (n · ∫_{t>0} ℙ(Y₀ > nm + t) dt
         − C(n,2) · ∫_{t>0} ℙ(Y₀ > nm + t)² dt)
      ≤ ∫ ω, |(∑ i, X i ω) - n·m| ∂μ
-/
#print axioms TailOptionPricing.LoulakisAlgebraic.M_n_lower_bound

-- σ→∞ asymptotic of `M(1)` (todo5.md Phase B.7).
/-
theorem tendsto_Y_atTop_zero (ω : ℝ) :
    Tendsto (fun σ : ℝ => Y σ ω) atTop (𝓝 0)
-/
#print axioms TailOptionPricing.LognormalAsymptotic.tendsto_Y_atTop_zero
/-
theorem integral_Y_eq_one (σ : ℝ) :
    ∫ ω, Y σ ω ∂(gaussianReal 0 1) = 1
-/
#print axioms TailOptionPricing.LognormalAsymptotic.integral_Y_eq_one
/-
theorem integral_min_Y_one_tendsto_zero :
    Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1))
      atTop (𝓝 0)
-/
#print axioms TailOptionPricing.LognormalAsymptotic.integral_min_Y_one_tendsto_zero
/-
theorem M_one_tendsto_two :
    Tendsto (fun σ : ℝ => ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1))
      atTop (𝓝 2)
-/
#print axioms TailOptionPricing.LognormalAsymptotic.M_one_tendsto_two

-- Loulakis main liminf asymptotic (todo5.md Phase C.3b).
/-
theorem liminf_M_ratio_ge_n
    {n : ℕ} {Mn M1 An Bn : ℝ → ℝ}
    (h_lower : ∀ σ, 2 * ((n:ℝ)·An σ - C(n,2)·Bn σ) ≤ Mn σ)
    (h_Mn_nn : ∀ σ, 0 ≤ Mn σ)
    (h_Mn_triangle : ∀ σ, Mn σ ≤ (n:ℝ) * M1 σ)
    (h_M1_tend : Tendsto M1 atTop (𝓝 2))
    (h_An_tend : Tendsto An atTop (𝓝 1))
    (h_Bn_tend : Tendsto Bn atTop (𝓝 0)) :
    (n : ℝ) ≤ Filter.liminf (fun σ => Mn σ / M1 σ) atTop
-/
#print axioms TailOptionPricing.LoulakisLiminf.liminf_M_ratio_ge_n

-- Lognormal n-fold iid setup (todo6.md Phase 6.1).
/-
theorem iIndepFun_Xσ (σ : ℝ) (n : ℕ) :
    iIndepFun (fun i : Fin n => LognormalIIdSetup.Xσ σ i) (LognormalIIdSetup.μn n)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.iIndepFun_Xσ
/-
theorem identDistrib_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) :
    IdentDistrib (Xσ σ i) (Y σ) (μn n) (gaussianReal 0 1)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.identDistrib_Xσ
/-
theorem integral_Xσ_eq_one (σ : ℝ) {n : ℕ} (i : Fin n) :
    (∫ ω, Xσ σ i ω ∂(μn n)) = 1
-/
#print axioms TailOptionPricing.LognormalIIdSetup.integral_Xσ_eq_one
/-
theorem integral_sum_Xσ_eq (σ : ℝ) (n : ℕ) :
    (∫ ω, ∑ i, Xσ σ i ω ∂(μn n)) = (n : ℝ)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.integral_sum_Xσ_eq

-- Lognormal tail integrals (todo6.md Phase 6.2, 6.3 partial).
/-
theorem integral_min_Y_const_tendsto_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) k ∂(gaussianReal 0 1)) atTop (𝓝 0)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.integral_min_Y_const_tendsto_zero
/-
theorem integral_pos_part_Y_sub_n_tendsto_one {n : ℝ} (hn : 0 < n) :
    Tendsto (fun σ : ℝ => ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1)) atTop (𝓝 1)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.integral_pos_part_Y_sub_n_tendsto_one
/-
theorem An_tendsto_one {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        (gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}) atTop (𝓝 1)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.An_tendsto_one
/-
theorem Y_tail_holder {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t)
    {γ' : ℝ} (hγ' : 0 ≤ γ') :
    (gaussianReal 0 1).real {ω | Y σ ω > t}
      ≤ t ^ (-γ') * Real.exp (γ' * (γ' - 1) * σ^2 / 2)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.Y_tail_holder
/-
theorem prob_Y_gt_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ => (gaussianReal 0 1).real {ω | Y σ ω > c}) atTop (𝓝 0)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.prob_Y_gt_tendsto_zero

-- Tail-integrability helpers (MadLayerCake).
/-
theorem integrableOn_measureReal_lt_Ioi
    {X : Ω → ℝ} (hX : Integrable X μ) (hX_nn : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => μ.real {ω | X ω > t}) (Set.Ioi (0 : ℝ))
-/
#print axioms TailOptionPricing.MadLayerCake.integrableOn_measureReal_lt_Ioi
/-
theorem integrableOn_measureReal_lt_sq_Ioi
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (hX_nn : 0 ≤ᵐ[μ] X) :
    IntegrableOn (fun t : ℝ => (μ.real {ω | X ω > t}) ^ 2) (Set.Ioi (0 : ℝ))
-/
#print axioms TailOptionPricing.MadLayerCake.integrableOn_measureReal_lt_sq_Ioi

-- Lognormal-specialised tail-integrability and Bn → 0 (todo6.md Phase 6.3 closure).
/-
theorem integrableOn_prob_Y_gt_Ioi (σ : ℝ) (n : ℝ) :
    IntegrableOn (fun t : ℝ => (gaussianReal 0 1).real {ω | Y σ ω > n + t})
      (Set.Ioi (0 : ℝ))
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.integrableOn_prob_Y_gt_Ioi
/-
theorem integrableOn_prob_Y_gt_sq_Ioi (σ : ℝ) (n : ℝ) :
    IntegrableOn (fun t : ℝ => ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2)
      (Set.Ioi (0 : ℝ))
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.integrableOn_prob_Y_gt_sq_Ioi
/-
theorem Bn_le_prob_mul_An (σ : ℝ) (n : ℝ) :
    ∫ t in Set.Ioi (0:ℝ), ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2
      ≤ (gaussianReal 0 1).real {ω | Y σ ω > n}
        * ∫ t in Set.Ioi (0:ℝ), (gaussianReal 0 1).real {ω | Y σ ω > n + t}
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.Bn_le_prob_mul_An
/-
theorem Bn_tendsto_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (0:ℝ),
        ((gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}) ^ 2) atTop (𝓝 0)
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.Bn_tendsto_zero

-- Lognormal-specialised Loulakis liminf (todo6.md Phase 6.4 wire-up).
/-
theorem Mn_le_n_M1 (n : ℕ) (σ : ℝ) : Mn n σ ≤ (n : ℝ) * M1 σ
-/
#print axioms TailOptionPricing.LoulakisLognormal.Mn_le_n_M1
/-
theorem M_n_lower_lognormal (n : ℕ) (σ : ℝ) :
    (2 : ℝ) * ((n : ℝ) * An n σ - (n.choose 2 : ℝ) * Bn n σ) ≤ Mn n σ
-/
#print axioms TailOptionPricing.LoulakisLognormal.M_n_lower_lognormal
/-
theorem liminf_M_ratio_lognormal_ge_n
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ Filter.liminf (fun σ : ℝ => Mn n σ / M1 σ) atTop
-/
#print axioms TailOptionPricing.LoulakisLognormal.liminf_M_ratio_lognormal_ge_n
/-
theorem tendsto_M_ratio_lognormal_eq_n {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => Mn n σ / M1 σ) atTop (𝓝 (n : ℝ))
-/
#print axioms TailOptionPricing.LoulakisLognormal.tendsto_M_ratio_lognormal_eq_n
/-
theorem Mn_tendsto_two_mul_n {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => Mn n σ) atTop (𝓝 ((n : ℝ) * 2))
-/
#print axioms TailOptionPricing.LoulakisLognormal.Mn_tendsto_two_mul_n
/-
theorem kappa_lognormal_tendsto_one {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun σ : ℝ =>
        (2 : ℝ) - Real.log n / (Real.log (Mn n σ) - Real.log (M1 σ)))
      atTop (𝓝 1)
-/
#print axioms TailOptionPricing.LoulakisLognormal.kappa_lognormal_tendsto_one
/-
theorem Mn_one_eq_M1 (σ : ℝ) : Mn 1 σ = M1 σ
-/
#print axioms TailOptionPricing.LoulakisLognormal.Mn_one_eq_M1
/-
theorem kappa_lognormal_tendsto_one_canonical {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun σ : ℝ => TailOptionPricing.kappa (fun k => Mn k σ) 1 n)
      atTop (𝓝 1)
-/
#print axioms TailOptionPricing.LoulakisLognormal.kappa_lognormal_tendsto_one_canonical

-- ============================================================================
-- arXiv:1802.05495v3 — additional paper-claim theorems (strict re-audit pass).
-- ============================================================================

-- Section IV-A (α-stable basin, paper Eq. 4): characteristic-function identity,
-- sum-of-stable closure, and stable-class κ invariance.
/-
theorem stable_charfun_pow_alpha_ne_one
    (α β μ σ : ℝ) (n : ℕ) (hn : 0 < n)
    (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hσ_pos : 0 < σ) (t : ℝ) :
    (stableCharacteristicFunction α β μ σ t) ^ n
      = stableCharacteristicFunction α β ((n : ℝ) * μ)
          ((n : ℝ) ^ ((1 : ℝ) / α) * σ) t
-/
#print axioms TailOptionPricing.stable_charfun_pow_alpha_ne_one
/-
theorem stable_charfun_pow_alpha_eq_one (β μ σ : ℝ) (n : ℕ) (t : ℝ) :
    (stableCharacteristicFunction 1 β μ σ t) ^ n = …
-/
#print axioms TailOptionPricing.stable_charfun_pow_alpha_eq_one
/-
theorem stable_sum_stable {φ Sn_charfun : ℝ → ℂ} {α β μ σ : ℝ} {n : ℕ}
    (hn : 0 < n) (hα_ne_one : α ≠ 1) (hX : StableClass φ α β μ σ)
    (h_iid : ∀ t, Sn_charfun t = (φ t) ^ n) :
    StableClass Sn_charfun α β ((n : ℝ) * μ) ((n : ℝ) ^ ((1 : ℝ) / α) * σ)
-/
#print axioms TailOptionPricing.stable_sum_stable
/-
theorem stable_class_kappa_invariance {M : ℕ → ℝ} {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α)
    (hM_form : ∀ k : ℕ, 0 < k → M k = c * (k : ℝ) ^ ((1 : ℝ) / stableAlphaBar α))
    {n₀ n : ℕ} (hn₀ : 0 < n₀) (h_lt : n₀ < n) :
    kappa M n₀ n = 2 - stableAlphaBar α
-/
#print axioms TailOptionPricing.stable_class_kappa_invariance

-- Section IV-B / Table I — closed-form κ for distributions in the paper table.
-- Row 1: Student T α; Row 2: Pareto α; Row 4: Normal with switching-variance;
-- Row 5: Lognormal explicit κ + Loulakis "star" form.
/-
theorem kappa_studentT_general {α : ℝ}
    (hT : 0 < studentTInner α)
    (h_den : 2 * Real.log (studentTInner α) + Real.log Real.pi ≠ 0) :
    kappa (tableIMAD (studentTRatio α)) 1 2 = studentTKappa α
-/
#print axioms TailOptionPricing.kappa_studentT_general
/-
theorem kappa_pareto_general (α : ℝ) :
    kappa (tableIMAD (paretoRatio α)) 1 2 = paretoKappa α
-/
#print axioms TailOptionPricing.kappa_pareto_general
/-
theorem kappa_normal_switching_variance (σ a p : ℝ) :
    kappa (tableIMAD (normalSwitchingVarianceRatio σ a p)) 1 2
      = normalSwitchingVarianceKappa σ a p
-/
#print axioms TailOptionPricing.kappa_normal_switching_variance
/-
theorem kappa_lognormal_explicit (σ : ℝ) (n : ℕ) :
    kappa (tableIMAD (lognormalExplicitRatio σ n)) 1 2
      = lognormalExplicitKappa σ n
-/
#print axioms TailOptionPricing.kappa_lognormal_explicit
/-
theorem lognormal_kappa_star (σ : ℝ) (n : ℕ) : lognormalKappaStar σ n = …
-/
#print axioms TailOptionPricing.lognormal_kappa_star
/-
theorem kappa_lognormal_star (σ : ℝ) {n : ℕ} (hn : 1 < n) :
    kappa (lognormalStarMAD σ n) 1 n = lognormalKappaStar σ n
-/
#print axioms TailOptionPricing.kappa_lognormal_star

-- Section IV-B-3 (Pearson IV approximation, paper Eq. 12 + Eq. 13).
/-
theorem pearsonIV_mad_eq (a₀ a₁ b₀ b₁ b₂ m fm intCentered : ℝ)
    (h_den_ne : a₁ - 2 * b₂ ≠ 0)
    (_h_mean_constraint : (a₁ - 2 * b₂) * m = b₁ - a₀)
    (h_ibp : (a₁ - 2 * b₂) * intCentered = pearsonIVQuad b₀ b₁ b₂ m * fm) :
    2 * intCentered = pearsonIVMADClosed a₀ a₁ b₀ b₁ b₂ m fm
-/
#print axioms TailOptionPricing.pearsonIV_mad_eq
/-
theorem pearsonIV_mad_eq_paper (paper-form Eq. 13)
-/
#print axioms TailOptionPricing.pearsonIV_mad_eq_paper
/-
theorem pearsonIV_lognormal_match_a1 (n : ℕ) (σ : ℝ) :
    pearsonIV_a1_lognormal n σ = 1  -- paper Eq. 12 "a₁ = 1" coefficient
-/
#print axioms TailOptionPricing.pearsonIV_lognormal_match_a1
/-
theorem pearsonIVLognormalDen_pos (n : ℕ) (σ : ℝ) (hn : 0 < n) :
    0 < pearsonIVLognormalDen n σ
-/
#print axioms TailOptionPricing.pearsonIVLognormalDen_pos
/-
theorem pearsonIV_lognormal_match_b2_nonneg (n : ℕ) (σ : ℝ) (hn : 0 < n) :
    0 ≤ pearsonIV_b2_lognormal n σ
-/
#print axioms TailOptionPricing.pearsonIV_lognormal_match_b2_nonneg

-- Section V-F / paper Eq. 18 (Gaussian switching-mean κ₁ + sign criterion).
/-
theorem gaussianSwitchingMean_kappa1 {σ d : ℝ}
    (hN : 0 < gaussianSwitchingMeanNum σ d)
    (hD : 0 < gaussianSwitchingMeanDen σ d)
    (hND_sq : gaussianSwitchingMeanNum σ d ^ 2
        ≠ Real.pi * gaussianSwitchingMeanDen σ d ^ 2) :
    kappa (gaussianSwitchingMeanMAD σ d) 1 2 = gaussianSwitchingMeanKappa1 σ d
-/
#print axioms TailOptionPricing.gaussianSwitchingMean_kappa1
/-
theorem gaussianSwitchingMean_kappa_neg_iff {σ d : ℝ}
    (hN : 0 < gaussianSwitchingMeanNum σ d)
    (hD : 0 < gaussianSwitchingMeanDen σ d) :
    gaussianSwitchingMeanKappa1 σ d < 0 ↔ …
-/
#print axioms TailOptionPricing.gaussianSwitchingMean_kappa_neg_iff

-- Cubic Student T (paper Section V-C / Eq. 11, Appendix A).
/-
theorem incompleteGamma_loulakis (n : ℕ) :
    incompleteGamma (n + 1) n
      = (n.factorial : ℝ) * Real.exp (-(n : ℝ)) *
          ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k.factorial : ℝ)
-/
#print axioms TailOptionPricing.incompleteGamma_loulakis
/-
theorem cubicStudentSumMAD_loulakis_form {n : ℕ} (hn : 2 ≤ n) :
    cubicStudentSumMAD n
      = (2 * Real.sqrt 3 * (n.factorial : ℝ)) / (Real.pi * (n : ℝ) ^ n) *
          ∑ k ∈ Finset.range n, (n : ℝ) ^ k / (k.factorial : ℝ)
-/
#print axioms TailOptionPricing.cubicStudentSumMAD_loulakis_form
/-
theorem cubicStudentSumDensity_eq_half_fourier_avg {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    (cubicStudentSumDensity n y : ℂ)
      = (cubicStudentSumFourierHalf n (Complex.I * y)
          + cubicStudentSumFourierHalf n (-(Complex.I * y))) / (2 * Real.pi)
-/
#print axioms TailOptionPricing.cubicStudentSumDensity_eq_half_fourier_avg
/-
theorem cubicStudentSumFourierHalf_eq_expIntegralNeg {n : ℕ} (ψ : ℂ) :
    cubicStudentSumFourierHalf n ψ = … * expIntegralNeg n ((n : ℂ) - ψ / √3)
-/
#print axioms TailOptionPricing.cubicStudentSumFourierHalf_eq_expIntegralNeg
/-
theorem cubicStudentSumDensity_via_exponentialIntegral
    {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :  paper Eq. 11 in `expIntegralNeg` form
-/
#print axioms TailOptionPricing.cubicStudentSumDensity_via_exponentialIntegral
/-
theorem incompleteGamma_laplace_asymptotic_thm :  paper Appendix C asymptotic
    Tendsto (fun n : ℕ =>
        Real.exp n * (n : ℝ) ^ (-(n : ℝ)) * incompleteGamma (n + 1) n /
          Real.sqrt n)
      atTop (𝓝 (Real.sqrt (Real.pi / 2)))
-/
#print axioms TailOptionPricing.CubicStudentLaplace.incompleteGamma_laplace_asymptotic_thm

-- Appendix B (lognormal moments + κ-proxy closed form).
/-
lemma lognormalMoment_one (μ σ : ℝ) :
    lognormalMoment 1 μ σ = Real.exp (μ + σ^2 / 2)
-/
#print axioms TailOptionPricing.lognormalMoment_one
/-
lemma lognormalMoment_two (μ σ : ℝ) :
    lognormalMoment 2 μ σ = Real.exp (2 * μ + 2 * σ^2)
-/
#print axioms TailOptionPricing.lognormalMoment_two
/-
lemma lognormalMoment_three (μ σ : ℝ) :
    lognormalMoment 3 μ σ = Real.exp (3 * μ + 9 * σ^2 / 2)
-/
#print axioms TailOptionPricing.lognormalMoment_three
/-
lemma lognormalMoment_four (μ σ : ℝ) :
    lognormalMoment 4 μ σ = Real.exp (4 * μ + 8 * σ^2)
-/
#print axioms TailOptionPricing.lognormalMoment_four
/-
lemma lognormalKappaProxy_closed_form (n : ℕ) (μ σ : ℝ) (hn : 0 < n) :
    lognormalKappaProxy n μ σ
      = (Real.exp (4 * σ^2) + 2 * Real.exp (3 * σ^2)
         + 3 * Real.exp (2 * σ^2) - 6) / (n : ℝ)
-/
#print axioms TailOptionPricing.lognormalKappaProxy_closed_form

-- Cumulant / moment relations (paper Appendix B prerequisite).
/-
theorem centralMoment_four_eq_cumulant_four_plus
    [IsProbabilityMeasure μ] (h : 0 ∈ interior (integrableExpSet X μ)) :
    centralMoment X 4 μ = cumulant 4 X μ + 3 * cumulant 2 X μ ^ 2
-/
#print axioms TailOptionPricing.centralMoment_four_eq_cumulant_four_plus

-- Loulakis abstract subexp lower / triangle upper bounds on M(n)/M(1).
/-
theorem lognormal_M_ratio_le_n {M : ℕ → ℝ} {n : ℕ}
    (hM1_pos : 0 < M 1) (h_subadditive : M n ≤ (n:ℝ) * M 1) :
    M n / M 1 ≤ (n:ℝ)
-/
#print axioms TailOptionPricing.lognormal_M_ratio_le_n
/-
theorem lognormal_M_ratio_ge_n_subexp {M : ℕ → ℝ} {n : ℕ}
    (hM1_pos : 0 < M 1) (h_subexp : (n:ℝ) * M 1 ≤ M n) :
    (n:ℝ) ≤ M n / M 1
-/
#print axioms TailOptionPricing.lognormal_M_ratio_ge_n_subexp

-- ============================================================================
-- arXiv:1802.05495v3 — exhaustive Stats.Kappa coverage (helpers & infra).
--   Every public theorem/lemma in Stats/Kappa/ now has a Verify entry.
-- ============================================================================

-- Section III (n-ν sample size translation; paper Eq. 7 supporting facts).
/-
theorem n_g_of_n_nu_n_nu : n_g (n_nu n_g κ_g) κ_g = n_g
-/
#print axioms TailOptionPricing.n_g_of_n_nu_n_nu
/-
theorem n_nu_n_g_of_n_nu : n_nu (n_g n_ν κ_g) κ_g = n_ν
-/
#print axioms TailOptionPricing.n_nu_n_g_of_n_nu
/-
theorem n_nu_bidirectional : the n-ν / n_g bijection
-/
#print axioms TailOptionPricing.n_nu_bidirectional
/-
theorem n_min_le_of_witness {Mν Mg : ℕ → ℝ} {ng k : ℕ}
    (hk : 0 < k) (h : sampleMeanMAD Mν k ≤ sampleMeanMAD Mg ng) :
    n_min Mν Mg ng ≤ k
-/
#print axioms TailOptionPricing.n_min_le_of_witness
/-
theorem n_min_mem {Mν Mg : ℕ → ℝ} {ng : ℕ}
    (hw : ∃ k, 0 < k ∧ sampleMeanMAD Mν k ≤ sampleMeanMAD Mg ng) :
    0 < n_min Mν Mg ng ∧ sampleMeanMAD Mν (n_min Mν Mg ng) ≤ sampleMeanMAD Mg ng
-/
#print axioms TailOptionPricing.n_min_mem

-- Cumulant alt indexing.
/-
theorem cumulant_zero_index [IsProbabilityMeasure μ] : cumulant 0 X μ = 0
-/
#print axioms TailOptionPricing.cumulant_zero_index

-- Cubic Student T helpers (paper Appendix A, Eq. 11 — exp-integral form).
/-
theorem cubicStudentSumFourierHalf_integrand_integrableOn  -- Fourier integrand
-/
#print axioms TailOptionPricing.cubicStudentSumFourierHalf_integrand_integrableOn
/-
theorem Ioi_translate_one_C : { ω | 1 < ω } = { ω | 0 < ω } translated  -- substitution
-/
#print axioms TailOptionPricing.Ioi_translate_one_C
/-
theorem incompleteGamma_laplace_asymptotic :
    Tendsto (fun n : ℕ => …)  -- Appendix C asymptotic (original form, DCT-discharged)
-/
#print axioms TailOptionPricing.incompleteGamma_laplace_asymptotic

-- Poisson CDF asymptotic helpers (Appendix A / todo3.md C.3, route b).
/-
theorem tendsto_stirling_rearranged :
    Tendsto (fun n => Stirling-rearranged ratio) atTop (𝓝 …)
-/
#print axioms TailOptionPricing.PoissonCDF.tendsto_stirling_rearranged
/-
theorem tendsto_incompleteGamma_div_factorial :
    Tendsto (fun n => incompleteGamma (n+1) n / n.factorial) atTop (𝓝 (1/2))
-/
#print axioms TailOptionPricing.PoissonCDF.tendsto_incompleteGamma_div_factorial
/-
theorem tendsto_pow_exp_div_factorial :
    Tendsto (fun n => n^n · e^(-n) · √n / n.factorial) atTop (𝓝 (1/√(2π)))
-/
#print axioms TailOptionPricing.PoissonCDF.tendsto_pow_exp_div_factorial

-- Pearson IV ODE-based density derivative (paper Section IV-B-3).
/-
theorem pearsonIV_aux_deriv  : ODE structure for Pearson IV density
-/
#print axioms TailOptionPricing.pearsonIV_aux_deriv

-- Loulakis structural-shell auxiliary lemmas (todo5 / todo6 supporting).
/-
theorem integral_pos_part_eq_tail_integral
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) (m : ℝ) :
    ∫ ω, max (X ω - m) 0 ∂μ = ∫ t in Set.Ioi 0, μ.real {ω | X ω > m + t}
-/
#print axioms TailOptionPricing.MadLayerCake.integral_pos_part_eq_tail_integral
/-
theorem integral_pos_part_eq_An (σ n : ℝ) :
    ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1)
      = ∫ t in Set.Ioi 0, (gaussianReal 0 1).real {ω | Y σ ω > n + t}
-/
#print axioms TailOptionPricing.LognormalTailIntegrals.integral_pos_part_eq_An
/-
theorem integral_exp_neg_half_sq_Ioi  -- Gaussian half-line integral, Laplace asym proof
-/
#print axioms TailOptionPricing.CubicStudentLaplace.integral_exp_neg_half_sq_Ioi
/-
theorem setOf_exists_gt_subset_setOf_sum_gt
    {n : ℕ} {X : Fin n → Ω → ℝ} (h_nonneg : ∀ i ω, 0 ≤ X i ω) (t : ℝ) :
    {ω | ∃ i, X i ω > t} ⊆ {ω | ∑ i, X i ω > t}
-/
#print axioms TailOptionPricing.SumMaxBound.setOf_exists_gt_subset_setOf_sum_gt
/-
theorem madSum_one [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX0 : Integrable (X 0) μ) :
    madSum μ X 1 = ∫ ω, |X 0 ω - μ[X 0]| ∂μ
-/
#print axioms TailOptionPricing.IIdTriangle.madSum_one

-- Lognormal n-fold iid family — positivity, integrability, measurability.
/-
theorem Xσ_pos (σ : ℝ) {n : ℕ} (i : Fin n) (ω : Ωspace n) : 0 < Xσ σ i ω
-/
#print axioms TailOptionPricing.LognormalIIdSetup.Xσ_pos
/-
theorem Xσ_nonneg (σ : ℝ) {n : ℕ} (i : Fin n) (ω : Ωspace n) : 0 ≤ Xσ σ i ω
-/
#print axioms TailOptionPricing.LognormalIIdSetup.Xσ_nonneg
/-
theorem measurable_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) : Measurable (Xσ σ i)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.measurable_Xσ
/-
theorem integrable_Xσ (σ : ℝ) {n : ℕ} (i : Fin n) : Integrable (Xσ σ i) (μn n)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.integrable_Xσ
/-
theorem integrable_sum_Xσ (σ : ℝ) (n : ℕ) :
    Integrable (fun ω => ∑ i, Xσ σ i ω) (μn n)
-/
#print axioms TailOptionPricing.LognormalIIdSetup.integrable_sum_Xσ
/-
theorem Y_pos (σ ω : ℝ) : 0 < Y σ ω
-/
#print axioms TailOptionPricing.LognormalAsymptotic.Y_pos
/-
theorem Y_nonneg (σ ω : ℝ) : 0 ≤ Y σ ω
-/
#print axioms TailOptionPricing.LognormalAsymptotic.Y_nonneg
/-
theorem Mn_nonneg (n : ℕ) (σ : ℝ) : 0 ≤ Mn n σ
-/
#print axioms TailOptionPricing.LoulakisLognormal.Mn_nonneg
