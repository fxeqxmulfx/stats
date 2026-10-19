module

/-
  Arbitrage boundaries: Eqs. (8)–(10) from Taleb et al.

  Abstract calculus of the matched-butterfly argument.  Given a "BSC"-side
  function matching the power-law `C` at an anchor `K₁` and the mixed
  butterfly inequality, the derivative of `BSC` is bounded by that of `C` —
  hence (Breeden–Litzenberger) the BS tail probability dominates the
  power-law tail at the matching anchor, yielding a lower bound on `α`.
-/
public import Stats.Calculus

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace TailOptionPricing

/-- **Abstract Eq. (9).**  If `f` and `g` are differentiable at `K₁`, agree at
    `K₁`, and the mixed butterfly `f(K₁+ΔK) + g(K₁-ΔK) ≥ 2·f(K₁)` holds
    along `0⁺`, then the derivative of `g` is bounded above by that of `f`
    at `K₁`. -/
theorem deriv_le_of_matched_butterfly {f g : ℝ → ℝ} {f' g' K₁ : ℝ}
    (hf : HasDerivAt f f' K₁) (hg : HasDerivAt g g' K₁) (h_match : f K₁ = g K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        f (K₁ + ΔK) + g (K₁ - ΔK) ≥ 2 * f K₁) :
    g' ≤ f' := by
  set φ : ℝ → ℝ := fun ΔK => f (K₁ + ΔK) + g (K₁ - ΔK) - 2 * f K₁ with hφdef
  have h_inner_add : HasDerivAt (fun ΔK : ℝ => K₁ + ΔK) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add K₁
  have h_inner_sub : HasDerivAt (fun ΔK : ℝ => K₁ - ΔK) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub K₁
  have hf_at : HasDerivAt f f' (K₁ + 0) := by rw [add_zero]; exact hf
  have hg_at : HasDerivAt g g' (K₁ - 0) := by rw [sub_zero]; exact hg
  have hf_comp : HasDerivAt (fun ΔK : ℝ => f (K₁ + ΔK)) f' 0 := by
    convert hf_at.comp 0 h_inner_add using 1 <;> simp [Function.comp_def]
  have hg_comp : HasDerivAt (fun ΔK : ℝ => g (K₁ - ΔK)) (-g') 0 := by
    convert hg_at.comp 0 h_inner_sub using 1 <;> simp [Function.comp_def]
  have hφ : HasDerivAt φ (f' - g') 0 := by
    have h_sum : HasDerivAt (fun ΔK : ℝ => f (K₁ + ΔK) + g (K₁ - ΔK))
        (f' + (-g')) 0 := hf_comp.add hg_comp
    have h := h_sum.sub_const (2 * f K₁)
    have h_eq : f' + (-g') = f' - g' := by ring
    rw [← h_eq]; exact h
  have hφ0 : φ 0 = 0 := by simp [hφdef, h_match]; ring
  have h_slope : Tendsto (fun ΔK : ℝ => ΔK⁻¹ • (φ (0 + ΔK) - φ 0))
      (𝓝[>] 0) (𝓝 (f' - g')) := hφ.tendsto_slope_zero_right
  have h_slope_nn : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
      0 ≤ ΔK⁻¹ • (φ (0 + ΔK) - φ 0) := by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)), h_butterfly]
      with ΔK hΔK_pos h_b
    have hΔK_pos' : 0 < ΔK := hΔK_pos
    have h_φ_nn : 0 ≤ φ ΔK := by
      simp only [hφdef]; linarith
    simp only [zero_add, hφ0, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hΔK_pos'.le) h_φ_nn
  have h_diff_nn : (0 : ℝ) ≤ f' - g' := ge_of_tendsto h_slope h_slope_nn
  linarith

/-- **Eq. (9), corrected, specialised to the power-law `callPrice`.**
    With matching `BSC(K₁) = C(K₁)` and the mixed-butterfly Eq. (8), any
    differentiable BSC at `K₁` satisfies `BSC'(K₁) ≤ −(l/K₁)^α`. -/
theorem callPrice_dominates_BSC_deriv {l α K₁ : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK₁ : l < K₁) {BSC : ℝ → ℝ} {bsc' : ℝ}
    (h_BSC : HasDerivAt BSC bsc' K₁)
    (h_match : BSC K₁ = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + BSC (K₁ - ΔK) ≥ 2 * callPrice l α K₁) :
    bsc' ≤ -((l / K₁) ^ α) :=
  deriv_le_of_matched_butterfly (callPrice_hasDerivAt hα hl hK₁) h_BSC
    h_match.symm h_butterfly

/-- **Eq. (10), corrected — explicit lower bound on `α`.**  Given a
    "BS tail probability" `Q ∈ (0, 1)` such that `(l/K₁)^α ≤ Q` (which is the
    Eq. (9)-style necessary condition translated via Breeden–Litzenberger),
    the tail index `α` is bounded below by `log(Q) / log(l/K₁)`. -/
theorem alpha_lower_bound {l α K₁ Q : ℝ} (hl : 0 < l) (hK₁ : l < K₁)
    (h_ineq : (l / K₁) ^ α ≤ Q) :
    Real.log Q / Real.log (l / K₁) ≤ α := by
  have hl_div_pos : 0 < l / K₁ := div_pos hl (hl.trans hK₁)
  have hl_div_lt : l / K₁ < 1 := by rw [div_lt_one (hl.trans hK₁)]; exact hK₁
  have hLog_neg : Real.log (l / K₁) < 0 := Real.log_neg hl_div_pos hl_div_lt
  have hLα_pos : 0 < (l / K₁) ^ α := Real.rpow_pos_of_pos hl_div_pos α
  have h_log : Real.log ((l / K₁) ^ α) ≤ Real.log Q :=
    Real.log_le_log hLα_pos h_ineq
  rw [Real.log_rpow hl_div_pos] at h_log
  rw [div_le_iff_of_neg hLog_neg]
  linarith

/-! ### Existence of matched butterfly via convexity.

    The matched-butterfly inequality (Eq. 8) is taken as a no-arbitrage
    hypothesis throughout the paper.  We show here that it is *automatic*
    — for *every* `ΔK` keeping both wings inside the convex domain, not
    merely "small `ΔK`" — once the BSC surface is matched to the power-law
    `C` in *both value and slope* at the anchor `K₁` and is convex on the
    domain.

    The proof is the two-line tangent-line bound for convex differentiable
    functions: a convex graph lies above its tangent at any point.  No
    Taylor expansion or third-order estimate is required; the conclusion
    is global on the convex domain rather than local. -/

/-- **Tangent-line bound** for a convex function with a derivative at one
    point: the graph of `f` lies above the tangent line at `K₁`.  This is
    the standard "first-order" characterisation of convexity, packaged as a
    helper for the matched-butterfly construction below. -/
private lemma tangent_le_of_convexOn_hasDerivAt {f : ℝ → ℝ} {f' K₁ : ℝ}
    {S : Set ℝ} (hf_conv : ConvexOn ℝ S f) (hK₁ : K₁ ∈ S)
    (hf : HasDerivAt f f' K₁) :
    ∀ y ∈ S, f K₁ + f' * (y - K₁) ≤ f y := by
  intro y hy
  rcases lt_trichotomy y K₁ with hyK | hyK | hyK
  · have h := hf_conv.slope_le_of_hasDerivAt hy hK₁ hyK hf
    rw [slope_def_field] at h
    have hKy : 0 < K₁ - y := sub_pos.mpr hyK
    rw [div_le_iff₀ hKy] at h
    nlinarith
  · subst hyK; simp
  · have h := hf_conv.le_slope_of_hasDerivAt hK₁ hy hyK hf
    rw [slope_def_field] at h
    have hyK' : 0 < y - K₁ := sub_pos.mpr hyK
    rw [le_div_iff₀ hyK'] at h
    linarith

/-- **Existence of matched butterfly — abstract.**  Suppose `f` and `g` are
    convex on a set `S`, agree at `K₁ ∈ S`, and have a *common* derivative
    `m` at `K₁` (value match `f K₁ = g K₁` and slope match
    `HasDerivAt f m K₁`, `HasDerivAt g m K₁`).  Then the matched-butterfly
    inequality
        f(K₁ + ΔK) + g(K₁ - ΔK) ≥ 2 · f K₁
    holds for *every* `ΔK` such that both `K₁ ± ΔK` lie in `S`.

    No "small `ΔK`" hypothesis: the conclusion is global on the convex
    domain.  In particular, this discharges the no-arbitrage hypothesis of
    Eq. (8) whenever the BSC pricing surface is calibrated to the power-law
    `C` in both value and slope at the anchor. -/
theorem matched_butterfly_of_convex {f g : ℝ → ℝ} {m K₁ : ℝ} {S : Set ℝ}
    (hf_conv : ConvexOn ℝ S f) (hg_conv : ConvexOn ℝ S g)
    (hf : HasDerivAt f m K₁) (hg : HasDerivAt g m K₁)
    (hK₁ : K₁ ∈ S) (h_match : f K₁ = g K₁) :
    ∀ {ΔK : ℝ}, K₁ + ΔK ∈ S → K₁ - ΔK ∈ S →
      f (K₁ + ΔK) + g (K₁ - ΔK) ≥ 2 * f K₁ := by
  intro ΔK h_plus h_minus
  have h1 := tangent_le_of_convexOn_hasDerivAt hf_conv hK₁ hf (K₁ + ΔK) h_plus
  have h2 := tangent_le_of_convexOn_hasDerivAt hg_conv hK₁ hg (K₁ - ΔK) h_minus
  have e1 : (K₁ + ΔK) - K₁ = ΔK := by ring
  have e2 : (K₁ - ΔK) - K₁ = -ΔK := by ring
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- **Existence of matched butterfly — power-law specialisation.**  When the
    BSC surface is convex on `Ioi l` and matched to the power-law `C` in
    both value and slope at `K₁ > l` (slope necessarily equal to
    `-((l/K₁)^α)`, the Breeden–Litzenberger derivative of `C`), the
    matched-butterfly inequality of Eq. (8) holds for every `ΔK` keeping
    both wings inside `(l, ∞)`. -/
theorem callPrice_matched_butterfly_of_BSC_convex {l α K₁ : ℝ} (hα : 1 < α)
    (hl : 0 < l) (hK₁ : l < K₁) {BSC : ℝ → ℝ}
    (hBSC_conv : ConvexOn ℝ (Set.Ioi l) BSC)
    (hBSC_deriv : HasDerivAt BSC (-((l / K₁) ^ α)) K₁)
    (h_match : BSC K₁ = callPrice l α K₁) :
    ∀ {ΔK : ℝ}, K₁ + ΔK ∈ Set.Ioi l → K₁ - ΔK ∈ Set.Ioi l →
      callPrice l α (K₁ + ΔK) + BSC (K₁ - ΔK) ≥ 2 * callPrice l α K₁ :=
  matched_butterfly_of_convex
    (callPrice_strictConvexOn hα hl).convexOn hBSC_conv
    (callPrice_hasDerivAt hα hl hK₁) hBSC_deriv hK₁ h_match.symm

/-- **Generic Eq. (9).**  The abstract Eq. (9) instantiated for the case where
    the BSC arises from a continuous integrable tail function `F_BS` via
    `BSC(K) = ∫_K^∞ F_BS(s) ds`:  the matching + butterfly hypotheses force the
    BS tail at `K₁` to dominate the power-law tail:

        F_BS(K₁) ≥ (l / K₁)^α  ─  BS tail must be at least as fat at K₁. -/
theorem BSC_tail_dominates_at_match {l α K₁ : ℝ} (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁)
    {F_BS : ℝ → ℝ} {a : ℝ} (ha : a < K₁)
    (hF_int : IntegrableOn F_BS (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F_BS (Set.Ioi a))
    (h_match : (∫ s in Set.Ioi K₁, F_BS s) = callPrice l α K₁)
    (h_butterfly : ∀ᶠ ΔK in 𝓝[>] (0:ℝ),
        callPrice l α (K₁ + ΔK) + (∫ s in Set.Ioi (K₁ - ΔK), F_BS s)
          ≥ 2 * callPrice l α K₁) :
    (l / K₁) ^ α ≤ F_BS K₁ := by
  have h_BSC_deriv : HasDerivAt (fun K' => ∫ s in Set.Ioi K', F_BS s) (-F_BS K₁) K₁ :=
    hasDerivAt_integral_Ioi ha hF_int hF_cont
  have h_main := callPrice_dominates_BSC_deriv hα hl hK₁ h_BSC_deriv h_match h_butterfly
  linarith

/-! ### No-arbitrage inequalities across strikes (Pareto-internal arb tests).

    Standard no-arb tests on a call surface — vertical-spread positivity,
    Lipschitz slope, and butterfly positivity — instantiated for the
    strong-Pareto closed-form `callPrice`.  Together they provide the
    "Pareto-internal" leg of arbitrage screening: any market call quotes
    purportedly drawn from a Pareto law must obey these inequalities. -/

/-- **Vertical-spread positivity (strict).**  Under the strong Pareto law,
    the call price `K ↦ C(K)` is strictly antitone on `[l, ∞)`.  In
    particular, for any `l ≤ K₁ < K₂` the bull spread is strictly
    positive: `C(K₁) − C(K₂) > 0`. -/
theorem callPrice_strictAntitoneOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictAntiOn (callPrice l α) (Set.Ici l) := by
  intro K₁ hK₁ K₂ hK₂ h_lt
  rw [callPrice_eq hα hl hK₁, callPrice_eq hα hl hK₂]
  have hK₁_pos : 0 < K₁ := hl.trans_le hK₁
  have hK₂_pos : 0 < K₂ := hK₁_pos.trans h_lt
  have hα1_pos : 0 < α - 1 := by linarith
  have hl_pow_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
  have h_K1_pow_pos : 0 < K₁ ^ (α - 1) := Real.rpow_pos_of_pos hK₁_pos _
  have h_K2_pow_pos : 0 < K₂ ^ (α - 1) := Real.rpow_pos_of_pos hK₂_pos _
  have h_inc : K₁ ^ (α - 1) < K₂ ^ (α - 1) :=
    Real.rpow_lt_rpow hK₁_pos.le h_lt hα1_pos
  have h_dec : K₂ ^ (1 - α) < K₁ ^ (1 - α) := by
    rw [show (1 - α : ℝ) = -(α - 1) from by ring,
        Real.rpow_neg hK₁_pos.le, Real.rpow_neg hK₂_pos.le]
    exact (inv_lt_inv₀ h_K2_pow_pos h_K1_pow_pos).mpr h_inc
  have h_num_lt : l ^ α * K₂ ^ (1 - α) < l ^ α * K₁ ^ (1 - α) :=
    (mul_lt_mul_iff_of_pos_left hl_pow_pos).mpr h_dec
  exact div_lt_div_of_pos_right h_num_lt hα1_pos

/-- **Slope (Lipschitz) bounds for the Pareto call price.**  For
    `l < K₁ < K₂`, the discrete Breeden–Litzenberger bracket holds:
        `(l/K₂)^α · (K₂ − K₁) ≤ C(K₁) − C(K₂) ≤ (l/K₁)^α · (K₂ − K₁)`.
    The lower bound says vertical spreads price at least the survival at
    the *right* strike; the upper bound says they price at most the
    survival at the *left* strike.  Direct from convexity: the secant
    slope is sandwiched between the derivatives at the two endpoints. -/
theorem callPrice_slope_bounds {l α K₁ K₂ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l < K₁) (h_lt : K₁ < K₂) :
    (l / K₂) ^ α * (K₂ - K₁) ≤ callPrice l α K₁ - callPrice l α K₂ ∧
    callPrice l α K₁ - callPrice l α K₂ ≤ (l / K₁) ^ α * (K₂ - K₁) := by
  have hK₁_pos : 0 < K₁ := hl.trans hK₁
  have hΔ_pos : 0 < K₂ - K₁ := by linarith
  have hConv : ConvexOn ℝ (Set.Ici l) (callPrice l α) :=
    (callPrice_strictConvexOn_Ici hα hl).convexOn
  have h_K₁_in : K₁ ∈ Set.Ici l := hK₁.le
  have h_K₂_in : K₂ ∈ Set.Ici l := (hK₁.trans h_lt).le
  have h_d₁ : HasDerivAt (callPrice l α) (-((l / K₁) ^ α)) K₁ :=
    callPrice_hasDerivAt hα hl hK₁
  have h_d₂ : HasDerivAt (callPrice l α) (-((l / K₂) ^ α)) K₂ :=
    callPrice_hasDerivAt hα hl (hK₁.trans h_lt)
  have h_left :=
    hConv.le_slope_of_hasDerivAt h_K₁_in h_K₂_in h_lt h_d₁
  have h_right :=
    hConv.slope_le_of_hasDerivAt h_K₁_in h_K₂_in h_lt h_d₂
  rw [slope_def_field] at h_left h_right
  rw [le_div_iff₀ hΔ_pos] at h_left
  rw [div_le_iff₀ hΔ_pos] at h_right
  exact ⟨by linarith, by linarith⟩

/-- **Asymmetric butterfly positivity (strict).**  For
    `l ≤ K₁ < K₂ < K₃` in `[l, ∞)`, the call price satisfies the
    discrete strict-convexity (asymmetric butterfly) inequality
        `(K₃ − K₁) · C(K₂) < (K₃ − K₂) · C(K₁) + (K₂ − K₁) · C(K₃)`.
    Equivalent to a strictly positive butterfly portfolio
    `(K₃ − K₂)·{long K₁} − (K₃ − K₁)·{long K₂} + (K₂ − K₁)·{long K₃}`.
    The symmetric case `K₂ = (K₁ + K₃)/2` recovers `callPrice_butterfly`. -/
theorem callPrice_butterfly_asymmetric {l α K₁ K₂ K₃ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK₁ : l ≤ K₁) (h₁₂ : K₁ < K₂) (h₂₃ : K₂ < K₃) :
    (K₃ - K₁) * callPrice l α K₂ <
      (K₃ - K₂) * callPrice l α K₁ + (K₂ - K₁) * callPrice l α K₃ := by
  have hK₃_K₁ : 0 < K₃ - K₁ := by linarith
  have hK₂_K₁ : 0 < K₂ - K₁ := by linarith
  have hK₃_K₂ : 0 < K₃ - K₂ := by linarith
  have hK₃_K₁_ne : K₃ - K₁ ≠ 0 := hK₃_K₁.ne'
  set lam : ℝ := (K₃ - K₂) / (K₃ - K₁) with hlam_def
  set mu  : ℝ := (K₂ - K₁) / (K₃ - K₁) with hmu_def
  have hlam_pos : 0 < lam := div_pos hK₃_K₂ hK₃_K₁
  have hmu_pos  : 0 < mu  := div_pos hK₂_K₁ hK₃_K₁
  have hlammu : lam + mu = 1 := by
    show (K₃ - K₂) / (K₃ - K₁) + (K₂ - K₁) / (K₃ - K₁) = 1
    field_simp
    ring
  have h_combo : lam * K₁ + mu * K₃ = K₂ := by
    show (K₃ - K₂) / (K₃ - K₁) * K₁ + (K₂ - K₁) / (K₃ - K₁) * K₃ = K₂
    field_simp
    ring
  have hK₁_in : K₁ ∈ Set.Ici l := hK₁
  have hK₃_in : K₃ ∈ Set.Ici l := hK₁.trans (h₁₂.trans h₂₃).le
  have hK₁_ne_K₃ : K₁ ≠ K₃ := by linarith
  have h := (callPrice_strictConvexOn_Ici hα hl).2 hK₁_in hK₃_in hK₁_ne_K₃
              hlam_pos hmu_pos hlammu
  simp only [smul_eq_mul] at h
  rw [h_combo] at h
  have h_mul : (K₃ - K₁) * callPrice l α K₂ <
      (K₃ - K₁) * (lam * callPrice l α K₁ + mu * callPrice l α K₃) :=
    (mul_lt_mul_iff_of_pos_left hK₃_K₁).mpr h
  have h_simp :
      (K₃ - K₁) * (lam * callPrice l α K₁ + mu * callPrice l α K₃)
        = (K₃ - K₂) * callPrice l α K₁ + (K₂ - K₁) * callPrice l α K₃ := by
    show (K₃ - K₁) * ((K₃ - K₂) / (K₃ - K₁) * callPrice l α K₁
            + (K₂ - K₁) / (K₃ - K₁) * callPrice l α K₃)
          = (K₃ - K₂) * callPrice l α K₁ + (K₂ - K₁) * callPrice l α K₃
    field_simp
  linarith

end TailOptionPricing
