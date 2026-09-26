/-
  Calculus of the strong-Pareto call price.

  ## Stats.Calculus.CallPrice — generic BL + Breeden–Litzenberger for the call.

  Contains:
    * Generic FTC for `K ↦ ∫_K^∞ F(s) ds` (`hasDerivAt_integral_Ioi`).
    * Breeden–Litzenberger first/second derivatives for the call price.
    * Continuity on `Ici l`, strict convexity on `Ioi l` and on the
      closed `Ici l`, pure-power-law butterfly bound.

  See `Stats/Calculus.lean` for the umbrella.
-/
import Stats.Pareto

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ### Generic Breeden–Litzenberger.

    For *any* continuous integrable tail function `F`, the call price
    `K ↦ ∫_K^∞ F(s) ds` has derivative `−F(K)`.  This is the layer-cake form
    of Breeden–Litzenberger that doesn't rely on a specific (Pareto)
    distribution. -/

/-- General FTC for the half-line integral as a function of the lower limit:
    if `F` is continuous and integrable on `(a, ∞)`, then `K ↦ ∫_K^∞ F(s) ds`
    has derivative `−F(K)` at every `K > a`. -/
theorem hasDerivAt_integral_Ioi
    {F : ℝ → ℝ} {a K : ℝ} (haK : a < K)
    (hF_int : IntegrableOn F (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F (Set.Ioi a)) :
    HasDerivAt (fun K' => ∫ s in Set.Ioi K', F s) (-F K) K := by
  set b : ℝ := K + 1 with hb_def
  have hKb : K < b := lt_add_one K
  have hab : a < b := haK.trans hKb
  have hF_int_Ioi_b : IntegrableOn F (Set.Ioi b) volume :=
    hF_int.mono_set (Set.Ioi_subset_Ioi hab.le)
  have h_eq : ∀ᶠ K' in 𝓝 K,
      (∫ s in Set.Ioi K', F s) = (∫ s in K'..b, F s) + (∫ s in Set.Ioi b, F s) := by
    filter_upwards [Ioo_mem_nhds haK hKb] with K' hK'
    have hF_int_K' : IntegrableOn F (Set.Ioi K') volume :=
      hF_int.mono_set (Set.Ioi_subset_Ioi hK'.1.le)
    have h := integral_Ioi_sub_Ioi hF_int_K' hK'.2.le
    linarith
  have h_contAt : ContinuousAt F K :=
    hF_cont.continuousAt (isOpen_Ioi.mem_nhds haK)
  have h_meas : StronglyMeasurableAtFilter F (𝓝 K) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF_cont K haK
  have h_subset : Set.uIcc K b ⊆ Set.Ioi a := by
    rw [Set.uIcc_of_le hKb.le]
    exact fun x hx => haK.trans_le hx.1
  have h_int_int : IntervalIntegrable F volume K b :=
    (hF_cont.mono h_subset).intervalIntegrable
  have h_deriv_int : HasDerivAt (fun K' => ∫ s in K'..b, F s) (-F K) K :=
    integral_hasDerivAt_left h_int_int h_meas h_contAt
  have h_deriv_total : HasDerivAt
      (fun K' => (∫ s in K'..b, F s) + (∫ s in Set.Ioi b, F s)) (-F K) K :=
    h_deriv_int.add_const (∫ s in Set.Ioi b, F s)
  exact h_deriv_total.congr_of_eventuallyEq h_eq

/-- **Continuity corollary.**  For continuous integrable `F` on `(a, ∞)`, the
    call-price functional `K ↦ ∫_K^∞ F(s) ds` is continuous on `(a, ∞)`. -/
theorem continuousOn_integral_Ioi
    {F : ℝ → ℝ} {a : ℝ}
    (hF_int : IntegrableOn F (Set.Ioi a) volume)
    (hF_cont : ContinuousOn F (Set.Ioi a)) :
    ContinuousOn (fun K => ∫ s in Set.Ioi K, F s) (Set.Ioi a) :=
  fun _ hK =>
    (hasDerivAt_integral_Ioi hK hF_int hF_cont).continuousAt.continuousWithinAt

/-! ### Breeden–Litzenberger for the strong Pareto. -/

/-- **First derivative:** `dC/dK = −(l/K)^α`. -/
theorem callPrice_hasDerivAt {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    HasDerivAt (callPrice l α) (-((l / K) ^ α)) K := by
  have hK_pos : 0 < K := hl.trans hK
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hKα_ne : K ^ α ≠ 0 := (Real.rpow_pos_of_pos hK_pos α).ne'
  have h_id : HasDerivAt (fun K : ℝ => K) 1 K := hasDerivAt_id K
  have h_pow := (h_id.rpow_const (p := 1 - α) (Or.inl hK_pos.ne')).const_mul (l ^ α)
  have h_form := h_pow.div_const (α - 1)
  have h_local : callPrice l α =ᶠ[𝓝 K]
      (fun K' : ℝ => l ^ α * K' ^ (1 - α) / (α - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hK] with K' hK'
    exact callPrice_eq hα hl (le_of_lt hK')
  have h := h_form.congr_of_eventuallyEq h_local
  convert h using 1
  rw [show (1 - α - 1 : ℝ) = -α from by ring,
      Real.div_rpow hl.le hK_pos.le, Real.rpow_neg hK_pos.le]
  field_simp
  ring

/-- The first derivative of the call price equals `−ℙ(S > K)`, recovering the
    survival function (the layer-cake derivative). -/
theorem callPrice_deriv_eq_neg_survival {l α K : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK : l < K) :
    HasDerivAt (callPrice l α) (-(survival l α K)) K := by
  simpa [survival] using callPrice_hasDerivAt hα hl hK

/-- **Second derivative (Breeden–Litzenberger):** `d²C/dK² = α · l^α / K^(α+1)`,
    which is the density `f_S(K)` of the Pareto law on `[l, ∞)`. -/
theorem callPrice_hasDerivAt_secondOrder {l α K : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hK : l < K) :
    HasDerivAt (fun K' => -((l / K') ^ α)) (α * l ^ α / K ^ (α + 1)) K := by
  have hK_pos : 0 < K := hl.trans hK
  have hKα_ne : K ^ α ≠ 0 := (Real.rpow_pos_of_pos hK_pos α).ne'
  have hKα1_ne : K ^ (α + 1) ≠ 0 := (Real.rpow_pos_of_pos hK_pos (α + 1)).ne'
  have h_id : HasDerivAt (fun K : ℝ => K) 1 K := hasDerivAt_id K
  have h_pow := (h_id.rpow_const (p := -α) (Or.inl hK_pos.ne')).const_mul (l ^ α)
  have h := h_pow.neg
  have h_local : (fun K' : ℝ => -((l / K') ^ α)) =ᶠ[𝓝 K]
      (fun K' : ℝ => -(l ^ α * K' ^ (-α))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hK_pos] with K' hK'_pos
    have hK'_pos' : 0 < K' := hK'_pos
    rw [Real.div_rpow hl.le hK'_pos'.le, Real.rpow_neg hK'_pos'.le]
    field_simp
  have hh := h.congr_of_eventuallyEq h_local
  convert hh using 1
  rw [show (-α - 1 : ℝ) = -(α + 1) from by ring, Real.rpow_neg hK_pos.le]
  field_simp

/-! ### Breeden–Litzenberger for the shadow put.

    By `putCallParity_Pareto`, `putShadow K = callPrice K + K − α·l/(α−1)`,
    so the put derivatives are obtained from the call derivatives by adding
    the affine correction.  In particular `dP̂/dK² = dC/dK²` (the put has the
    same second derivative — namely the strong-Pareto density — as the call). -/

/-- **First derivative of the shadow put:** `dP̂/dK = 1 − (l/K)^α = ℙ(S ≤ K)`.
    Recovers the CDF, mirroring `callPrice_hasDerivAt`. -/
theorem putShadow_hasDerivAt {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    HasDerivAt (putShadow l α) (1 - (l / K) ^ α) K := by
  have h_local : putShadow l α =ᶠ[𝓝 K]
      fun K' => callPrice l α K' + K' - α * l / (α - 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hK] with K' hK'
    have h := putCallParity_Pareto hα hl hK'.le
    linarith
  have h_call := callPrice_hasDerivAt hα hl hK
  have h_id : HasDerivAt (fun K' : ℝ => K') 1 K := hasDerivAt_id K
  have h1 : HasDerivAt (fun K' : ℝ => callPrice l α K' + K')
      (-((l / K) ^ α) + 1) K := h_call.add h_id
  have h2 := h1.sub_const (α * l / (α - 1))
  have hh := h2.congr_of_eventuallyEq h_local
  convert hh using 1
  ring

/-- The first derivative of the shadow put equals `1 − ℙ(S > K)`, i.e. the
    CDF (the layer-cake-derivative of the put). -/
theorem putShadow_deriv_eq_one_sub_survival {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    HasDerivAt (putShadow l α) (1 - survival l α K) K := by
  simpa [survival] using putShadow_hasDerivAt hα hl hK

/-- **Second derivative of the shadow put (Breeden–Litzenberger):**
        d²P̂/dK² = α · l^α / K^(α+1),
    the strong-Pareto density `f_S(K)` — same as `callPrice_hasDerivAt_secondOrder`. -/
theorem putShadow_hasDerivAt_secondOrder {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l < K) :
    HasDerivAt (fun K' => 1 - (l / K') ^ α) (α * l ^ α / K ^ (α + 1)) K := by
  have h_call := callPrice_hasDerivAt_secondOrder hα hl hK
  have h := h_call.add_const (1 : ℝ)
  have h_eq : (fun K' : ℝ => -((l / K') ^ α) + 1)
            = (fun K' : ℝ => 1 - (l / K') ^ α) := by
    funext K'; ring
  rw [h_eq] at h
  exact h

/-! ### Convexity, continuity at the boundary, butterfly bound. -/

/-- **Convexity of the call price.**  As a consequence of the Breeden–Litzenberger
    second-derivative formula and the strict positivity of the Pareto density
    on `(l, ∞)`, the call price `K ↦ C(K)` is strictly convex on `(l, ∞)`. -/
theorem callPrice_strictConvexOn {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Ioi l) (callPrice l α) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi l)
  · intro K hK
    exact (callPrice_hasDerivAt hα hl hK).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro K hK
    have hK_pos : 0 < K := hl.trans hK
    have h_eqLocal : deriv (callPrice l α) =ᶠ[𝓝 K] fun y : ℝ => -((l / y) ^ α) := by
      filter_upwards [isOpen_Ioi.mem_nhds hK] with y hy
      exact (callPrice_hasDerivAt hα hl hy).deriv
    have h2 : HasDerivAt (deriv (callPrice l α)) (α * l ^ α / K ^ (α + 1)) K :=
      (callPrice_hasDerivAt_secondOrder hα hl hK).congr_of_eventuallyEq h_eqLocal
    have h_eq : deriv^[2] (callPrice l α) K = α * l ^ α / K ^ (α + 1) := h2.deriv
    rw [show (deriv^[2] (callPrice l α)) K = deriv (deriv (callPrice l α)) K from rfl,
        h2.deriv]
    have hα_pos : 0 < α := by linarith
    have hlα_pos : 0 < l ^ α := Real.rpow_pos_of_pos hl _
    have hKα1_pos : 0 < K ^ (α + 1) := Real.rpow_pos_of_pos hK_pos _
    positivity

/-- **Continuity of the power-law call price on the closed half-line.**
    Since `callPrice = (closed form)` on `Ici l` (Result 1, Eq. 2), and the
    closed form `K ↦ l^α · K^(1-α) / (α-1)` is continuous on `Ici l ⊆ Ioi 0`,
    the call price is continuous up to and including the Karamata anchor `l`. -/
theorem callPrice_continuousOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    ContinuousOn (callPrice l α) (Set.Ici l) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_closed_form_cont :
      ContinuousOn (fun K => l ^ α * K ^ (1 - α) / (α - 1)) (Set.Ici l) := by
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const continuousOn_id (fun K hK => Or.inl ?_)
    exact (hl.trans_le hK).ne'
  refine h_closed_form_cont.congr (fun K hK => ?_)
  exact callPrice_eq hα hl hK

/-- **Strict convexity on the closed half-line.**  Combining
    `callPrice_continuousOn_Ici` with the fact that `K ↦ −(l/K)^α`
    (= the first derivative) is strictly increasing on `Ioi l`, we obtain
    strict convexity of the call price on the *closed* half-line `Ici l`. -/
theorem callPrice_strictConvexOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Set.Ici l) (callPrice l α) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici l)
        (callPrice_continuousOn_Ici hα hl)
  rw [interior_Ici]
  intro K₁ hK₁ K₂ hK₂ h_lt
  have hK₁_pos : 0 < K₁ := hl.trans hK₁
  have hK₂_pos : 0 < K₂ := hl.trans hK₂
  have hd₁ : deriv (callPrice l α) K₁ = -((l / K₁) ^ α) :=
    (callPrice_hasDerivAt hα hl hK₁).deriv
  have hd₂ : deriv (callPrice l α) K₂ = -((l / K₂) ^ α) :=
    (callPrice_hasDerivAt hα hl hK₂).deriv
  rw [hd₁, hd₂, neg_lt_neg_iff]
  refine Real.rpow_lt_rpow (div_nonneg hl.le hK₂_pos.le) ?_ (by linarith : 0 < α)
  exact div_lt_div_of_pos_left hl hK₁_pos h_lt

/-- **Eq. (8) — pure-power-law butterfly bound.**  As an immediate consequence
    of strict convexity, for any anchor `K₁ > l` and any nonzero perturbation
    `ΔK` keeping both wings strictly inside `(l, ∞)`, the call surface
    satisfies the strict butterfly inequality
        2 · C(K₁) < C(K₁ + ΔK) + C(K₁ - ΔK).
    This corresponds to Eq. (8) in the paper specialised to the case where
    *both* wing prices are taken under the power-law model. -/
theorem callPrice_butterfly {l α K₁ ΔK : ℝ} (hα : 1 < α) (hl : 0 < l)
    (hΔK : 0 < ΔK) (hΔK_lt : ΔK < K₁ - l) :
    2 * callPrice l α K₁ < callPrice l α (K₁ + ΔK) + callPrice l α (K₁ - ΔK) := by
  have hConvex := callPrice_strictConvexOn hα hl
  have hK₁_plus : K₁ + ΔK ∈ Ioi l := by simp [mem_Ioi]; linarith
  have hK₁_minus : K₁ - ΔK ∈ Ioi l := by simp [mem_Ioi]; linarith
  have hne : K₁ + ΔK ≠ K₁ - ΔK := by intro h; linarith
  have h := hConvex.2 hK₁_plus hK₁_minus hne
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have h_mid : (1/2 : ℝ) * (K₁ + ΔK) + 1/2 * (K₁ - ΔK) = K₁ := by ring
  simp only [smul_eq_mul] at h
  rw [h_mid] at h
  linarith


end TailOptionPricing
