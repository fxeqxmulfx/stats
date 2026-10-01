/-
  Strong-Pareto core: put-call parity from
    Taleb–Yarckin–Mann–Delic–Spitznagel,
    "Tail Option Pricing Under Power Laws", arXiv:1908.02347v3 (March 2023).

  ## Stats.Pareto.PutCallParity — put-call parity in the Pareto family.

  Contains the closed-form put price (`putShadow`) and the
  put-call parity statements for both the strong-Pareto density
  and the upside-Pareto returns density (Result 2 form).

  See `Stats/Pareto.lean` for the umbrella module.
-/
import Stats.Pareto.Put
import Stats.Pareto.Returns

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ## Put-call parity within the strong-Pareto density.

    The paper's `callPrice` (Result 1) is for `S ~ strong Pareto(l, α)` on
    `[l, ∞)`.  The paper's `putPrice` (Result 3) is under a *different*
    density: Pareto on the negative return `r := (S₀ − S)/S₀`, rescaled to
    `S ∈ [0, (1−l)S₀]`.  Classical put–call parity therefore cannot relate
    `callPrice` and `putPrice` directly — they live on different probability
    spaces.  The paper's mention of "put-call parity arbitrage" (Section III)
    refers to *classical* model-free PCP `C(K) − P(K) = S₀ − K` as an
    external no-arbitrage tool to recover deep-ITM left-tail calls from the
    put model, not a model-derived parity.

    Within the same Pareto density on `[l, ∞)` used by `callPrice`, the
    BS-style proof transports cleanly.  We define a "shadow put" as
    `E[(K − S)⁺]` under that density and obtain the analogue of
    `putCallParity_BS`:
        callPrice(K) − putShadow(K) = E[S] − K = α·l/(α−1) − K.
    `putShadow` is *not* the paper's `putPrice` — it is a hypothetical put
    under the call's own density, used only to state this parity. -/

/-- "Shadow" put under the strong-Pareto density on `[l, ∞)`:
        P̂(K) := ∫_l^K (K − s) · α·l^α / s^(α+1) ds = E[(K − S)⁺].
    Not the paper's `putPrice`; used only for the within-density parity. -/
noncomputable def putShadow (l α K : ℝ) : ℝ :=
  ∫ s in l..K, (K - s) * (α * l ^ α / s ^ (α + 1))

/-- Antiderivative of the `putShadow` integrand on `Ioi 0`. -/
private noncomputable def putShadowAntideriv (l α K s : ℝ) : ℝ :=
  -K * l ^ α * s ^ (-α) + α * l ^ α * s ^ (1 - α) / (α - 1)

private lemma hasDerivAt_putShadowAntideriv {l α K s : ℝ}
    (hα : 1 < α) (hs : 0 < s) :
    HasDerivAt (putShadowAntideriv l α K)
      ((K - s) * (α * l ^ α / s ^ (α + 1))) s := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hs_ne : (s : ℝ) ≠ 0 := hs.ne'
  have h_id : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
  have h_neg_α : HasDerivAt (fun t : ℝ => t ^ (-α))
      ((-α) * s ^ (-α - 1)) s := by
    have := h_id.rpow_const (p := -α) (Or.inl hs_ne)
    convert this using 1
    ring
  have h_one_α : HasDerivAt (fun t : ℝ => t ^ (1 - α))
      ((1 - α) * s ^ (-α)) s := by
    have := h_id.rpow_const (p := 1 - α) (Or.inl hs_ne)
    convert this using 1
    rw [show (1 - α - 1 : ℝ) = -α from by ring]
    ring
  have h_F1 : HasDerivAt (fun t : ℝ => -K * l ^ α * t ^ (-α))
      (-K * l ^ α * ((-α) * s ^ (-α - 1))) s :=
    h_neg_α.const_mul (-K * l ^ α)
  have h_F2 : HasDerivAt (fun t : ℝ => α * l ^ α * t ^ (1 - α) / (α - 1))
      (α * l ^ α * ((1 - α) * s ^ (-α)) / (α - 1)) s :=
    (h_one_α.const_mul (α * l ^ α)).div_const (α - 1)
  have h_sum := h_F1.add h_F2
  convert h_sum using 1 <;> try rfl
  have hpow_pos : 0 < s ^ (α + 1) := Real.rpow_pos_of_pos hs _
  have hpow_ne : s ^ (α + 1) ≠ 0 := hpow_pos.ne'
  have h1 : s ^ (-α - 1) = (s ^ (α + 1))⁻¹ := by
    rw [show (-α - 1 : ℝ) = -(α + 1) from by ring, Real.rpow_neg hs.le]
  have h2 : s ^ (-α) = (s ^ (α + 1))⁻¹ * s := by
    rw [show (-α : ℝ) = -(α + 1) + 1 from by ring,
        Real.rpow_add hs, Real.rpow_one, Real.rpow_neg hs.le]
  rw [h1, h2]
  field_simp
  ring

/-- **Closed form of the shadow put.**
        P̂(K) = l^α · K^(1−α) / (α−1) + K − α·l/(α−1). -/
theorem putShadow_eq {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    putShadow l α K =
      l ^ α * K ^ (1 - α) / (α - 1) + K - α * l / (α - 1) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hK_pos : 0 < K := hl.trans_le hK
  have h_pos_uIcc : ∀ s ∈ Set.uIcc l K, 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hK] at hs
    exact lt_of_lt_of_le hl hs.1
  have hF_deriv : ∀ s ∈ Set.uIcc l K,
      HasDerivAt (putShadowAntideriv l α K)
        ((K - s) * (α * l ^ α / s ^ (α + 1))) s :=
    fun s hs => hasDerivAt_putShadowAntideriv hα (h_pos_uIcc s hs)
  have hF_int : IntervalIntegrable
      (fun s => (K - s) * (α * l ^ α / s ^ (α + 1))) volume l K := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hK]
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hl hs.1
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (by fun_prop) ?_
    refine ContinuousAt.div (by fun_prop) ?_
      (Real.rpow_pos_of_pos hs_pos _).ne'
    exact ContinuousAt.rpow_const (by fun_prop) (Or.inl hs_pos.ne')
  unfold putShadow
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hF_int]
  unfold putShadowAntideriv
  have hKK : K * K ^ (-α) = K ^ (1 - α) := by
    rw [show (1 - α : ℝ) = 1 + -α from by ring,
        Real.rpow_add hK_pos, Real.rpow_one]
  have hll0 : l ^ α * l ^ (-α) = 1 := by
    rw [← Real.rpow_add hl,
        show α + -α = (0 : ℝ) from by ring, Real.rpow_zero]
  have hll1 : l ^ α * l ^ (1 - α) = l := by
    rw [← Real.rpow_add hl,
        show α + (1 - α) = (1 : ℝ) from by ring, Real.rpow_one]
  have h_F_K :
      -K * l ^ α * K ^ (-α) + α * l ^ α * K ^ (1 - α) / (α - 1)
        = l ^ α * K ^ (1 - α) / (α - 1) := by
    have hrw : -K * l ^ α * K ^ (-α) = -(l ^ α * (K * K ^ (-α))) := by ring
    rw [hrw, hKK]
    field_simp
    ring
  have h_F_l :
      -K * l ^ α * l ^ (-α) + α * l ^ α * l ^ (1 - α) / (α - 1)
        = -K + α * l / (α - 1) := by
    have h1 : -K * l ^ α * l ^ (-α) = -K * (l ^ α * l ^ (-α)) := by ring
    have h2 : α * l ^ α * l ^ (1 - α) / (α - 1)
            = α * (l ^ α * l ^ (1 - α)) / (α - 1) := by ring
    rw [h1, hll0, h2, hll1]
    ring
  rw [h_F_K, h_F_l]
  ring

/-- **Pareto put-call parity (within-density).**
        callPrice(K) − putShadow(K) = E[S] − K = α·l/(α−1) − K.
    Analogue of `putCallParity_BS` for the strong-Pareto law.  Does *not*
    relate to the paper's `putPrice`, which is under a different (downside-
    return) density. -/
theorem putCallParity_Pareto {l α K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    callPrice l α K - putShadow l α K = α * l / (α - 1) - K := by
  rw [callPrice_eq hα hl hK, putShadow_eq hα hl hK]
  ring

/-- **Risk-neutral Pareto calibration.**  For any spot `S₀ > 0`, choosing
    the Karamata constant `l := S₀·(α−1)/α` makes the strong-Pareto mean
    equal to the spot, `E[S] = α·l/(α−1) = S₀`, so `putCallParity_Pareto`
    collapses to the classical `C(K) − P̂(K) = S₀ − K`.

    Mirror of `putCallParity_BS` under risk-neutral parametrisation
    (`μ = −v/2`, giving `E[S_T] = S₀`). -/
theorem putCallParity_Pareto_riskNeutral {α S₀ K : ℝ}
    (hα : 1 < α) (hS₀ : 0 < S₀) (hK : S₀ * (α - 1) / α ≤ K) :
    callPrice (S₀ * (α - 1) / α) α K - putShadow (S₀ * (α - 1) / α) α K
      = S₀ - K := by
  have hα_pos : 0 < α := by linarith
  have hα_ne : (α : ℝ) ≠ 0 := hα_pos.ne'
  have hα1_pos : 0 < α - 1 := by linarith
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := hα1_pos.ne'
  have hl_pos : 0 < S₀ * (α - 1) / α :=
    div_pos (mul_pos hS₀ hα1_pos) hα_pos
  have h := putCallParity_Pareto hα hl_pos hK
  have h_mean : α * (S₀ * (α - 1) / α) / (α - 1) = S₀ := by field_simp
  linarith

/-! ## Put-call parity within the upside-Pareto returns density (Result 2).

    Mirror of `putCallParity_Pareto` for the upside-return Pareto density
    used by `callPriceReturns`.  `putShadowReturns(K)` is `E[(K − S)⁺]`
    under the same density (positive return `r := (S − S₀)/S₀ ~ Pareto(l, α)`,
    equivalently `S ∈ [S₀·(1+l), ∞)`).  Parity:
        callPriceReturns(K) − putShadowReturns(K) = E[S] − K
                                                  = S₀ + α·l·S₀/(α−1) − K. -/

/-- "Shadow" put under the upside-return Pareto density on `[S₀·(1+l), ∞)`.
    Not the paper's `putPrice`; used only for the Result 2 within-density
    parity. -/
noncomputable def putShadowReturns (l α S₀ K : ℝ) : ℝ :=
  ∫ s in S₀ * (1 + l)..K, (K - s) * (α * (l * S₀) ^ α / (s - S₀) ^ (α + 1))

/-- Antiderivative of the `putShadowReturns` integrand on `Ioi S₀`. -/
private noncomputable def putShadowReturnsAntideriv (l α S₀ K s : ℝ) : ℝ :=
  -(K - S₀) * (l * S₀) ^ α * (s - S₀) ^ (-α) +
    α * (l * S₀) ^ α * (s - S₀) ^ (1 - α) / (α - 1)

private lemma hasDerivAt_putShadowReturnsAntideriv {l α S₀ K s : ℝ}
    (hα : 1 < α) (hs_S₀ : 0 < s - S₀) :
    HasDerivAt (putShadowReturnsAntideriv l α S₀ K)
      ((K - s) * (α * (l * S₀) ^ α / (s - S₀) ^ (α + 1))) s := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hs_S₀_ne : (s - S₀) ≠ 0 := hs_S₀.ne'
  have h_base : HasDerivAt (fun s : ℝ => s - S₀) 1 s := by
    simpa using (hasDerivAt_id s).sub_const S₀
  have h_neg_α : HasDerivAt (fun s : ℝ => (s - S₀) ^ (-α))
      ((-α) * (s - S₀) ^ (-α - 1)) s := by
    have := h_base.rpow_const (p := -α) (Or.inl hs_S₀_ne)
    convert this using 1
    ring
  have h_one_α : HasDerivAt (fun s : ℝ => (s - S₀) ^ (1 - α))
      ((1 - α) * (s - S₀) ^ (-α)) s := by
    have := h_base.rpow_const (p := 1 - α) (Or.inl hs_S₀_ne)
    convert this using 1
    rw [show (1 - α - 1 : ℝ) = -α from by ring]
    ring
  have h_F1 : HasDerivAt
      (fun s : ℝ => -(K - S₀) * (l * S₀) ^ α * (s - S₀) ^ (-α))
      (-(K - S₀) * (l * S₀) ^ α * ((-α) * (s - S₀) ^ (-α - 1))) s :=
    h_neg_α.const_mul (-(K - S₀) * (l * S₀) ^ α)
  have h_F2 : HasDerivAt
      (fun s : ℝ => α * (l * S₀) ^ α * (s - S₀) ^ (1 - α) / (α - 1))
      (α * (l * S₀) ^ α * ((1 - α) * (s - S₀) ^ (-α)) / (α - 1)) s :=
    (h_one_α.const_mul (α * (l * S₀) ^ α)).div_const (α - 1)
  have h_sum := h_F1.add h_F2
  convert h_sum using 1 <;> try rfl
  have hpow_pos : 0 < (s - S₀) ^ (α + 1) := Real.rpow_pos_of_pos hs_S₀ _
  have hpow_ne : (s - S₀) ^ (α + 1) ≠ 0 := hpow_pos.ne'
  have h1 : (s - S₀) ^ (-α - 1) = ((s - S₀) ^ (α + 1))⁻¹ := by
    rw [show (-α - 1 : ℝ) = -(α + 1) from by ring, Real.rpow_neg hs_S₀.le]
  have h2 : (s - S₀) ^ (-α) = ((s - S₀) ^ (α + 1))⁻¹ * (s - S₀) := by
    rw [show (-α : ℝ) = -(α + 1) + 1 from by ring,
        Real.rpow_add hs_S₀, Real.rpow_one, Real.rpow_neg hs_S₀.le]
  rw [h1, h2]
  field_simp
  ring

/-- **Closed form of the upside-returns shadow put.**
        P̂↑(K) = (l·S₀)^α · (K − S₀)^(1−α) / (α−1) + (K − S₀) − α·l·S₀/(α−1). -/
theorem putShadowReturns_eq {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) ≤ K) :
    putShadowReturns l α S₀ K =
      (l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1)
        + (K - S₀) - α * (l * S₀) / (α - 1) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hK_S₀_pos : 0 < K - S₀ := by nlinarith
  have h_pos_uIcc : ∀ s ∈ Set.uIcc (S₀ * (1 + l)) K, 0 < s - S₀ := by
    intro s hs
    rw [Set.uIcc_of_le hK] at hs
    nlinarith [hs.1]
  have hF_deriv : ∀ s ∈ Set.uIcc (S₀ * (1 + l)) K,
      HasDerivAt (putShadowReturnsAntideriv l α S₀ K)
        ((K - s) * (α * (l * S₀) ^ α / (s - S₀) ^ (α + 1))) s :=
    fun s hs => hasDerivAt_putShadowReturnsAntideriv hα (h_pos_uIcc s hs)
  have hF_int : IntervalIntegrable
      (fun s => (K - s) * (α * (l * S₀) ^ α / (s - S₀) ^ (α + 1)))
        volume (S₀ * (1 + l)) K := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hK]
    intro s hs
    have hs_S₀_pos : 0 < s - S₀ := by nlinarith [hs.1]
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (by fun_prop) ?_
    refine ContinuousAt.div (by fun_prop) ?_
      (Real.rpow_pos_of_pos hs_S₀_pos _).ne'
    refine ContinuousAt.rpow_const ?_ (Or.inl hs_S₀_pos.ne')
    fun_prop
  unfold putShadowReturns
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hF_int]
  unfold putShadowReturnsAntideriv
  have h_rw1 : S₀ * (1 + l) - S₀ = l * S₀ := by ring
  rw [h_rw1]
  have hKK : (K - S₀) * (K - S₀) ^ (-α) = (K - S₀) ^ (1 - α) := by
    rw [show (1 - α : ℝ) = 1 + -α from by ring,
        Real.rpow_add hK_S₀_pos, Real.rpow_one]
  have hll0 : (l * S₀) ^ α * (l * S₀) ^ (-α) = 1 := by
    rw [← Real.rpow_add hlS₀_pos,
        show α + -α = (0 : ℝ) from by ring, Real.rpow_zero]
  have hll1 : (l * S₀) ^ α * (l * S₀) ^ (1 - α) = l * S₀ := by
    rw [← Real.rpow_add hlS₀_pos,
        show α + (1 - α) = (1 : ℝ) from by ring, Real.rpow_one]
  have h_F_K :
      -(K - S₀) * (l * S₀) ^ α * (K - S₀) ^ (-α)
        + α * (l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1)
        = (l * S₀) ^ α * (K - S₀) ^ (1 - α) / (α - 1) := by
    have hrw : -(K - S₀) * (l * S₀) ^ α * (K - S₀) ^ (-α)
             = -((l * S₀) ^ α * ((K - S₀) * (K - S₀) ^ (-α))) := by ring
    rw [hrw, hKK]
    field_simp
    ring
  have h_F_l :
      -(K - S₀) * (l * S₀) ^ α * (l * S₀) ^ (-α)
        + α * (l * S₀) ^ α * (l * S₀) ^ (1 - α) / (α - 1)
        = -(K - S₀) + α * (l * S₀) / (α - 1) := by
    have h1 : -(K - S₀) * (l * S₀) ^ α * (l * S₀) ^ (-α)
            = -(K - S₀) * ((l * S₀) ^ α * (l * S₀) ^ (-α)) := by ring
    have h2 : α * (l * S₀) ^ α * (l * S₀) ^ (1 - α) / (α - 1)
            = α * ((l * S₀) ^ α * (l * S₀) ^ (1 - α)) / (α - 1) := by ring
    rw [h1, hll0, h2, hll1]
    ring
  rw [h_F_K, h_F_l]
  ring

/-- **Pareto put-call parity (within-density, Result 2).**
        callPriceReturns(K) − putShadowReturns(K)
            = S₀ + α·l·S₀/(α−1) − K = E[S] − K.
    Mirror of `putCallParity_Pareto` for Result 2. -/
theorem putCallParity_Pareto_returns {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀)
    (hK : S₀ * (1 + l) ≤ K) :
    callPriceReturns l α S₀ K - putShadowReturns l α S₀ K =
      S₀ + α * (l * S₀) / (α - 1) - K := by
  rw [callPriceReturns_eq hα hl hS₀ hK, putShadowReturns_eq hα hl hS₀ hK]
  ring


end TailOptionPricing
