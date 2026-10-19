module

/-
  Calculus of the strong-Pareto put shadow.

  ## Stats.Calculus.PutShadow — Breeden–Litzenberger for the shadow put.

  Contains:
    * Breeden–Litzenberger derivatives for the upside-returns shadow put.
    * Strict convexity and boundary continuity of the shadow puts.

  See `Stats/Calculus.lean` for the umbrella.
-/
public import Stats.Calculus.CallPrice

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ### Breeden–Litzenberger for the upside-returns shadow put (Result 2). -/

/-- **First derivative of `putShadowReturns`:** for `K > S₀(1+l)`,
        d P̂↑/dK = 1 − ((l·S₀)/(K−S₀))^α = ℙ(S ≤ K)
    under the upside-return Pareto density.  Mirror of `putShadow_hasDerivAt`. -/
theorem putShadowReturns_hasDerivAt {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) < K) :
    HasDerivAt (putShadowReturns l α S₀)
      (1 - ((l * S₀) / (K - S₀)) ^ α) K := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hKS₀_pos : 0 < K - S₀ := by nlinarith
  have h_base : HasDerivAt (fun K' : ℝ => K' - S₀) 1 K := by
    simpa using (hasDerivAt_id K).sub_const S₀
  have h_pow : HasDerivAt (fun K' : ℝ => (K' - S₀) ^ (1 - α))
      ((1 - α) * (K - S₀) ^ (-α)) K := by
    have := h_base.rpow_const (p := 1 - α) (Or.inl hKS₀_pos.ne')
    convert this using 1
    rw [show (1 - α - 1 : ℝ) = -α from by ring]; ring
  have h_form_g : HasDerivAt
      (fun K' : ℝ => (l * S₀) ^ α * (K' - S₀) ^ (1 - α) / (α - 1))
      ((l * S₀) ^ α * ((1 - α) * (K - S₀) ^ (-α)) / (α - 1)) K :=
    (h_pow.const_mul ((l * S₀) ^ α)).div_const (α - 1)
  have h_form : HasDerivAt
      (fun K' : ℝ =>
        (l * S₀) ^ α * (K' - S₀) ^ (1 - α) / (α - 1) + (K' - S₀)
          - α * (l * S₀) / (α - 1))
      ((l * S₀) ^ α * ((1 - α) * (K - S₀) ^ (-α)) / (α - 1) + 1) K :=
    (h_form_g.add h_base).sub_const (α * (l * S₀) / (α - 1))
  have h_local : putShadowReturns l α S₀ =ᶠ[𝓝 K]
      (fun K' : ℝ =>
        (l * S₀) ^ α * (K' - S₀) ^ (1 - α) / (α - 1) + (K' - S₀)
          - α * (l * S₀) / (α - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hK] with K' hK'
    exact putShadowReturns_eq hα hl hS₀ (le_of_lt hK')
  have h := h_form.congr_of_eventuallyEq h_local
  convert h using 1
  rw [Real.div_rpow hlS₀_pos.le hKS₀_pos.le, Real.rpow_neg hKS₀_pos.le]
  have hKS₀α_ne : (K - S₀) ^ α ≠ 0 := (Real.rpow_pos_of_pos hKS₀_pos _).ne'
  field_simp
  ring

/-- **Second derivative of `putShadowReturns`** (Breeden–Litzenberger):
        d² P̂↑/dK² = α · (l·S₀)^α / (K − S₀)^(α+1),
    the upside-return Pareto density.  Mirror of
    `putShadow_hasDerivAt_secondOrder`. -/
theorem putShadowReturns_hasDerivAt_secondOrder {l α S₀ K : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) (hK : S₀ * (1 + l) < K) :
    HasDerivAt (fun K' => 1 - ((l * S₀) / (K' - S₀)) ^ α)
      (α * (l * S₀) ^ α / (K - S₀) ^ (α + 1)) K := by
  have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
  have hKS₀_pos : 0 < K - S₀ := by nlinarith
  have h_base : HasDerivAt (fun K' : ℝ => K' - S₀) 1 K := by
    simpa using (hasDerivAt_id K).sub_const S₀
  have h_pow : HasDerivAt (fun K' : ℝ => (K' - S₀) ^ (-α))
      ((-α) * (K - S₀) ^ (-α - 1)) K := by
    have := h_base.rpow_const (p := -α) (Or.inl hKS₀_pos.ne')
    convert this using 1; ring
  have h_step : HasDerivAt
      (fun K' : ℝ => 1 + -((l * S₀) ^ α * (K' - S₀) ^ (-α)))
      (-((l * S₀) ^ α * ((-α) * (K - S₀) ^ (-α - 1)))) K :=
    ((h_pow.const_mul ((l * S₀) ^ α)).neg).const_add 1
  have h_eqfun : (fun K' : ℝ => 1 + -((l * S₀) ^ α * (K' - S₀) ^ (-α)))
               = (fun K' : ℝ => 1 - (l * S₀) ^ α * (K' - S₀) ^ (-α)) := by
    funext K'; ring
  rw [h_eqfun] at h_step
  have h_local : (fun K' : ℝ => 1 - ((l * S₀) / (K' - S₀)) ^ α) =ᶠ[𝓝 K]
      (fun K' : ℝ => 1 - (l * S₀) ^ α * (K' - S₀) ^ (-α)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hK] with K' hK'
    have hK'_lt : S₀ * (1 + l) < K' := hK'
    have hK'_S₀_pos : 0 < K' - S₀ := by nlinarith [mul_pos hS₀ hl]
    rw [Real.div_rpow hlS₀_pos.le hK'_S₀_pos.le, Real.rpow_neg hK'_S₀_pos.le]
    field_simp
  have hh := h_step.congr_of_eventuallyEq h_local
  convert hh using 1
  rw [show (-α - 1 : ℝ) = -(α + 1) from by ring, Real.rpow_neg hKS₀_pos.le]
  have hKS₀α1_ne : (K - S₀) ^ (α + 1) ≠ 0 := (Real.rpow_pos_of_pos hKS₀_pos _).ne'
  field_simp

/-! ### Strict convexity and boundary continuity of the shadow puts. -/

/-- **Strict convexity of the shadow put** on `Ioi l`.  Mirror of
    `putPriceBS_strictConvexOn`: from put–call parity
    `P̂(K) = C(K) + (K − α·l/(α−1))` on `Ici l`, so adding an affine
    function preserves the strict convexity established in
    `callPrice_strictConvexOn`. -/
theorem putShadow_strictConvexOn {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    StrictConvexOn ℝ (Ioi l) (putShadow l α) := by
  have h_eq : Set.EqOn (putShadow l α)
      (fun K : ℝ => callPrice l α K + (K - α * l / (α - 1))) (Ioi l) := by
    intro K hK
    have h := putCallParity_Pareto hα hl (le_of_lt hK)
    linarith
  have h_aff : ConvexOn ℝ (Ioi l) (fun K : ℝ => K - α * l / (α - 1)) := by
    have h_id : ConvexOn ℝ (Ioi l) (id : ℝ → ℝ) := convexOn_id (convex_Ioi l)
    have h := h_id.add_const (-(α * l / (α - 1)))
    have h_eq : (id + fun _ : ℝ => -(α * l / (α - 1)))
              = (fun K : ℝ => K - α * l / (α - 1)) := by
      funext K; simp [Pi.add_apply, sub_eq_add_neg]
    rwa [h_eq] at h
  have h_combined : StrictConvexOn ℝ (Ioi l)
      (fun K : ℝ => callPrice l α K + (K - α * l / (α - 1))) :=
    (callPrice_strictConvexOn hα hl).add_convexOn h_aff
  exact h_combined.congr h_eq.symm

/-- **Strict convexity of the upside-returns shadow put** on `Ioi (S₀·(1+l))`.
    Direct analogue of `callPrice_strictConvexOn`: the BL second derivative
    is the strictly positive returns Pareto density. -/
theorem putShadowReturns_strictConvexOn {l α S₀ : ℝ}
    (hα : 1 < α) (hl : 0 < l) (hS₀ : 0 < S₀) :
    StrictConvexOn ℝ (Ioi (S₀ * (1 + l))) (putShadowReturns l α S₀) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi _)
  · intro K hK
    exact (putShadowReturns_hasDerivAt hα hl hS₀ hK).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro K hK
    have hK_lt : S₀ * (1 + l) < K := hK
    have hKS₀_pos : 0 < K - S₀ := by nlinarith [mul_pos hS₀ hl]
    have hlS₀_pos : 0 < l * S₀ := mul_pos hl hS₀
    have h_eqLocal : deriv (putShadowReturns l α S₀) =ᶠ[𝓝 K]
        (fun y : ℝ => 1 - ((l * S₀) / (y - S₀)) ^ α) := by
      filter_upwards [isOpen_Ioi.mem_nhds hK] with y hy
      exact (putShadowReturns_hasDerivAt hα hl hS₀ hy).deriv
    have h2 : HasDerivAt (deriv (putShadowReturns l α S₀))
        (α * (l * S₀) ^ α / (K - S₀) ^ (α + 1)) K :=
      (putShadowReturns_hasDerivAt_secondOrder hα hl hS₀ hK).congr_of_eventuallyEq h_eqLocal
    rw [show (deriv^[2] (putShadowReturns l α S₀)) K
          = deriv (deriv (putShadowReturns l α S₀)) K from rfl, h2.deriv]
    have hα_pos : 0 < α := by linarith
    have hlS₀α_pos : 0 < (l * S₀) ^ α := Real.rpow_pos_of_pos hlS₀_pos _
    have hKS₀α1_pos : 0 < (K - S₀) ^ (α + 1) := Real.rpow_pos_of_pos hKS₀_pos _
    positivity

/-- **Boundary continuity of the shadow put on the closed half-line.**
    Mirror of `callPrice_continuousOn_Ici`: since `putShadow` admits the closed
    form `l^α · K^(1−α)/(α−1) + K − α·l/(α−1)` on `Ici l`, and that closed form
    is continuous on `Ici l ⊆ Ioi 0`, the shadow put extends continuously up to
    and including the Karamata anchor `l`. -/
theorem putShadow_continuousOn_Ici {l α : ℝ} (hα : 1 < α) (hl : 0 < l) :
    ContinuousOn (putShadow l α) (Set.Ici l) := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_pow_cont :
      ContinuousOn (fun K : ℝ => l ^ α * K ^ (1 - α) / (α - 1)) (Set.Ici l) := by
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const continuousOn_id (fun K hK => Or.inl ?_)
    exact (hl.trans_le hK).ne'
  have h_closed_form_cont :
      ContinuousOn (fun K => l ^ α * K ^ (1 - α) / (α - 1) + K - α * l / (α - 1))
        (Set.Ici l) :=
    (h_pow_cont.add continuousOn_id).sub continuousOn_const
  refine h_closed_form_cont.congr (fun K hK => ?_)
  exact putShadow_eq hα hl hK


end TailOptionPricing
