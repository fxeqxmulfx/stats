module

/-
  Calculus of the strong-Pareto family — Pareto Greeks.

  ## Stats.Calculus.Greeks — parametric sensitivities.

  Parametric sensitivities `∂C/∂α`, `∂C/∂l`, `∂P̂/∂α`, `∂P̂/∂l`
  for the call and shadow put under the strong-Pareto density.

  See `Stats/Calculus.lean` for the umbrella.
-/
public import Stats.Calculus.PutShadow

@[expose] public section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace TailOptionPricing

/-! ### Pareto Greeks: parametric sensitivities `∂C/∂α`, `∂C/∂l`, `∂P̂/∂α`,
    `∂P̂/∂l`.  Strike-derivatives `∂C/∂K`, `∂P̂/∂K` are `callPrice_hasDerivAt`
    and `putShadow_hasDerivAt`. -/

/-- **`∂C/∂l` (sensitivity of the call to the Karamata anchor):**
        ∂C/∂l = α · l^(α−1) · K^(1−α) / (α−1). -/
theorem callPrice_hasDerivAt_l {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hlK : l < K) :
    HasDerivAt (fun l' => callPrice l' α K)
      (α * l ^ (α - 1) * K ^ (1 - α) / (α - 1)) l := by
  have h_id : HasDerivAt (fun l' : ℝ => l') 1 l := hasDerivAt_id l
  have h_pow : HasDerivAt (fun l' : ℝ => l' ^ α) (1 * α * l ^ (α - 1)) l :=
    h_id.rpow_const (Or.inl hl.ne')
  have h_form : HasDerivAt (fun l' : ℝ => l' ^ α * K ^ (1 - α) / (α - 1))
      (1 * α * l ^ (α - 1) * K ^ (1 - α) / (α - 1)) l :=
    (h_pow.mul_const (K ^ (1 - α))).div_const (α - 1)
  have h_local : (fun l' => callPrice l' α K) =ᶠ[𝓝 l]
      (fun l' : ℝ => l' ^ α * K ^ (1 - α) / (α - 1)) := by
    filter_upwards [(isOpen_Ioo (a := 0) (b := K)).mem_nhds ⟨hl, hlK⟩] with l' hl'
    obtain ⟨hl'_pos, hl'_lt⟩ := hl'
    exact callPrice_eq hα hl'_pos hl'_lt.le
  have h := h_form.congr_of_eventuallyEq h_local
  convert h using 1; ring

/-- **`∂P̂/∂l` (sensitivity of the shadow put to the Karamata anchor):**
        ∂P̂/∂l = α · l^(α−1) · K^(1−α) / (α−1) − α/(α−1). -/
theorem putShadow_hasDerivAt_l {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hlK : l < K) :
    HasDerivAt (fun l' => putShadow l' α K)
      (α * l ^ (α - 1) * K ^ (1 - α) / (α - 1) - α / (α - 1)) l := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_call := callPrice_hasDerivAt_l hα hl hlK
  have h_id : HasDerivAt (fun l' : ℝ => l') 1 l := hasDerivAt_id l
  have h_div : HasDerivAt (fun l' : ℝ => α * l' / (α - 1)) (α / (α - 1)) l := by
    have h := (h_id.const_mul α).div_const (α - 1)
    convert h using 1; field_simp
  have h_aff : HasDerivAt (fun l' : ℝ => K - α * l' / (α - 1)) (-(α / (α - 1))) l := by
    simpa using h_div.const_sub K
  have h_sum : HasDerivAt (fun l' : ℝ => callPrice l' α K + (K - α * l' / (α - 1)))
      (α * l ^ (α - 1) * K ^ (1 - α) / (α - 1) + (-(α / (α - 1)))) l :=
    h_call.add h_aff
  have h_local : (fun l' => putShadow l' α K) =ᶠ[𝓝 l]
      (fun l' : ℝ => callPrice l' α K + (K - α * l' / (α - 1))) := by
    filter_upwards [(isOpen_Ioo (a := 0) (b := K)).mem_nhds ⟨hl, hlK⟩] with l' hl'
    obtain ⟨hl'_pos, hl'_lt⟩ := hl'
    have h := putCallParity_Pareto hα hl'_pos hl'_lt.le
    linarith
  have h := h_sum.congr_of_eventuallyEq h_local
  convert h using 1

/-- **`∂C/∂α` (sensitivity of the call to the tail index, "Pareto Vega"):**
        ∂C/∂α = l^α · K^(1−α) · ((α−1)·log(l/K) − 1) / (α−1)². -/
theorem callPrice_hasDerivAt_alpha {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    HasDerivAt (fun α' => callPrice l α' K)
      (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) / (α - 1) ^ 2)
      α := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have hK_pos : 0 < K := hl.trans_le hK
  have h_id : HasDerivAt (fun α' : ℝ => α') 1 α := hasDerivAt_id α
  have h_lpow : HasDerivAt (fun α' : ℝ => l ^ α') (Real.log l * 1 * l ^ α) α :=
    h_id.const_rpow hl
  have h_one_sub : HasDerivAt (fun α' : ℝ => 1 - α') (-1) α := by
    simpa using h_id.const_sub (1 : ℝ)
  have h_Kpow : HasDerivAt (fun α' : ℝ => K ^ (1 - α'))
      (Real.log K * (-1) * K ^ (1 - α)) α :=
    h_one_sub.const_rpow hK_pos
  have h_N : HasDerivAt (fun α' : ℝ => l ^ α' * K ^ (1 - α'))
      (Real.log l * 1 * l ^ α * K ^ (1 - α)
        + l ^ α * (Real.log K * (-1) * K ^ (1 - α))) α :=
    h_lpow.mul h_Kpow
  have h_D : HasDerivAt (fun α' : ℝ => α' - 1) 1 α := by
    simpa using h_id.sub_const 1
  have h_D_ne : (fun α' : ℝ => α' - 1) α ≠ 0 := by simpa using hα1_ne
  have h_div : HasDerivAt (fun α' : ℝ => l ^ α' * K ^ (1 - α') / (α' - 1))
      (((Real.log l * 1 * l ^ α * K ^ (1 - α)
          + l ^ α * (Real.log K * (-1) * K ^ (1 - α))) * (α - 1)
        - l ^ α * K ^ (1 - α) * 1) / (α - 1) ^ 2) α :=
    h_N.div h_D h_D_ne
  have h_local : (fun α' => callPrice l α' K) =ᶠ[𝓝 α]
      (fun α' : ℝ => l ^ α' * K ^ (1 - α') / (α' - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hα] with α' hα'
    exact callPrice_eq hα' hl hK
  have h := h_div.congr_of_eventuallyEq h_local
  convert h using 1; ring

/-- **`∂P̂/∂α` (sensitivity of the shadow put to the tail index):**
        ∂P̂/∂α = ∂C/∂α + l/(α−1)². -/
theorem putShadow_hasDerivAt_alpha {l α K : ℝ} (hα : 1 < α) (hl : 0 < l) (hK : l ≤ K) :
    HasDerivAt (fun α' => putShadow l α' K)
      (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) / (α - 1) ^ 2
        + l / (α - 1) ^ 2) α := by
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα.ne'
  have h_call := callPrice_hasDerivAt_alpha hα hl hK
  have h_id : HasDerivAt (fun α' : ℝ => α') 1 α := hasDerivAt_id α
  have h_num : HasDerivAt (fun α' : ℝ => α' * l) (1 * l) α := h_id.mul_const l
  have h_den : HasDerivAt (fun α' : ℝ => α' - 1) 1 α := by
    simpa using h_id.sub_const 1
  have h_den_ne : (fun α' : ℝ => α' - 1) α ≠ 0 := by simpa using hα1_ne
  have h_div : HasDerivAt (fun α' : ℝ => α' * l / (α' - 1))
      ((1 * l * (α - 1) - α * l * 1) / (α - 1) ^ 2) α :=
    h_num.div h_den h_den_ne
  have h_K : HasDerivAt (fun _ : ℝ => K) 0 α := hasDerivAt_const α K
  have h_sum : HasDerivAt (fun α' : ℝ => callPrice l α' K + K - α' * l / (α' - 1))
      (l ^ α * K ^ (1 - α) * ((α - 1) * (Real.log l - Real.log K) - 1) / (α - 1) ^ 2
        + 0 - (1 * l * (α - 1) - α * l * 1) / (α - 1) ^ 2) α :=
    (h_call.add h_K).sub h_div
  have h_local : (fun α' => putShadow l α' K) =ᶠ[𝓝 α]
      (fun α' : ℝ => callPrice l α' K + K - α' * l / (α' - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hα] with α' hα'
    have h := putCallParity_Pareto hα' hl hK
    linarith
  have h := h_sum.congr_of_eventuallyEq h_local
  convert h using 1; field_simp; ring


end TailOptionPricing
