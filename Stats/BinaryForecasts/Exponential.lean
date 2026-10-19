module

/-
  Statistical differences between binary forecasts and real-world payoffs.
    Taleb, arXiv:1907.11162v3 (Dec 2019).

  ## Stats.BinaryForecasts.Exponential — paper Definition 4 borderline case.

  Exponential distribution as the borderline class for the
  characteristic-scale criterion: `λ → 0` exhibits the heavy-tail
  symptoms even though all moments are finite.

  See `Stats/BinaryForecasts.lean` for the umbrella module.
-/
public import Stats.BinaryForecasts.CharacteristicScale

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped NNReal

namespace TailOptionPricing

open ProbabilityTheory

/-! ## Exponential distribution — borderline class (paper Definition 4).

    For `X ∼ Exponential(λ)` with `λ > 0`, density `f(x) = λ·e^(−λx)`
    on `[0, ∞)`:
        ℙ(X > K) = e^(−λK),
        ∫_K^∞ x · λ·e^(−λx) dx = (K + 1/λ) · e^(−λK),
        E[X | X > K] = K + 1/λ      (memoryless excess).

    Hence `lim_{K → ∞} E[X|X>K] − K = 1/λ > 0`, placing exponential in
    the borderline class of Definition 4: thin-tailed by `λ = 1` but
    with positive constant conditional excess. -/

/-- **Exponential density** `λ · e^(−λx)`. -/
noncomputable def expDensity (lam x : ℝ) : ℝ := lam * Real.exp (-(lam * x))

/-- **Exponential survival** `ℙ(X > K) = e^(−λK)` for any `K ≥ 0`. -/
theorem exp_survival_eq {lam K : ℝ} (hlam : 0 < lam) (_hK : 0 ≤ K) :
    ∫ x in Ioi K, expDensity lam x = Real.exp (-(lam * K)) := by
  -- Antiderivative of λ·e^(−λx) is −e^(−λx).
  set F : ℝ → ℝ := fun x => -Real.exp (-(lam * x)) with hF_def
  have hF_deriv : ∀ x : ℝ, HasDerivAt F (expDensity lam x) x := by
    intro x
    have h_inner : HasDerivAt (fun y : ℝ => -(lam * y)) (-lam) x := by
      have h := (hasDerivAt_id x).const_mul lam
      convert h.neg using 1
      · rfl
      · simp
    have h_exp := Real.hasDerivAt_exp (-(lam * x))
    have h_comp := h_exp.comp x h_inner
    -- h_comp : HasDerivAt (exp ∘ ...) (exp(-(lam*x)) * (-lam)) x
    have h_neg : HasDerivAt (fun y : ℝ => -Real.exp (-(lam * y)))
        (-(Real.exp (-(lam * x)) * (-lam))) x := h_comp.neg
    convert h_neg using 1
    show expDensity lam x = -(Real.exp (-(lam * x)) * -lam)
    unfold expDensity; ring
  have h_tendsto : Tendsto F atTop (𝓝 0) := by
    have h_inner_atBot : Tendsto (fun x : ℝ => -(lam * x)) atTop atBot := by
      have h_lin : Tendsto (fun x : ℝ => lam * x) atTop atTop :=
        Tendsto.const_mul_atTop hlam tendsto_id
      exact tendsto_neg_atTop_atBot.comp h_lin
    have h_exp_to_zero : Tendsto (fun x : ℝ => Real.exp (-(lam * x)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_inner_atBot
    have := h_exp_to_zero.neg
    simpa using this
  have h_nonneg : ∀ x ∈ Set.Ioi K, 0 ≤ expDensity lam x := by
    intro x _hx
    unfold expDensity
    have : 0 < Real.exp (-(lam * x)) := Real.exp_pos _
    positivity
  have h_int : IntegrableOn (expDensity lam) (Set.Ioi K) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_tendsto
    · exact (hF_deriv K).continuousAt.continuousWithinAt
    · intro x _; exact hF_deriv x
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (a := K) (m := 0) (f' := expDensity lam)
    (hF_deriv K).continuousAt.continuousWithinAt
    (fun x _ => hF_deriv x) h_int h_tendsto
  rw [hFTC]; show 0 - F K = Real.exp (-(lam * K)); rw [hF_def]; ring

/-- **Exponential tail expectation (paper context for Def. 4 borderline):**
        ∫_K^∞ x · λ·e^(−λx) dx = (K + 1/λ) · e^(−λK).
    FTC with antiderivative `F(x) = −(x + 1/λ) · e^(−λx)`. -/
theorem exp_tail_expectation_eq {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    ∫ x in Ioi K, x * expDensity lam x
      = (K + 1 / lam) * Real.exp (-(lam * K)) := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  -- Antiderivative: F(x) = −(x + 1/λ) · e^(−λx).
  set F : ℝ → ℝ := fun x => -(x + 1 / lam) * Real.exp (-(lam * x)) with hF_def
  have hF_deriv : ∀ x : ℝ, HasDerivAt F (x * expDensity lam x) x := by
    intro x
    have h_lin : HasDerivAt (fun y : ℝ => -(y + 1 / lam)) (-1) x := by
      have h_id : HasDerivAt (fun y : ℝ => y + 1 / lam) 1 x := by
        simpa using (hasDerivAt_id x).add_const (1 / lam)
      have h_neg := h_id.neg
      convert h_neg using 1
    have h_inner : HasDerivAt (fun y : ℝ => -(lam * y)) (-lam) x := by
      have h := (hasDerivAt_id x).const_mul lam
      convert h.neg using 1
      · rfl
      · simp
    have h_exp_inner : HasDerivAt (fun y : ℝ => Real.exp (-(lam * y)))
        (Real.exp (-(lam * x)) * (-lam)) x :=
      (Real.hasDerivAt_exp _).comp x h_inner
    have h_prod := h_lin.mul h_exp_inner
    -- h_prod : derivative of (-(y+1/λ)) · exp(-(λy)) is computed
    convert h_prod using 1
    show x * expDensity lam x =
        -1 * Real.exp (-(lam * x)) + -(x + 1 / lam) * (Real.exp (-(lam * x)) * -lam)
    unfold expDensity
    field_simp
    ring
  have h_tendsto : Tendsto F atTop (𝓝 0) := by
    -- F(x) = -(x + 1/λ) · e^(-λx).  Use `mul_atTop` style: polynomial × exp(-x).
    have h_inner_atBot : Tendsto (fun x : ℝ => -(lam * x)) atTop atBot := by
      have h_lin : Tendsto (fun x : ℝ => lam * x) atTop atTop :=
        Tendsto.const_mul_atTop hlam tendsto_id
      exact tendsto_neg_atTop_atBot.comp h_lin
    -- Use: x · e^{-x} → 0; thus (x + c) · e^{-λx} → 0.
    have h_aux : Tendsto (fun x : ℝ => -(x + 1 / lam) * Real.exp (-(lam * x)))
        atTop (𝓝 0) := by
      -- Rewrite: -(x + 1/λ) · e^{-λx} = -(λx · e^{-λx})/λ - (1/λ) · e^{-λx}
      have h_eq : ∀ x : ℝ, -(x + 1 / lam) * Real.exp (-(lam * x))
          = -(lam * x * Real.exp (-(lam * x))) / lam
            - (1 / lam) * Real.exp (-(lam * x)) := by
        intro x; field_simp; ring
      have h_t1 : Tendsto (fun x : ℝ => lam * x) atTop atTop :=
        Tendsto.const_mul_atTop hlam tendsto_id
      have h_t1_exp : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
        -- y · e^{-y} → 0 as y → ∞.
        have h_pol_exp := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
        have h_eq2 : (fun y : ℝ => y ^ 1 * Real.exp (-y))
                  = (fun y : ℝ => y * Real.exp (-y)) := by
          funext y; rw [pow_one]
        rwa [h_eq2] at h_pol_exp
      have h_t1_inner : Tendsto (fun x : ℝ => lam * x * Real.exp (-(lam * x))) atTop (𝓝 0) := by
        have := h_t1_exp.comp h_t1
        convert this using 1 ; rfl
      have h_t1_div : Tendsto (fun x : ℝ => lam * x * Real.exp (-(lam * x)) / lam)
          atTop (𝓝 (0 / lam)) :=
        h_t1_inner.div_const lam
      rw [zero_div] at h_t1_div
      have h_t1_neg : Tendsto (fun x : ℝ => -(lam * x * Real.exp (-(lam * x)) / lam))
          atTop (𝓝 (-0)) := h_t1_div.neg
      rw [neg_zero] at h_t1_neg
      have h_t2_exp : Tendsto (fun x : ℝ => Real.exp (-(lam * x))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp h_inner_atBot
      have h_t2 : Tendsto (fun x : ℝ => (1 / lam) * Real.exp (-(lam * x)))
          atTop (𝓝 ((1 / lam) * 0)) := tendsto_const_nhds.mul h_t2_exp
      rw [mul_zero] at h_t2
      have h_sum : Tendsto
          (fun x : ℝ => -(lam * x * Real.exp (-(lam * x)) / lam)
            - (1 / lam) * Real.exp (-(lam * x))) atTop (𝓝 (0 - 0)) :=
        h_t1_neg.sub h_t2
      rw [sub_zero] at h_sum
      refine h_sum.congr ?_
      intro x; rw [h_eq]; ring
    exact h_aux
  have h_nonneg : ∀ x ∈ Set.Ioi K, 0 ≤ x * expDensity lam x := by
    intro x hx
    have hx_pos : 0 ≤ x := le_of_lt (lt_of_le_of_lt hK hx)
    unfold expDensity
    have h_exp : 0 < Real.exp (-(lam * x)) := Real.exp_pos _
    positivity
  have h_int : IntegrableOn (fun x : ℝ => x * expDensity lam x)
      (Set.Ioi K) volume := by
    refine integrableOn_Ioi_deriv_of_nonneg ?_ ?_ h_nonneg h_tendsto
    · exact (hF_deriv K).continuousAt.continuousWithinAt
    · intro x _; exact hF_deriv x
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (a := K) (m := 0) (f' := fun x => x * expDensity lam x)
    (hF_deriv K).continuousAt.continuousWithinAt
    (fun x _ => hF_deriv x) h_int h_tendsto
  rw [hFTC]; show 0 - F K = (K + 1 / lam) * Real.exp (-(lam * K))
  rw [hF_def]; ring

/-- **Exponential conditional excess (Def. 4 borderline class):**
        E[X | X > K] − K = 1 / λ
    for any `K ≥ 0`.  Constant, independent of `K` (memoryless
    property).  Places exponential in the *borderline* class of
    Definition 4: characteristic scale `λ = 1` (`E[X|X>K]/K → 1`) but
    with positive constant excess `μ := 1/λ > 0`. -/
theorem exp_conditional_excess {lam K : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K) :
    (∫ x in Ioi K, x * expDensity lam x) / (∫ x in Ioi K, expDensity lam x) - K
      = 1 / lam := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have h_exp_pos : 0 < Real.exp (-(lam * K)) := Real.exp_pos _
  have h_exp_ne : Real.exp (-(lam * K)) ≠ 0 := h_exp_pos.ne'
  rw [exp_tail_expectation_eq hlam hK, exp_survival_eq hlam hK]
  field_simp
  ring


end TailOptionPricing
