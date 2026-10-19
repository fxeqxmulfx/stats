module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalTailIntegrals — `An σ → 1` and `Bn σ → 0` for the lognormal.

  Phases 6.2 and 6.3 of [todo6.md](todo6.md).  Two σ-tendsto facts about
  the lognormal `Y σ ω := exp(σ·ω − σ²/2)` on `(ℝ, gaussianReal 0 1)`:

  * **An**: `∫_{t > 0} ℙ_σ(Y > n + t) dt → 1` as `σ → ∞` (any `n : ℕ`,
    `n ≥ 1`).
    Proof: layer cake gives `∫_{t > 0} ℙ_σ(Y > n + t) dt = 𝔼[(Y σ − n)⁺]
    = 𝔼Y σ − 𝔼[min(Y σ, n)] = 1 − 𝔼[min(Y σ, n)]`.  By DCT (bound `n`,
    pointwise → 0), the second term → 0.

  * **Bn**: `∫_{t > 0} ℙ_σ(Y > n + t)² dt → 0` as `σ → ∞`.
    Proof: Hölder bound (`LognormalMarkov.lognormalReal_real_Ioi_le`)
    gives `ℙ_σ(Y > n + t)² ≤ (n + t)^(−2γ) · exp(γ(γ − 1)·σ²)` for
    `γ ∈ (1/2, 1)`.  Integrate `t^(−2γ)` (convergent for `γ > 1/2`);
    the exp factor → 0 as σ → ∞ (since `γ(γ − 1) < 0`).
-/
public import Stats.Kappa.LognormalAsymptotic
public import Stats.Kappa.LognormalMarkov
public import Stats.Kappa.MadLayerCake

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

namespace TailOptionPricing.LognormalTailIntegrals

open TailOptionPricing.LognormalAsymptotic
  (Y Y_pos Y_nonneg integral_Y_eq_one tendsto_Y_atTop_zero)

/-! ### Generalised B.7: `𝔼[min(Y σ, k)] → 0` for any `k > 0`. -/

/-- **DCT generalisation**: `∫ min(Y σ ω, k) ∂(gauss 0 1) → 0` as `σ → ∞`,
    for any `k > 0`. -/
theorem integral_min_Y_const_tendsto_zero {k : ℝ} (hk : 0 < k) :
    Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) k ∂(gaussianReal 0 1))
      atTop (𝓝 0) := by
  have h_bound_int : Integrable (fun _ : ℝ => k) (gaussianReal 0 1) :=
    integrable_const _
  have h_lim_zero :
      Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) k ∂(gaussianReal 0 1))
        atTop (𝓝 (∫ ω, (0 : ℝ) ∂(gaussianReal 0 1))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => k)
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      have h_meas_Y : Measurable (fun ω => Y σ ω) := by unfold Y; fun_prop
      exact (h_meas_Y.min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      refine .of_forall (fun ω => ?_)
      have h_nn : 0 ≤ min (Y σ ω) k := le_min (Y_nonneg σ ω) hk.le
      have h_le : min (Y σ ω) k ≤ k := min_le_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact h_le
    · exact h_bound_int
    · refine .of_forall (fun ω => ?_)
      have h_min : Tendsto (fun σ : ℝ => min (Y σ ω) k) atTop (𝓝 (min 0 k)) :=
        (tendsto_Y_atTop_zero ω).min tendsto_const_nhds
      simpa [min_eq_left hk.le] using h_min
  rw [integral_zero] at h_lim_zero
  exact h_lim_zero

/-! ### An σ → 1. -/

/-- **Pointwise identity** `(Y σ ω − n)⁺ = Y σ ω − min(Y σ ω, n)` for `n ≥ 0`. -/
private lemma pos_part_sub_const_eq (σ n ω : ℝ) (_hn : 0 ≤ n) :
    max (Y σ ω - n) 0 = Y σ ω - min (Y σ ω) n := by
  by_cases h : Y σ ω ≤ n
  · have h1 : Y σ ω - n ≤ 0 := by linarith
    rw [max_eq_right h1, min_eq_left h]; ring
  · push Not at h
    have h1 : 0 < Y σ ω - n := by linarith
    rw [max_eq_left h1.le, min_eq_right h.le]

/-- **`𝔼[(Y σ − n)⁺] → 1`** as `σ → ∞`. -/
theorem integral_pos_part_Y_sub_n_tendsto_one {n : ℝ} (hn : 0 < n) :
    Tendsto (fun σ : ℝ => ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1))
      atTop (𝓝 1) := by
  -- Rewrite via the identity `(Y − n)⁺ = Y − min(Y, n)`.
  have h_pt : ∀ σ ω, max (Y σ ω - n) 0 = Y σ ω - min (Y σ ω) n :=
    fun σ ω => pos_part_sub_const_eq σ n ω hn.le
  have h_fun_eq : ∀ σ, (fun ω => max (Y σ ω - n) 0)
      = fun ω => Y σ ω - min (Y σ ω) n := fun σ => funext (h_pt σ)
  -- Integrate: ∫(Y − min(Y, n)) = ∫Y − ∫min(Y, n) = 1 − ∫min(Y, n).
  have h_eq : ∀ σ, ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1)
      = 1 - ∫ ω, min (Y σ ω) n ∂(gaussianReal 0 1) := by
    intro σ
    rw [h_fun_eq]
    -- Need integrability of `Y σ` and `min (Y σ, n)`.
    have hY_int : Integrable (Y σ) (gaussianReal 0 1) := by
      unfold Y
      have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
          = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
        funext ω; rw [← Real.exp_add]; congr 1; ring
      rw [h_factor]
      exact (integrable_exp_mul_gaussianReal σ).const_mul _
    have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
    have h_min_int : Integrable (fun ω => min (Y σ ω) n) (gaussianReal 0 1) := by
      refine Integrable.mono' (g := fun _ => n) (integrable_const _)
        (h_meas_Y.min measurable_const).aestronglyMeasurable ?_
      refine .of_forall (fun ω => ?_)
      have h_nn : 0 ≤ min (Y σ ω) n := le_min (Y_nonneg σ ω) hn.le
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact min_le_right _ _
    rw [integral_sub hY_int h_min_int, integral_Y_eq_one σ]
  rw [show (fun σ => ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1))
      = fun σ => 1 - ∫ ω, min (Y σ ω) n ∂(gaussianReal 0 1) from funext h_eq]
  -- 1 − ∫min(Y, n) → 1 − 0 = 1.
  have h_target : Tendsto (fun σ : ℝ =>
        (1 : ℝ) - ∫ ω, min (Y σ ω) n ∂(gaussianReal 0 1))
      atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (integral_min_Y_const_tendsto_zero hn)
  simpa using h_target

/-! ### Layer-cake bridge: `An σ = 𝔼[(Y σ − n)⁺]`. -/

/-- **An σ in tail-integral form** via the public layer cake
    [`MadLayerCake.integral_pos_part_eq_tail_integral`](Stats/Kappa/MadLayerCake.lean).
    For each σ and any real `n`,
        `𝔼[(Y σ − n)⁺] = ∫_{t > 0} ℙ_σ(Y > n + t) dt`. -/
theorem integral_pos_part_eq_An (σ n : ℝ) :
    ∫ ω, max (Y σ ω - n) 0 ∂(gaussianReal 0 1)
      = ∫ t in Set.Ioi (0 : ℝ),
          (gaussianReal 0 1).real {ω | Y σ ω > n + t} := by
  have hY_int : Integrable (Y σ) (gaussianReal 0 1) := by
    unfold Y
    have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
        = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
      funext ω; rw [← Real.exp_add]; congr 1; ring
    rw [h_factor]
    exact (integrable_exp_mul_gaussianReal σ).const_mul _
  exact TailOptionPricing.MadLayerCake.integral_pos_part_eq_tail_integral hY_int n

/-- **`An σ → 1`** as σ → ∞ for any `n ≥ 1`.

    Direct corollary: `An σ := ∫_{t > 0} ℙ_σ(Y > n + t) dt = 𝔼[(Y σ − n)⁺] → 1`. -/
theorem An_tendsto_one {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        (gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}) atTop (𝓝 1) := by
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- An σ = 𝔼[(Y σ − n)⁺]; the latter → 1.
  refine (integral_pos_part_Y_sub_n_tendsto_one hn_real_pos).congr' ?_
  refine .of_forall fun σ => ?_
  exact integral_pos_part_eq_An σ (n : ℝ)

/-! ### Bn σ → 0 via Hölder bound. -/

/-- **Hölder/Markov bound for `Y σ` on `(ℝ, gaussianReal 0 1)`.**

    For `σ > 0`, `t > 0`, `γ' ∈ ℝ` with `γ' ≥ 0`,
        `(gaussianReal 0 1).real {ω | Y σ ω > t} ≤ t^(−γ') · exp(γ'(γ' − 1)·σ²/2)`.

    Proof: rewrite the preimage `{Y σ > t} = Ioi((log t)/σ + σ/2)`
    (using `σ > 0`); apply `LognormalMarkov.gaussianReal_real_Ici_le`
    with Chernoff parameter `γ := γ' · σ`; the σ-scaling produces the
    `t^(−γ')` factor and the `γ'(γ' − 1)·σ²/2` exponent. -/
theorem Y_tail_holder {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t)
    {γ' : ℝ} (hγ' : 0 ≤ γ') :
    (gaussianReal 0 1).real {ω | Y σ ω > t}
      ≤ t ^ (-γ') * Real.exp (γ' * (γ' - 1) * σ^2 / 2) := by
  -- {Y σ > t} ⊆ Ici (log t / σ + σ/2).
  have h_set_sub : {ω | Y σ ω > t} ⊆ Set.Ici ((Real.log t) / σ + σ / 2) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have h_Y_pos : 0 < Y σ ω := Y_pos σ ω
    -- Y σ ω > t > 0; take log on both sides.
    have h_log_lt : Real.log t < Real.log (Y σ ω) := Real.log_lt_log ht hω
    -- log(Y σ ω) = σ·ω - σ²/2.
    have h_log_Y : Real.log (Y σ ω) = σ * ω - σ^2 / 2 := by
      unfold Y; rw [Real.log_exp]
    rw [h_log_Y] at h_log_lt
    -- σ·ω - σ²/2 > log t ⟹ σ·ω > log t + σ²/2 ⟹ ω > (log t + σ²/2)/σ
    --                                            = log t/σ + σ/2.
    have h_div : Real.log t + σ^2 / 2 < σ * ω := by linarith
    have h_step : (Real.log t + σ^2 / 2) / σ < ω := by
      rw [div_lt_iff₀ hσ]; linarith
    have h_split : (Real.log t + σ^2 / 2) / σ = Real.log t / σ + σ / 2 := by
      field_simp
    rw [h_split] at h_step
    exact h_step.le
  -- (gauss 0 1).real {Y σ > t} ≤ (gauss 0 1).real (Ici ...).
  have h_meas_set : MeasurableSet {ω | Y σ ω > t} := by
    have : Measurable (Y σ) := by unfold Y; fun_prop
    exact this measurableSet_Ioi
  have h_mono : (gaussianReal 0 1).real {ω | Y σ ω > t}
      ≤ (gaussianReal 0 1).real (Set.Ici (Real.log t / σ + σ / 2)) :=
    measureReal_mono h_set_sub (measure_ne_top _ _)
  -- Apply Chernoff with γ := γ' · σ.
  have h_chern := TailOptionPricing.LognormalMarkov.gaussianReal_real_Ici_le
    (μ := 0) (v := 1) (Real.log t / σ + σ / 2)
    (γ := γ' * σ) (mul_nonneg hγ' hσ.le)
  -- Simplify the Chernoff bound.
  -- exp(-γ'σ · (log t/σ + σ/2) + γ'σ·0 + 1·(γ'σ)²/2)
  --   = exp(-γ' log t - γ'σ²/2 + γ'²σ²/2)
  --   = t^(-γ') · exp(γ'(γ'-1) σ²/2).
  have h_exponent_eq :
      -(γ' * σ) * (Real.log t / σ + σ / 2) + γ' * σ * 0 +
        ((1 : ℝ≥0) : ℝ) * (γ' * σ)^2 / 2
      = -γ' * Real.log t + γ' * (γ' - 1) * σ^2 / 2 := by
    have : (((1 : ℝ≥0) : ℝ)) = (1 : ℝ) := by norm_num
    rw [this]
    field_simp
    ring
  rw [h_exponent_eq] at h_chern
  -- exp(a + b) = exp a · exp b.  And exp(-γ' log t) = t^(-γ') (since t > 0).
  have h_exp_split :
      Real.exp (-γ' * Real.log t + γ' * (γ' - 1) * σ^2 / 2)
        = t ^ (-γ') * Real.exp (γ' * (γ' - 1) * σ^2 / 2) := by
    rw [Real.exp_add]
    congr 1
    -- t^(-γ') = exp(-γ' · log t).
    rw [Real.rpow_def_of_pos ht]
    congr 1; ring
  rw [h_exp_split] at h_chern
  -- Glue: real of set ≤ real of Ici ≤ bound.
  have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
  calc (gaussianReal 0 1).real {ω | Y σ ω > t}
      ≤ (gaussianReal 0 1).real (Set.Ici (Real.log t / σ + σ / 2)) := h_mono
    _ ≤ t ^ (-γ') * Real.exp (γ' * (γ' - 1) * σ^2 / 2) := h_chern

/-! ### Bn σ → 0 via monotonicity. -/

/-- **`ℙ_σ(Y > c) → 0`** as σ → ∞ for any fixed `c > 0`.

    By DCT on `min(Y σ ω, 1) · (some indicator)`: pointwise convergence
    to 0 (via `tendsto_Y_atTop_zero`), bounded by the integrable
    `min(Y σ, 1)`.  Equivalently: `min(Y σ, c) / c · 𝟙_{Y σ > c} ≤ 1`
    and gives `ℙ(Y > c) ≤ 𝔼[min(Y σ, c) / c]`.  Cleaner proof:
    `c · ℙ(Y > c) ≤ 𝔼[min(Y σ, c)] → 0`. -/
theorem prob_Y_gt_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ => (gaussianReal 0 1).real {ω | Y σ ω > c})
      atTop (𝓝 0) := by
  -- Markov: c · ℙ(Y > c) ≤ 𝔼[min(Y σ, c)].
  -- Reason: for ω with Y σ ω > c, min(Y σ ω, c) = c; otherwise min ≤ c.
  -- So `c · 𝟙_{Y > c} ≤ min(Y σ, c)` pointwise.  Integrate.
  -- Then `𝔼[min(Y σ, c)] → 0` (from `integral_min_Y_const_tendsto_zero hc`).
  -- Squeeze: c · ℙ(Y > c) → 0, hence ℙ(Y > c) → 0.
  have h_bound : ∀ σ : ℝ,
      c * (gaussianReal 0 1).real {ω | Y σ ω > c}
        ≤ ∫ ω, min (Y σ ω) c ∂(gaussianReal 0 1) := by
    intro σ
    have h_meas_set : MeasurableSet {ω | Y σ ω > c} := by
      have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
      exact h_meas_Y measurableSet_Ioi
    have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
    have h_min_int : Integrable (fun ω => min (Y σ ω) c) (gaussianReal 0 1) := by
      refine Integrable.mono' (g := fun _ => c) (integrable_const _)
        (h_meas_Y.min measurable_const).aestronglyMeasurable ?_
      refine .of_forall (fun ω => ?_)
      have h_nn : 0 ≤ min (Y σ ω) c := le_min (Y_nonneg σ ω) hc.le
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact min_le_right _ _
    -- Pointwise: c · 𝟙_{Y > c} ≤ min(Y σ, c).
    -- Integrate via `setIntegral_indicator` / `integral_indicator`.
    have h_pt : ∀ ω, c * Set.indicator {ω | Y σ ω > c} (fun _ => (1 : ℝ)) ω
        ≤ min (Y σ ω) c := by
      intro ω
      by_cases hω : ω ∈ {ω | Y σ ω > c}
      · rw [Set.indicator_of_mem hω, mul_one]
        simp only [Set.mem_ofPred_eq] at hω
        rw [min_eq_right hω.le]
      · rw [Set.indicator_of_notMem hω, mul_zero]
        exact le_min (Y_nonneg σ ω) hc.le
    have h_ind_int : Integrable
        ({ω | Y σ ω > c}.indicator (fun _ => (1 : ℝ))) (gaussianReal 0 1) :=
      (integrable_const (1 : ℝ)).indicator h_meas_set
    have h_int_pt :
        ∫ ω, c * Set.indicator {ω | Y σ ω > c} (fun _ => (1 : ℝ)) ω ∂(gaussianReal 0 1)
          ≤ ∫ ω, min (Y σ ω) c ∂(gaussianReal 0 1) := by
      apply integral_mono_ae
      · exact h_ind_int.const_mul c
      · exact h_min_int
      · exact .of_forall h_pt
    -- LHS = c · ∫ indicator = c · μ(set) = c · ℙ.
    have h_lhs_eq :
        ∫ ω, c * Set.indicator {ω | Y σ ω > c} (fun _ => (1 : ℝ)) ω ∂(gaussianReal 0 1)
          = c * (gaussianReal 0 1).real {ω | Y σ ω > c} := by
      rw [integral_const_mul]
      congr 1
      exact integral_indicator_one h_meas_set
    rw [h_lhs_eq] at h_int_pt
    exact h_int_pt
  -- Squeeze: 0 ≤ c · ℙ(Y > c) ≤ 𝔼[min(Y, c)] → 0.  Divide by c.
  have h_min_tend := integral_min_Y_const_tendsto_zero hc
  have h_prod_tend :
      Tendsto (fun σ => c * (gaussianReal 0 1).real {ω | Y σ ω > c})
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_min_tend
    · intro σ; positivity
    · exact h_bound
  -- Divide by c.
  have hc_ne : c ≠ 0 := hc.ne'
  have h_final : Tendsto (fun σ => (gaussianReal 0 1).real {ω | Y σ ω > c})
      atTop (𝓝 (0 / c)) := h_prod_tend.div_const c |>.congr' (by
    refine Filter.Eventually.of_forall (fun σ => ?_)
    field_simp)
  simpa using h_final

/-! ### Bn σ → 0 — full proof.

`Bn σ ≤ ℙ_σ(Y > n) · An σ` (pointwise `p(t)² ≤ ℙ_σ(Y > n) · p(t)` for
`t > 0`, since `{Y > n+t} ⊆ {Y > n}`).  Squeeze: `ℙ_σ(Y > n) → 0` and
`An σ → 1` give `Bn σ → 0`.

The integrability of `t ↦ ν.real {Y σ > n + t}` on `Ioi 0` comes from
the layer-cake form `∫_{Ioi 0} = 𝔼(Y σ − n)⁺ < ∞`, packaged in
[`MadLayerCake.integrableOn_measureReal_lt_Ioi`](Stats/Kappa/MadLayerCake.lean). -/

/-! ### An integrability piece. -/

/-- **`Y σ` is integrable** under `gaussianReal 0 1`. -/
private lemma Y_integrable (σ : ℝ) : Integrable (Y σ) (gaussianReal 0 1) := by
  unfold Y
  have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
      = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
    funext ω; rw [← Real.exp_add]; congr 1; ring
  rw [h_factor]
  exact (integrable_exp_mul_gaussianReal σ).const_mul _

/-- **Tail-integrability of `t ↦ ℙ_σ(Y > n + t)` on `Ioi 0`**.

    Apply [`MadLayerCake.integrableOn_measureReal_lt_Ioi`](Stats/Kappa/MadLayerCake.lean)
    to the centred non-negative function `(Y σ − n)`. -/
theorem integrableOn_prob_Y_gt_Ioi (σ : ℝ) (n : ℝ) :
    IntegrableOn (fun t : ℝ => (gaussianReal 0 1).real {ω | Y σ ω > n + t})
      (Set.Ioi (0 : ℝ)) := by
  -- Apply the helper to the shifted RV `Y σ - n`, but we need to recognise
  -- `{Y σ > n + t} = {Y σ - n > t}`.
  set X : ℝ → ℝ := fun ω => Y σ ω - n with hX_def
  have hX_int : Integrable X (gaussianReal 0 1) :=
    (Y_integrable σ).sub (integrable_const _)
  -- `X` may be negative for some ω, but the tail-integrability helper
  -- only needs `X` to be integrable (it doesn't actually require non-negativity,
  -- since we're only looking at `{X > t}` for `t > 0` where it's automatically
  -- the positive part).  We apply the helper to `X⁺ := max X 0` which IS nonneg.
  set Xp : ℝ → ℝ := fun ω => max (Y σ ω - n) 0 with hXp_def
  have hXp_int : Integrable Xp (gaussianReal 0 1) := hX_int.pos_part
  have hXp_nn : 0 ≤ᵐ[gaussianReal 0 1] Xp :=
    .of_forall (fun _ => le_max_right _ _)
  have h_helper := TailOptionPricing.MadLayerCake.integrableOn_measureReal_lt_Ioi
    hXp_int hXp_nn
  -- Now bridge {Xp > t} = {Y > n + t} for t > 0.
  refine h_helper.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht_pos : (0 : ℝ) < t := ht
  have h_pt : (gaussianReal 0 1).real {ω | Xp ω > t}
      = (gaussianReal 0 1).real {ω | Y σ ω > n + t} := by
    congr 1
    ext ω
    show Xp ω > t ↔ Y σ ω > n + t
    simp only [hXp_def]
    by_cases h' : 0 ≤ Y σ ω - n
    · rw [max_eq_left h']
      constructor
      · intro h; linarith
      · intro h; linarith
    · push Not at h'
      rw [max_eq_right h'.le]
      constructor
      · intro h; linarith
      · intro h; linarith
  exact h_pt

/-- **Tail-integrability of `t ↦ ℙ_σ(Y > n + t)²` on `Ioi 0`**.  Bounded
    by the linear version (probability ≤ 1). -/
theorem integrableOn_prob_Y_gt_sq_Ioi (σ : ℝ) (n : ℝ) :
    IntegrableOn (fun t : ℝ => ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have h_lin := integrableOn_prob_Y_gt_Ioi σ n
  refine h_lin.mono' ?_ ?_
  · -- Square is AEStronglyMeasurable: linear is, square of stronglyMeasurable too.
    exact h_lin.aestronglyMeasurable.pow 2
  · refine .of_forall (fun t => ?_)
    have h_nn : 0 ≤ (gaussianReal 0 1).real {ω | Y σ ω > n + t} :=
      ENNReal.toReal_nonneg
    have h_le_one : (gaussianReal 0 1).real {ω | Y σ ω > n + t} ≤ 1 := by
      rw [measureReal_def]
      have h1 : (gaussianReal 0 1) {ω | Y σ ω > n + t} ≤ 1 := prob_le_one
      have h2 := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (by simp : (1 : ENNReal) ≠ ⊤)).mpr h1
      simpa using h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_of_le_one_right h_nn h_le_one

/-! ### Pointwise bound: `p(t)² ≤ ℙ_σ(Y > n) · p(t)` for `t > 0`. -/

/-- **Monotonicity of the tail**: `ℙ_σ(Y > n + t) ≤ ℙ_σ(Y > n)` for `t > 0`. -/
private lemma prob_Y_gt_mono (σ : ℝ) (n : ℝ) {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {ω | Y σ ω > n + t}
      ≤ (gaussianReal 0 1).real {ω | Y σ ω > n} := by
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω h
  simp only [Set.mem_ofPred_eq] at h ⊢
  linarith

/-- **Bn σ ≤ ℙ_σ(Y > n) · An σ**, the squeeze bound. -/
theorem Bn_le_prob_mul_An (σ : ℝ) (n : ℝ) :
    ∫ t in Set.Ioi (0:ℝ), ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2
      ≤ (gaussianReal 0 1).real {ω | Y σ ω > n}
        * ∫ t in Set.Ioi (0:ℝ), (gaussianReal 0 1).real {ω | Y σ ω > n + t} := by
  have h_sq_int := integrableOn_prob_Y_gt_sq_Ioi σ n
  have h_lin_int := integrableOn_prob_Y_gt_Ioi σ n
  have h_mul_int := h_lin_int.const_mul ((gaussianReal 0 1).real {ω | Y σ ω > n})
  have h_pointwise : ∀ t ∈ Set.Ioi (0:ℝ),
      ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2
        ≤ (gaussianReal 0 1).real {ω | Y σ ω > n}
          * (gaussianReal 0 1).real {ω | Y σ ω > n + t} := by
    intro t ht
    have h_mono := prob_Y_gt_mono σ n ht
    have h_nn : 0 ≤ (gaussianReal 0 1).real {ω | Y σ ω > n + t} :=
      ENNReal.toReal_nonneg
    have h_sq : ((gaussianReal 0 1).real {ω | Y σ ω > n + t}) ^ 2
        ≤ (gaussianReal 0 1).real {ω | Y σ ω > n}
          * (gaussianReal 0 1).real {ω | Y σ ω > n + t} := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right h_mono h_nn
    exact h_sq
  have h_int := MeasureTheory.setIntegral_mono_on h_sq_int h_mul_int
    measurableSet_Ioi h_pointwise
  rw [integral_const_mul] at h_int
  exact h_int

/-- **`Bn σ → 0`** for any `n ≥ 1`.  The squeeze
    `0 ≤ Bn σ ≤ ℙ_σ(Y > n) · An σ` plus `ℙ_σ(Y > n) → 0`,
    `An σ → 1` (both proved above). -/
theorem Bn_tendsto_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun σ : ℝ => ∫ t in Set.Ioi (0:ℝ),
        ((gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t}) ^ 2) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- 0 ≤ Bn σ ≤ ℙ_σ(Y > n) · An σ → 0 · 1 = 0.
  have h_upper : Tendsto (fun σ : ℝ =>
      (gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ)} *
        ∫ t in Set.Ioi (0:ℝ),
          (gaussianReal 0 1).real {ω | Y σ ω > (n : ℝ) + t})
      atTop (𝓝 0) := by
    have h_mul := (prob_Y_gt_tendsto_zero hn_pos).mul (An_tendsto_one hn)
    simpa using h_mul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
  · intro σ
    apply MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  · intro σ
    exact Bn_le_prob_mul_An σ (n : ℝ)

end TailOptionPricing.LognormalTailIntegrals
