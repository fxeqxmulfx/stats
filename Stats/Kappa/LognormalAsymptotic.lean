module

/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LognormalAsymptotic — `σ → ∞` analysis of the lognormal.

  The Loulakis subexponentiality argument's final ingredient: as
  `σ → ∞`, the lognormal `Y_σ` with parameters `μ = -σ²/2`, `v = σ²`
  (so `𝔼Y_σ = 1` for all σ) satisfies:

  * **Pointwise collapse**: `Y_σ(ω) → 0` for every `ω : ℝ` (standard
    Gaussian sample space).  Mass concentrates near 0 as σ grows;
    the mean stays at 1 only via a thin, heavy right tail.
  * **`M(1; σ) → 2`**: the lognormal's MAD → 2 (since the right
    tail "absorbs" the entire mean as σ → ∞).

  Proof: parametrise `Y σ ω := exp(σ·ω − σ²/2)` on `(ℝ, gaussianReal 0 1)`.

  1.  `σ·ω − σ²/2 → -∞` as `σ → ∞` for every ω (since `σ²/2` dominates
      `σ·ω`).  Compose with `Real.tendsto_exp_atBot` to get
      `Y σ ω → 0` pointwise.

  2.  Dominated convergence with `|Y σ · 𝟙_{Y σ ≤ 1}| ≤ 1` (constant
      bound, integrable on the probability space):
      `𝔼[Y σ · 𝟙_{Y σ ≤ 1}] → 0`.

  3.  Mean condition `𝔼Y σ = 1` (from `mgf_id_gaussianReal`):
      `𝔼[Y σ · 𝟙_{Y σ > 1}] = 1 − 𝔼[Y σ · 𝟙_{Y σ ≤ 1}] → 1`.

  4.  `𝔼[(Y σ − 1)⁺] = 𝔼[Y σ · 𝟙_{Y σ > 1}] − ℙ(Y σ > 1)`.
      Since `ℙ(Y σ > 1) → 0` (by DCT on `𝟙_{Y > 1} ≤ 1`), the
      right-hand side `→ 1 − 0 = 1`.

  5.  `M(1; σ) = 𝔼|Y σ − 1| = 2·𝔼[(Y σ − 1)⁺] → 2` (via the centred-MAD
      identity `𝔼[(X−m)⁺] = 𝔼[(m−X)⁺]` when `𝔼X = m`).

  Provides the σ-asymptotic input to the Loulakis main argument
  ([LoulakisAlgebraic](Stats/Kappa/LoulakisAlgebraic.lean)).
-/
public import Stats.Kappa.LognormalMeasure
public import Stats.Kappa.MadLayerCake
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

namespace TailOptionPricing.LognormalAsymptotic

/-! ### The σ-parametrised lognormal sample function on `(ℝ, gaussianReal 0 1)`. -/

/-- **`Y σ ω := exp(σ·ω − σ²/2)`**.  Under `Z ~ gaussianReal 0 1`,
    `Y σ Z ~ lognormalReal (-σ²/2) σ²`, which has `𝔼[Y σ Z] = 1` for
    every σ (paper's "mean-1 lognormal" parametrisation). -/
noncomputable def Y (σ ω : ℝ) : ℝ := Real.exp (σ * ω - σ^2 / 2)

theorem Y_pos (σ ω : ℝ) : 0 < Y σ ω := Real.exp_pos _

theorem Y_nonneg (σ ω : ℝ) : 0 ≤ Y σ ω := (Y_pos σ ω).le

/-! ### Step 1: Pointwise `Y σ ω → 0` as `σ → ∞`. -/

/-- The exponent `σω − σ²/2 → −∞` as `σ → ∞` for any fixed `ω`. -/
private theorem tendsto_exponent_atBot (ω : ℝ) :
    Tendsto (fun σ : ℝ => σ * ω - σ^2 / 2) atTop atBot := by
  -- σω - σ²/2 = -σ · (σ/2 - ω).  As σ → ∞, both σ and σ/2 - ω → ∞;
  -- product → ∞; negation → -∞.
  have h_rewrite : (fun σ : ℝ => σ * ω - σ^2 / 2)
      = (fun σ : ℝ => -(σ * (σ / 2 - ω))) := by
    funext σ; ring
  rw [h_rewrite]
  -- Show σ · (σ/2 - ω) → ∞ as σ → ∞.
  have h_div : Tendsto (fun σ : ℝ => σ / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 2) tendsto_id
  have h_half : Tendsto (fun σ : ℝ => σ / 2 - ω) atTop atTop := by
    have := h_div.atTop_add (tendsto_const_nhds (x := -ω))
    simpa [sub_eq_add_neg] using this
  have h_mul : Tendsto (fun σ : ℝ => σ * (σ / 2 - ω)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ h_half
  exact tendsto_neg_atTop_atBot.comp h_mul

/-- `Y σ ω → 0` as `σ → ∞`, pointwise in `ω`. -/
theorem tendsto_Y_atTop_zero (ω : ℝ) :
    Tendsto (fun σ : ℝ => Y σ ω) atTop (𝓝 0) := by
  unfold Y
  exact Real.tendsto_exp_atBot.comp (tendsto_exponent_atBot ω)

/-! ### Step 2: `𝔼[Y σ] = 1` for every σ. -/

/-- **Mean of the σ-parametrised lognormal is 1.**  Direct from
    `mgf_id_gaussianReal` (Mathlib): the Gaussian mgf at `σ` is
    `exp(σ²/2)`, and combining with the location factor `exp(−σ²/2)`
    gives 1. -/
theorem integral_Y_eq_one (σ : ℝ) :
    ∫ ω, Y σ ω ∂(gaussianReal 0 1) = 1 := by
  unfold Y
  -- exp(σω - σ²/2) = exp(-σ²/2) · exp(σω) pointwise.
  have h_factor : ∀ ω : ℝ,
      Real.exp (σ * ω - σ^2 / 2) = Real.exp (-(σ^2 / 2)) * Real.exp (σ * ω) := by
    intro ω
    rw [← Real.exp_add]; congr 1; ring
  rw [show (fun ω => Real.exp (σ * ω - σ^2 / 2))
      = (fun ω => Real.exp (-(σ^2 / 2)) * Real.exp (σ * ω)) from funext h_factor]
  rw [integral_const_mul]
  -- The remaining integral is the Gaussian mgf at σ.
  have h_mgf : ∫ ω, Real.exp (σ * ω) ∂(gaussianReal 0 1)
      = Real.exp (σ^2 / 2) := by
    have := mgf_id_gaussianReal (μ := 0) (v := 1)
    have h_apply : mgf id (gaussianReal 0 1) σ
        = Real.exp ((0 : ℝ) * σ + (1 : ℝ≥0) * σ^2 / 2) := by
      have h_eval := congrFun this σ
      exact h_eval
    rw [show ∫ ω, Real.exp (σ * ω) ∂(gaussianReal 0 1)
        = mgf id (gaussianReal 0 1) σ from rfl]
    rw [h_apply]
    push_cast
    congr 1; ring
  rw [h_mgf]
  rw [← Real.exp_add]
  have : -(σ^2 / 2) + σ^2 / 2 = 0 := by ring
  rw [this, Real.exp_zero]

/-! ### Step 3: `𝔼[min(Y σ, 1)] → 0` as `σ → ∞` (DCT).

We use the auxiliary `min(Y σ, 1)` (nonneg, bounded by `1`) rather than
`Y σ · 𝟙_{Y σ ≤ 1}`.  Both approaches work, but `min` is cleaner because
the bound is uniform and the pointwise limit is just continuity of `min`
at `(0, 1)`. -/

/-- DCT applied to `min(Y σ ω, 1)`: bounded by `1`, pointwise → 0. -/
theorem integral_min_Y_one_tendsto_zero :
    Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1))
      atTop (𝓝 0) := by
  -- `atTop` on ℝ is countably generated (basis `Ici n` for n ∈ ℕ).
  have h_bound_int : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
    integrable_const _
  -- Apply DCT with bound `1`.
  have h_lim_zero :
      Tendsto (fun σ : ℝ => ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1))
        atTop (𝓝 (∫ ω, (0 : ℝ) ∂(gaussianReal 0 1))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (1 : ℝ))
    · -- AE measurability of `min(Y σ, 1)` for σ large enough (in fact all σ).
      refine Filter.Eventually.of_forall (fun σ => ?_)
      have h_meas_Y : Measurable (fun ω => Y σ ω) := by
        unfold Y
        fun_prop
      exact (h_meas_Y.min measurable_const).aestronglyMeasurable
    · -- bound: |min(Y σ, 1)| ≤ 1.  Since Y σ > 0, min ∈ (0, 1], so ≤ 1.
      refine Filter.Eventually.of_forall (fun σ => ?_)
      refine .of_forall (fun ω => ?_)
      have h_min_nn : 0 ≤ min (Y σ ω) 1 := le_min (Y_nonneg σ ω) (by norm_num)
      have h_min_le : min (Y σ ω) 1 ≤ 1 := min_le_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg h_min_nn]
      exact h_min_le
    · exact h_bound_int
    · -- pointwise: min(Y σ ω, 1) → min(0, 1) = 0 by continuity of min.
      refine .of_forall (fun ω => ?_)
      have h_min : Tendsto (fun σ : ℝ => min (Y σ ω) 1) atTop (𝓝 (min 0 1)) :=
        (tendsto_Y_atTop_zero ω).min tendsto_const_nhds
      simpa using h_min
  rw [integral_zero] at h_lim_zero
  exact h_lim_zero

/-! ### Step 4: `M(1; σ) → 2` as `σ → ∞`. -/

/-- **Identity** `(Y − 1)⁺ = Y − min(Y, 1)` for `Y ≥ 0`. -/
private lemma pos_part_sub_one_eq (y : ℝ) (_hy : 0 ≤ y) :
    max (y - 1) 0 = y - min y 1 := by
  by_cases h : y ≤ 1
  · have h1 : y - 1 ≤ 0 := by linarith
    rw [max_eq_right h1, min_eq_left h]; ring
  · push Not at h
    have h1 : 0 < y - 1 := by linarith
    rw [max_eq_left h1.le, min_eq_right h.le]

/-- **Identity** `|Y − 1| = 2·(Y − 1)⁺ + (1 − Y)` for `Y ≥ 0`.
    More useful form: when integrated against a probability measure with
    `𝔼Y = 1`, the `(1 − Y)` term has expectation 0, giving
    `𝔼|Y − 1| = 2·𝔼[(Y − 1)⁺]`. -/
private lemma abs_sub_one_eq_two_pos_part_plus (y : ℝ) (_hy : 0 ≤ y) :
    |y - 1| = 2 * max (y - 1) 0 + (1 - y) := by
  by_cases h : y ≤ 1
  · have h1 : y - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos h1, max_eq_right h1]; ring
  · push Not at h
    have h1 : 0 < y - 1 := by linarith
    rw [abs_of_pos h1, max_eq_left h1.le]; ring

/-- **`M(1; σ) → 2`** — the headline σ→∞ asymptotic.

    With `Y σ ~ lognormalReal(-σ²/2, σ²)` (mean 1),
        `M(1; σ) = 𝔼|Y σ − 1| → 2`. -/
theorem M_one_tendsto_two :
    Tendsto (fun σ : ℝ => ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1))
      atTop (𝓝 2) := by
  -- Rewrite `|Y − 1| = 2(Y − 1)⁺ + (1 − Y) = 2(Y − min(Y, 1)) + (1 − Y)`.
  -- Integrating: ∫|Y − 1| = 2(∫Y − ∫min(Y, 1)) + (1 − ∫Y) = 2 − 2·∫min(Y, 1).
  -- As σ → ∞, ∫min(Y, 1) → 0 (DCT), hence ∫|Y − 1| → 2.
  have h_eq : ∀ σ : ℝ,
      ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1)
        = 2 * (1 - ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1)) := by
    intro σ
    -- Step a: pointwise identity.
    have h_pt : ∀ ω, |Y σ ω - 1|
        = 2 * (Y σ ω - min (Y σ ω) 1) + (1 - Y σ ω) := by
      intro ω
      rw [abs_sub_one_eq_two_pos_part_plus _ (Y_nonneg σ ω)]
      rw [pos_part_sub_one_eq _ (Y_nonneg σ ω)]
    have h_fun_eq : (fun ω => |Y σ ω - 1|)
        = fun ω => 2 * (Y σ ω - min (Y σ ω) 1) + (1 - Y σ ω) :=
      funext h_pt
    rw [h_fun_eq]
    -- Step b: integrability of each piece.
    have h_Y_int : Integrable (Y σ) (gaussianReal 0 1) := by
      unfold Y
      have h_factor : (fun ω => Real.exp (σ * ω - σ^2 / 2))
          = (fun ω => Real.exp (-(σ^2/2)) * Real.exp (σ * ω)) := by
        funext ω; rw [← Real.exp_add]; congr 1; ring
      rw [h_factor]
      exact (integrable_exp_mul_gaussianReal σ).const_mul _
    have h_min_int : Integrable (fun ω => min (Y σ ω) 1) (gaussianReal 0 1) := by
      have h_meas_Y : Measurable (Y σ) := by unfold Y; fun_prop
      have h_aestrong : AEStronglyMeasurable (fun ω => min (Y σ ω) 1)
          (gaussianReal 0 1) :=
        (h_meas_Y.min measurable_const).aestronglyMeasurable
      refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _) h_aestrong ?_
      refine .of_forall (fun ω => ?_)
      have h_nn : 0 ≤ min (Y σ ω) 1 := le_min (Y_nonneg σ ω) (by norm_num)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact min_le_right _ _
    -- Step c: integrate.
    have h_int1 : Integrable (fun ω => 2 * (Y σ ω - min (Y σ ω) 1)) (gaussianReal 0 1) :=
      (h_Y_int.sub h_min_int).const_mul 2
    have h_int2 : Integrable (fun ω => (1 : ℝ) - Y σ ω) (gaussianReal 0 1) :=
      (integrable_const _).sub h_Y_int
    rw [integral_add h_int1 h_int2, integral_const_mul,
        integral_sub h_Y_int h_min_int,
        integral_sub (integrable_const _) h_Y_int,
        integral_Y_eq_one σ, integral_const]
    simp
  -- Apply the rewriting and the DCT limit.
  rw [show (fun σ => ∫ ω, |Y σ ω - 1| ∂(gaussianReal 0 1))
      = fun σ => 2 * (1 - ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1)) from
    funext h_eq]
  -- 2 · (1 − f(σ)) → 2 · (1 − 0) = 2, where f(σ) → 0.
  have h_target : Tendsto (fun σ : ℝ =>
        (2 : ℝ) * (1 - ∫ ω, min (Y σ ω) 1 ∂(gaussianReal 0 1)))
      atTop (𝓝 (2 * (1 - 0))) :=
    (tendsto_const_nhds.sub integral_min_Y_one_tendsto_zero).const_mul 2
  simpa using h_target

end TailOptionPricing.LognormalAsymptotic
