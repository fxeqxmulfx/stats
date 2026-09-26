/-
  Taleb's κ-metric for pre-asymptotic fat-tailedness.
    "How Much Data Do You Need?  A Pre-asymptotic Metric for Fat-tailedness"
    arXiv:1802.05495v3 (Nov 2018).

  ## Stats.Kappa.LoulakisLiminf — Loulakis main asymptotic `liminf M(n)/M(1) ≥ n`.

  Abstract `liminf` theorem combining:

  * The **algebraic** Loulakis lower bound (Phase C.3a,
    [LoulakisAlgebraic](Stats/Kappa/LoulakisAlgebraic.lean)):
        `M(n; σ) ≥ 2·(n · A_n(σ) − C(n,2) · B_n(σ))`,
    where `A_n(σ) := ∫_{t>0} ℙ_σ(Y > n + t) dt`,
    `B_n(σ) := ∫_{t>0} ℙ_σ(Y > n + t)² dt`.

  * The **σ→∞ asymptotics** (Phases B.5, B.7):
    - `M(1; σ) → 2` (from `LognormalAsymptotic.M_one_tendsto_two`);
      hence `A_1(σ) = M(1; σ)/2 → 1`.
    - `B_n(σ) → 0` as `σ → ∞` (Hölder bound, [LognormalMarkov](Stats/Kappa/LognormalMarkov.lean) Phase B.5).
    - `A_n(σ) → 1` as `σ → ∞` (tail leakage `A_1 − A_n → 0`).

  Yields:

      `liminf_{σ → ∞} M(n; σ) / M(1; σ) ≥ n`.

  This file is **abstract** in σ: it takes the relevant tendsto facts
  as hypotheses, isolating the pure `Filter.liminf` reasoning.  The
  hypotheses are discharged for the lognormal specifically in
  [LognormalAsymptotic.lean](Stats/Kappa/LognormalAsymptotic.lean)
  + [LognormalMarkov.lean](Stats/Kappa/LognormalMarkov.lean).
-/
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace TailOptionPricing.LoulakisLiminf

/-- **Abstract `liminf` Loulakis bound.**  Given σ-parametrised quantities
    `Mn σ`, `M1 σ`, `An σ`, `Bn σ` with:

    * `Mn σ ≥ 2 · (n · An σ − C(n,2) · Bn σ)` for every `σ` (algebraic
      Loulakis from C.3a);
    * `M1 σ = 2 · A1 σ` (layer cake at `n = 1`);
    * `M1 σ → 2` as `σ → ∞` (so `A1 σ → 1`);
    * `An σ → 1` as `σ → ∞` (tail-leakage convergence);
    * `Bn σ → 0` as `σ → ∞` (Hölder bound),

    we conclude `liminf_{σ → ∞} Mn σ / M1 σ ≥ n`.

    Pure algebra on the `Filter.liminf` API; no measure theory. -/
theorem liminf_M_ratio_ge_n
    {n : ℕ} {Mn M1 An Bn : ℝ → ℝ}
    (h_lower : ∀ σ, (2 : ℝ) * ((n : ℝ) * An σ - (n.choose 2 : ℝ) * Bn σ) ≤ Mn σ)
    (h_Mn_nn : ∀ σ, 0 ≤ Mn σ)
    (h_Mn_triangle : ∀ σ, Mn σ ≤ (n : ℝ) * M1 σ)
    (h_M1_tend : Tendsto M1 atTop (𝓝 2))
    (h_An_tend : Tendsto An atTop (𝓝 1))
    (h_Bn_tend : Tendsto Bn atTop (𝓝 0)) :
    (n : ℝ) ≤ Filter.liminf (fun σ : ℝ => Mn σ / M1 σ) atTop := by
  -- Strategy: bound `Mn/M1 ≥ g` where `g σ := lower bound / M1 σ`.
  -- Show `g → n`, so `n = liminf g ≤ liminf (Mn/M1)`.
  set g : ℝ → ℝ := fun σ =>
    (2 : ℝ) * ((n : ℝ) * An σ - (n.choose 2 : ℝ) * Bn σ) / M1 σ
  -- Numerator → 2n; denominator → 2; quotient → n.
  have h_g_tend : Tendsto g atTop (𝓝 (n : ℝ)) := by
    have h_num : Tendsto (fun σ =>
        (2 : ℝ) * ((n : ℝ) * An σ - (n.choose 2 : ℝ) * Bn σ)) atTop
          (𝓝 ((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0))) :=
      ((h_An_tend.const_mul (n : ℝ)).sub
        (h_Bn_tend.const_mul (n.choose 2 : ℝ))).const_mul 2
    have h_quot : Tendsto g atTop
        (𝓝 (((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0)) / 2)) :=
      h_num.div h_M1_tend (by norm_num : (2 : ℝ) ≠ 0)
    have h_limit_eq : (((2 : ℝ) * ((n : ℝ) * 1 - (n.choose 2 : ℝ) * 0)) / 2)
        = (n : ℝ) := by ring
    rw [h_limit_eq] at h_quot
    exact h_quot
  -- M1 > 0 eventually (since M1 → 2).
  have h_M1_pos : ∀ᶠ σ in atTop, 0 < M1 σ :=
    h_M1_tend.eventually_const_lt (by norm_num : (0 : ℝ) < 2)
  -- Pointwise: g σ ≤ Mn σ / M1 σ (eventually).
  have h_le : ∀ᶠ σ in atTop, g σ ≤ Mn σ / M1 σ := by
    filter_upwards [h_M1_pos] with σ hM1
    exact div_le_div_of_nonneg_right (h_lower σ) hM1.le
  -- Use the iff-form of `le_liminf` to avoid boundedness machinery.
  -- For any `y < n`, we need eventually `y < Mn σ / M1 σ`.
  -- We have `g σ → n`, so eventually `g σ > y`.  Combined with `g σ ≤ Mn/M1`,
  -- we get `Mn/M1 > y` eventually.
  -- The `le_liminf_iff` needs `IsCoboundedUnder` and `IsBoundedUnder (≥)`.
  -- `Mn/M1 ≥ 0` eventually (since `Mn ≥ 0`, `M1 > 0`): `IsBoundedUnder (≥)`.
  -- `Mn/M1 ≤ n` (from `h_Mn_triangle` and `M1 > 0`): `IsCoboundedUnder (≥)`.
  have h_ratio_nn : ∀ᶠ σ in atTop, 0 ≤ Mn σ / M1 σ := by
    filter_upwards [h_M1_pos] with σ hM1
    exact div_nonneg (h_Mn_nn σ) hM1.le
  have h_ratio_le : ∀ᶠ σ in atTop, Mn σ / M1 σ ≤ (n : ℝ) := by
    filter_upwards [h_M1_pos] with σ hM1
    rw [div_le_iff₀ hM1]
    exact h_Mn_triangle σ
  have h_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop (fun σ => Mn σ / M1 σ) :=
    ⟨0, h_ratio_nn⟩
  have h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop (fun σ => Mn σ / M1 σ) :=
    ⟨(n : ℝ), h_ratio_le⟩
  -- `IsBoundedUnder (· ≤ ·)` gives `IsCoboundedUnder (· ≥ ·)` (the function is
  -- bounded above, so any eventual lower bound is ≤ some upper bound).
  have h_cobdd_ge : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun σ => Mn σ / M1 σ) :=
    h_bdd_le.isCoboundedUnder_ge
  -- Apply `le_liminf_iff`.
  rw [Filter.le_liminf_iff h_cobdd_ge h_bdd_ge]
  intro y hy
  -- We have g σ → n, so eventually g σ > y.  Combined with g ≤ Mn/M1.
  have h_g_gt : ∀ᶠ σ in atTop, y < g σ := by
    have := h_g_tend.eventually_const_lt hy
    exact this
  filter_upwards [h_g_gt, h_le] with σ h1 h2
  linarith

end TailOptionPricing.LoulakisLiminf
