module

/-
  Karamata's theory of regular variation — closure properties.

  Slow variation is preserved under eventual equality, pointwise products
  and quotients of positive SV functions, and translations.
-/
public import Stats.RegularVariation.Defs
public import Stats.RegularVariation.UCT

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-- A function that is eventually equal to a slowly varying function is itself
    slowly varying. -/
theorem IsSlowlyVarying.congr_eventuallyEq {L M : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (h_eq : L =ᶠ[atTop] M) :
    IsSlowlyVarying M := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have h_eq_tx : (fun t : ℝ => L (t * x)) =ᶠ[atTop] (fun t => M (t * x)) :=
    h_lift.eventually h_eq
  have h_ratio_eq :
      (fun t : ℝ => L (t * x) / L t) =ᶠ[atTop] (fun t => M (t * x) / M t) := by
    filter_upwards [h_eq_tx, h_eq] with t htx ht
    rw [htx, ht]
  exact (hL x hx).congr' h_ratio_eq

/-- Pointwise product of slowly varying functions is slowly varying. -/
theorem IsSlowlyVarying.mul {L M : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (hM : IsSlowlyVarying M)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hM_pos : ∀ᶠ s in atTop, 0 < M s) :
    IsSlowlyVarying (fun s => L s * M s) := by
  intro x hx
  have h_ratio_eq :
      (fun t : ℝ => L (t * x) * M (t * x) / (L t * M t)) =ᶠ[atTop]
      (fun t => (L (t * x) / L t) * (M (t * x) / M t)) := by
    filter_upwards [hL_pos, hM_pos] with t hL_t hM_t
    field_simp
  have h_prod : Tendsto (fun t : ℝ => (L (t * x) / L t) * (M (t * x) / M t))
      atTop (𝓝 1) := by
    have := (hL x hx).mul (hM x hx)
    simpa using this
  exact h_prod.congr' h_ratio_eq.symm

/-- Pointwise inverse of an eventually-positive slowly varying function
    is slowly varying.  `(1/L)(t·x) / (1/L)(t) = L(t)/L(t·x) → 1`. -/
theorem IsSlowlyVarying.inv {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (hL_pos : ∀ᶠ s in atTop, 0 < L s) :
    IsSlowlyVarying (fun s => (L s)⁻¹) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hL_pos_tx : ∀ᶠ t in atTop, 0 < L (t * x) := h_lift.eventually hL_pos
  have h_ratio_eq : ∀ᶠ t in atTop,
      (L (t * x))⁻¹ / (L t)⁻¹ = (L (t * x) / L t)⁻¹ := by
    filter_upwards [hL_pos, hL_pos_tx] with t hL_t hL_tx
    field_simp
  have h_to : Tendsto (fun t : ℝ => (L (t * x) / L t)⁻¹) atTop (𝓝 ((1 : ℝ)⁻¹)) :=
    (hL x hx).inv₀ one_ne_zero
  rw [inv_one] at h_to
  exact h_to.congr' (h_ratio_eq.mono fun _ h => h.symm)

/-- Pointwise quotient of slowly varying functions is slowly varying. -/
theorem IsSlowlyVarying.div {L M : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (hM : IsSlowlyVarying M)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hM_pos : ∀ᶠ s in atTop, 0 < M s) :
    IsSlowlyVarying (fun s => L s / M s) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hM_pos_tx : ∀ᶠ t in atTop, 0 < M (t * x) := h_lift.eventually hM_pos
  have h_ratio_eq :
      (fun t : ℝ => L (t * x) / M (t * x) / (L t / M t)) =ᶠ[atTop]
      (fun t => (L (t * x) / L t) / (M (t * x) / M t)) := by
    filter_upwards [hL_pos, hM_pos, hM_pos_tx] with t hL_t hM_t hM_tx
    field_simp
  have h_quot : Tendsto (fun t : ℝ => (L (t * x) / L t) / (M (t * x) / M t))
      atTop (𝓝 1) := by
    have := (hL x hx).div (hM x hx) one_ne_zero
    convert this using 1 ; simp
  exact h_quot.congr' h_ratio_eq.symm

/-- **Translation invariance under monotonicity.**  For slowly varying
    `L > 0` that is monotone (or antitone) on `(0, ∞)`, `s ↦ L(s + c)` is
    also slowly varying.

    *Note.*  No "general" `comp_translation` (without a regularity
    hypothesis) is provable — pathological non-measurable SV functions exist
    for which `L(t+1)/L(t)` does not tend to `1`.  The standard textbook
    proof routes through UCT, which we have here only in monotone form.

    Proof uses `uniform_convergence_of_monotone`: the substitution
    `τ = t + c` reduces `L(t·x + c)/L(t + c)` to `L(τ·y_τ)/L(τ)` with
    `y_τ → x`, which → 1 by UCT applied to a compact sub-interval of
    `(0, ∞)` containing `x`. -/
theorem IsSlowlyVarying.comp_translation_of_monotone {L : ℝ → ℝ} (c : ℝ)
    (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : MonotoneOn L (Set.Ioi 0) ∨ AntitoneOn L (Set.Ioi 0)) :
    IsSlowlyVarying (fun s => L (s + c)) := by
  intro x hx
  -- After substituting τ = t + c, the goal `L(t·x+c)/L(t+c) → 1`
  -- becomes `L(τ·x + α)/L(τ) → 1` with α = c·(1-x).
  set α := c * (1 - x) with hα_def
  -- Step 1: prove `L(τ·x + α)/L(τ) → 1` along atTop in τ.
  have h_main : Tendsto (fun τ : ℝ => L (τ * x + α) / L τ) atTop (𝓝 1) := by
    -- UCT on [x/2, 2x] (an interval containing x with positive endpoints).
    have hx_2_pos : (0 : ℝ) < x / 2 := by linarith
    have h2x_pos : (0 : ℝ) < 2 * x := by linarith
    have h_a_le_b : x / 2 ≤ 2 * x := by linarith
    have h_uct := hL.uniform_convergence_of_monotone hL_pos hL_mono hx_2_pos h_a_le_b
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendstoUniformlyOn_iff] at h_uct
    rcases Filter.eventually_atTop.mp (h_uct ε hε) with ⟨N₁, hN₁⟩
    -- y_τ := x + α/τ → x; need y_τ ∈ [x/2, 2x] eventually.
    -- |y_τ - x| = |α|/τ ≤ x/2 ⟺ τ ≥ 2·|α|/x.
    refine ⟨max N₁ (max 1 (2 * |α| / x + 1)), fun τ hτ => ?_⟩
    have hτ_ge_N₁ : N₁ ≤ τ := le_trans (le_max_left _ _) hτ
    have hτ_ge_1 : 1 ≤ τ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
    have hτ_ge_α : 2 * |α| / x + 1 ≤ τ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
    have hτ_pos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ_ge_1
    have h_α_div_le : |α / τ| ≤ x / 2 := by
      rw [abs_div, abs_of_pos hτ_pos, div_le_iff₀ hτ_pos]
      have : 2 * |α| ≤ x * τ - x := by
        have h_τ : 2 * |α| / x ≤ τ - 1 := by linarith
        have hx' : 0 < x := hx
        calc 2 * |α| = (2 * |α| / x) * x := by field_simp
          _ ≤ (τ - 1) * x :=
              mul_le_mul_of_nonneg_right h_τ hx'.le
          _ = x * τ - x := by ring
      linarith
    set y := x + α / τ with hy_def
    have hy_in : y ∈ Set.Icc (x / 2) (2 * x) := by
      refine ⟨?_, ?_⟩
      · have : -(x / 2) ≤ α / τ := by
          have := abs_le.mp h_α_div_le
          linarith [this.1]
        linarith [hy_def]
      · have : α / τ ≤ x / 2 := (abs_le.mp h_α_div_le).2
        rw [hy_def]; linarith
    -- Apply UCT at τ, y.
    have h_uct_τ := hN₁ τ hτ_ge_N₁ y hy_in
    -- L(τ · y) = L(τ · (x + α/τ)) = L(τ·x + α) (using division by positive τ).
    have h_τy : τ * y = τ * x + α := by
      rw [hy_def]; field_simp
    rw [h_τy] at h_uct_τ
    rwa [dist_comm] at h_uct_τ
  -- Step 2: lift along τ = t + c.
  have h_lift : Tendsto (fun t : ℝ => t + c) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop c tendsto_id
  have h_comp : Tendsto (fun t : ℝ => L ((t + c) * x + α) / L (t + c))
      atTop (𝓝 1) := h_main.comp h_lift
  -- Step 3: (t + c)·x + α = t·x + c (algebraic identity, using α = c·(1-x)).
  have h_eq : ∀ t : ℝ,
      L ((t + c) * x + α) / L (t + c) = L (t * x + c) / L (t + c) := by
    intro t
    have h_arg_eq : (t + c) * x + α = t * x + c := by rw [hα_def]; ring
    rw [h_arg_eq]
  -- Goal: Tendsto (fun t => L((t·x) + c) / L(t + c)) atTop (𝓝 1).
  -- Note: the SV definition uses L((t·x) + c) but our function is `fun s => L(s + c)`,
  -- so SV at x means L(t·x + c) / L(t + c) → 1. Match.
  exact h_comp.congr h_eq

/-- **Real-power closure.**  If `L` is slowly varying and eventually positive,
    then `s ↦ (L s)^k` is slowly varying for every real `k`.  Proof: the
    ratio `(L(t·x))^k / (L t)^k = (L(t·x)/L t)^k → 1^k = 1` by continuity of
    `y ↦ y^k` at `y = 1`. -/
theorem IsSlowlyVarying.rpow {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (hL_pos : ∀ᶠ s in atTop, 0 < L s) (k : ℝ) :
    IsSlowlyVarying (fun s => (L s) ^ k) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hL_pos_tx : ∀ᶠ t in atTop, 0 < L (t * x) := h_lift.eventually hL_pos
  have h_ratio_eq : ∀ᶠ t in atTop,
      (L (t * x)) ^ k / (L t) ^ k = (L (t * x) / L t) ^ k := by
    filter_upwards [hL_pos, hL_pos_tx] with t hL_t hL_tx
    rw [← Real.div_rpow hL_tx.le hL_t.le]
  have h_to_one : Tendsto (fun t : ℝ => L (t * x) / L t) atTop (𝓝 1) := hL x hx
  have h_pow_to_one :
      Tendsto (fun t : ℝ => (L (t * x) / L t) ^ k) atTop (𝓝 1) := by
    have h_cont : ContinuousAt (fun y : ℝ => y ^ k) 1 :=
      Real.continuousAt_rpow_const _ k (Or.inl one_ne_zero)
    have h_lim : Tendsto (fun y : ℝ => y ^ k) (𝓝 1) (𝓝 ((1 : ℝ) ^ k)) :=
      h_cont.tendsto
    rw [show (1 : ℝ) = (1 : ℝ) ^ k from (Real.one_rpow k).symm]
    exact h_lim.comp h_to_one
  exact h_pow_to_one.congr' (h_ratio_eq.mono fun _ h => h.symm)

/-! ### Bridges between slow and regular variation -/

/-- **Bridge from slow to regular variation.**  If `L` is slowly varying
    (eventually positive), then `s ↦ s^k · L(s)` is regularly varying with
    index `k`.  This generalizes `survival_isRegularlyVarying` (the
    constant-`L` case) and gives a generic construction of `RV_k` from any
    proved-SV remainder. -/
theorem isRegularlyVarying_rpow_mul {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s) (k : ℝ) :
    IsRegularlyVarying (fun s => s ^ k * L s) k := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hL_pos_tx : ∀ᶠ t in atTop, 0 < L (t * x) := h_lift.eventually hL_pos
  have h_ratio_eq : ∀ᶠ t in atTop,
      (t * x) ^ k * L (t * x) / (t ^ k * L t) =
        x ^ k * (L (t * x) / L t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hL_pos, hL_pos_tx]
      with t ht hL_t hL_tx
    have h_t_rpow_pos : 0 < t ^ k := Real.rpow_pos_of_pos ht k
    rw [Real.mul_rpow ht.le hx.le]
    field_simp
  have h_to_xk : Tendsto (fun t : ℝ => x ^ k * (L (t * x) / L t))
      atTop (𝓝 (x ^ k * 1)) :=
    (hL x hx).const_mul (x ^ k)
  have h_simp : (x : ℝ) ^ k * 1 = x ^ k := mul_one _
  rw [h_simp] at h_to_xk
  exact h_to_xk.congr' (h_ratio_eq.mono fun _ h => h.symm)

/-- **Reverse bridge.**  If `f` is regularly varying with index `k` and
    eventually positive, then `s ↦ f(s) / s^k` is slowly varying.

    Together with `isRegularlyVarying_rpow_mul`, this gives the structural
    decomposition: `f ∈ RV_k ⟺ f(s) = s^k · L(s)` for some slowly-varying
    `L` (modulo the eventual-positivity caveat). -/
theorem IsRegularlyVarying.div_rpow_isSlowlyVarying {f : ℝ → ℝ} {k : ℝ}
    (hf : IsRegularlyVarying f k) (hf_pos : ∀ᶠ s in atTop, 0 < f s) :
    IsSlowlyVarying (fun s => f s / s ^ k) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hf_pos_tx : ∀ᶠ t in atTop, 0 < f (t * x) := h_lift.eventually hf_pos
  have h_ratio_eq : ∀ᶠ t in atTop,
      f (t * x) / (t * x) ^ k / (f t / t ^ k) =
        f (t * x) / f t / x ^ k := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hf_pos, hf_pos_tx]
      with t ht hf_t hf_tx
    have h_t_rpow : 0 < t ^ k := Real.rpow_pos_of_pos ht k
    have h_x_rpow : 0 < x ^ k := Real.rpow_pos_of_pos hx k
    rw [Real.mul_rpow ht.le hx.le]
    field_simp
  have h_to : Tendsto (fun t : ℝ => f (t * x) / f t / x ^ k)
      atTop (𝓝 (x ^ k / x ^ k)) := (hf x hx).div_const _
  have h_eq_one : x ^ k / x ^ k = 1 :=
    div_self (Real.rpow_pos_of_pos hx k).ne'
  rw [h_eq_one] at h_to
  exact h_to.congr' (h_ratio_eq.mono fun _ h => h.symm)

/-! ### Closure of `IsRegularlyVarying` -/

/-- The pure power `s ↦ s^k` is regularly varying with index `k`.  This is
    the canonical `RV_k` example. -/
theorem isRegularlyVarying_rpow (k : ℝ) :
    IsRegularlyVarying (fun s => s ^ k) k := by
  intro x hx
  have h_eq : ∀ᶠ t in atTop, (t * x) ^ k / t ^ k = x ^ k := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h_t_rpow : 0 < t ^ k := Real.rpow_pos_of_pos ht k
    rw [Real.mul_rpow ht.le hx.le]
    field_simp
  exact (tendsto_const_nhds.congr' (h_eq.mono fun _ h => h.symm))

/-- Pointwise product: `f ∈ RV_α`, `g ∈ RV_β` ⟹ `f · g ∈ RV_{α+β}`.

    Requires both `f` and `g` to be eventually nonzero so the ratio
    `(f·g)(t·x)/(f·g)(t)` decomposes into `(f(t·x)/f(t)) · (g(t·x)/g(t))`. -/
theorem IsRegularlyVarying.mul {f g : ℝ → ℝ} {α β : ℝ}
    (hf : IsRegularlyVarying f α) (hg : IsRegularlyVarying g β)
    (hf_ne : ∀ᶠ s in atTop, f s ≠ 0)
    (hg_ne : ∀ᶠ s in atTop, g s ≠ 0) :
    IsRegularlyVarying (fun s => f s * g s) (α + β) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hf_ne_tx := h_lift.eventually hf_ne
  have hg_ne_tx := h_lift.eventually hg_ne
  have h_eq : ∀ᶠ t in atTop,
      f (t * x) * g (t * x) / (f t * g t) =
        (f (t * x) / f t) * (g (t * x) / g t) := by
    filter_upwards [hf_ne, hg_ne, hf_ne_tx, hg_ne_tx]
      with t hf_t hg_t hf_tx hg_tx
    field_simp
  have h_to : Tendsto (fun t : ℝ => f (t * x) / f t * (g (t * x) / g t))
      atTop (𝓝 (x ^ α * x ^ β)) := (hf x hx).mul (hg x hx)
  rw [show x ^ α * x ^ β = x ^ (α + β) from (Real.rpow_add hx α β).symm] at h_to
  exact h_to.congr' (h_eq.mono fun _ h => h.symm)

/-- Pointwise quotient: `f ∈ RV_α`, `g ∈ RV_β` ⟹ `f / g ∈ RV_{α-β}`. -/
theorem IsRegularlyVarying.div {f g : ℝ → ℝ} {α β : ℝ}
    (hf : IsRegularlyVarying f α) (hg : IsRegularlyVarying g β)
    (hf_ne : ∀ᶠ s in atTop, f s ≠ 0)
    (hg_ne : ∀ᶠ s in atTop, g s ≠ 0) :
    IsRegularlyVarying (fun s => f s / g s) (α - β) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hg_ne_tx := h_lift.eventually hg_ne
  have h_eq : ∀ᶠ t in atTop,
      f (t * x) / g (t * x) / (f t / g t) =
        (f (t * x) / f t) / (g (t * x) / g t) := by
    filter_upwards [hf_ne, hg_ne, hg_ne_tx] with t hf_t hg_t hg_tx
    field_simp
  have h_to : Tendsto (fun t : ℝ => f (t * x) / f t / (g (t * x) / g t))
      atTop (𝓝 (x ^ α / x ^ β)) :=
    (hf x hx).div (hg x hx) (Real.rpow_pos_of_pos hx β).ne'
  have h_pow_div : x ^ α / x ^ β = x ^ (α - β) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_neg hx.le, div_eq_mul_inv]
  rw [h_pow_div] at h_to
  exact h_to.congr' (h_eq.mono fun _ h => h.symm)

/-- Real-power: `f ∈ RV_α` (eventually positive) ⟹ `f^k ∈ RV_{α·k}`. -/
theorem IsRegularlyVarying.rpow {f : ℝ → ℝ} {α : ℝ}
    (hf : IsRegularlyVarying f α) (hf_pos : ∀ᶠ s in atTop, 0 < f s) (k : ℝ) :
    IsRegularlyVarying (fun s => (f s) ^ k) (α * k) := by
  intro x hx
  have h_lift : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hx
  have hf_pos_tx := h_lift.eventually hf_pos
  have h_eq : ∀ᶠ t in atTop,
      (f (t * x)) ^ k / (f t) ^ k = (f (t * x) / f t) ^ k := by
    filter_upwards [hf_pos, hf_pos_tx] with t hf_t hf_tx
    rw [← Real.div_rpow hf_tx.le hf_t.le]
  have h_cont : ContinuousAt (fun y : ℝ => y ^ k) (x ^ α) :=
    Real.continuousAt_rpow_const _ k (Or.inl (Real.rpow_pos_of_pos hx α).ne')
  have h_to : Tendsto (fun t : ℝ => (f (t * x) / f t) ^ k)
      atTop (𝓝 ((x ^ α) ^ k)) := h_cont.tendsto.comp (hf x hx)
  have h_pow : (x ^ α) ^ k = x ^ (α * k) := (Real.rpow_mul hx.le α k).symm
  rw [h_pow] at h_to
  exact h_to.congr' (h_eq.mono fun _ h => h.symm)

end TailOptionPricing
