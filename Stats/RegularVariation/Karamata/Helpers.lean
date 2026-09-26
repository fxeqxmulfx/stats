/-
  Karamata's theory of regular variation.

  ## Stats.RegularVariation.Karamata.Helpers — auxiliary step / telescope lemmas.

  Step bound from pointwise SV, telescoping inequality, and the
  `log_one_add_ge_half` shrinkage estimate.  Used by both the
  monotone and measurable variants of the `o`-bound theorem.

  See `Stats/RegularVariation/Karamata.lean` for the umbrella.
-/
import Stats.RegularVariation.Defs
import Stats.RegularVariation.UCT

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics

namespace TailOptionPricing

/-! ### Helper lemmas. -/

/-- **Step bound from pointwise SV.**  For any `K > 0` and `r > 0`, eventually
    `|log L(t·r) - log L(t)| ≤ K`.  Pointwise SV says `L(t·r)/L(t) → 1`; by
    continuity of `log` at `1` (and `log 1 = 0`), `log L(t·r) - log L(t) → 0`,
    so the absolute value is eventually `≤ K`. -/
lemma IsSlowlyVarying.log_step_bound_eventually
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    {r : ℝ} (hr : 0 < r) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ t in atTop, |Real.log (L (t * r)) - Real.log (L t)| ≤ K := by
  have h_lift : Tendsto (fun t : ℝ => t * r) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hr
  have h_to_one : Tendsto (fun t : ℝ => L (t * r) / L t) atTop (𝓝 1) :=
    hL r hr
  have h_log_cont : ContinuousAt Real.log 1 :=
    Real.continuousAt_log one_ne_zero
  have h_log_tendsto : Tendsto Real.log (𝓝 1) (𝓝 0) := by
    have := h_log_cont.tendsto
    rwa [Real.log_one] at this
  have h_log_to_zero :
      Tendsto (fun t : ℝ => Real.log (L (t * r) / L t)) atTop (𝓝 0) :=
    h_log_tendsto.comp h_to_one
  have h_close : ∀ᶠ t in atTop, |Real.log (L (t * r) / L t)| ≤ K := by
    have h_ball : Set.Icc (-K) K ∈ 𝓝 (0 : ℝ) :=
      Icc_mem_nhds (by linarith) hK
    have := h_log_to_zero.eventually h_ball
    exact this.mono (fun t ht => abs_le.mpr ht)
  filter_upwards [h_close, hL_pos, h_lift.eventually hL_pos]
    with t h_close_t hL_t hL_tr
  rwa [Real.log_div hL_tr.ne' hL_t.ne'] at h_close_t

/-- **Telescoping inequality.**  Iterating a one-step bound `|log L(t·r) −
    log L(t)| ≤ K` (valid for `t ≥ T₀`) over `n` multiplicative steps. -/
lemma log_L_telescope {L : ℝ → ℝ} {r T₀ K : ℝ}
    (hr : 1 ≤ r) (hT₀ : 0 < T₀)
    (h_step : ∀ t, T₀ ≤ t → |Real.log (L (t * r)) - Real.log (L t)| ≤ K) :
    ∀ n : ℕ, ∀ t, T₀ ≤ t →
      |Real.log (L (t * r ^ n)) - Real.log (L t)| ≤ n * K := by
  intro n
  induction n with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    have h_rk_ge_one : (1 : ℝ) ≤ r ^ k := one_le_pow₀ hr
    have h_t_pos : 0 < t := lt_of_lt_of_le hT₀ ht
    have h_t_rk : T₀ ≤ t * r ^ k := by
      calc T₀ ≤ t := ht
        _ = t * 1 := (mul_one t).symm
        _ ≤ t * r ^ k := mul_le_mul_of_nonneg_left h_rk_ge_one h_t_pos.le
    have h_step_at :
        |Real.log (L ((t * r ^ k) * r)) - Real.log (L (t * r ^ k))| ≤ K :=
      h_step (t * r ^ k) h_t_rk
    have h_ih := ih t ht
    have h_succ : t * r ^ (k + 1) = (t * r ^ k) * r := by rw [pow_succ]; ring
    rw [h_succ]
    have h_split :
        Real.log (L ((t * r ^ k) * r)) - Real.log (L t) =
        (Real.log (L ((t * r ^ k) * r)) - Real.log (L (t * r ^ k))) +
        (Real.log (L (t * r ^ k)) - Real.log (L t)) := by ring
    calc |Real.log (L ((t * r ^ k) * r)) - Real.log (L t)|
        = |(Real.log (L ((t * r ^ k) * r)) - Real.log (L (t * r ^ k))) +
            (Real.log (L (t * r ^ k)) - Real.log (L t))| := by rw [h_split]
      _ ≤ |Real.log (L ((t * r ^ k) * r)) - Real.log (L (t * r ^ k))| +
          |Real.log (L (t * r ^ k)) - Real.log (L t)| :=
            abs_add_le (Real.log (L ((t * r ^ k) * r)) - Real.log (L (t * r ^ k)))
              (Real.log (L (t * r ^ k)) - Real.log (L t))
      _ ≤ K + (k : ℝ) * K := add_le_add h_step_at h_ih
      _ = (↑(k + 1) : ℝ) * K := by push_cast; ring

/-- For `0 < δ ≤ 1`, `log(1 + δ) ≥ δ/2`.  Used to lower-bound `log r`
    where `r = 1 + δ`.  Standard chain
    `δ/2 ≤ δ/(1+δ) ≤ log(1+δ)` via `Real.one_sub_inv_le_log_of_pos`. -/
lemma log_one_add_ge_half {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    δ / 2 ≤ Real.log (1 + δ) := by
  have h1 : 0 < 1 + δ := by linarith
  have h1_ne : (1 + δ : ℝ) ≠ 0 := h1.ne'
  have h_id : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by
    field_simp
    ring
  have h_log : 1 - (1 + δ)⁻¹ ≤ Real.log (1 + δ) :=
    Real.one_sub_inv_le_log_of_pos h1
  rw [h_id] at h_log
  have h_div : δ / 2 ≤ δ / (1 + δ) := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h1]
    nlinarith
  linarith

end TailOptionPricing
