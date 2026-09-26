/-
  Karamata's theory of regular variation — Uniform Convergence Theorem.

  ## Stats.RegularVariation.UCT.Monotone — monotone UCT (Karamata 1933).

  Elementary sandwich proof: pointwise SV at the endpoints,
  monotonicity sandwiches `L(t·x)/L(t)` between them, so the
  same `(1−ε, 1+ε)` bound applies uniformly on `[a, b]`.

  See `Stats/RegularVariation/UCT.lean` for the umbrella.
-/
import Stats.RegularVariation.Defs

set_option maxHeartbeats 800000

open Real Set Filter Topology Asymptotics MeasureTheory

namespace TailOptionPricing

/-- **UCT under monotonicity.**  If `L` is slowly varying, eventually positive,
    and monotone (or antitone) on `(0, ∞)`, then `L(t·x)/L(t) → 1`
    uniformly in `x ∈ [a, b]` for any `0 < a ≤ b`.

    *Proof.*  Pointwise SV at `a` and `b` gives eventual `(1−ε, 1+ε)`-closeness
    for `L(t·a)/L(t)` and `L(t·b)/L(t)`.  Monotonicity sandwiches `L(t·x)/L(t)`
    between those endpoints, so the same `(1−ε, 1+ε)` bound applies uniformly
    on `[a, b]`. -/
theorem IsSlowlyVarying.uniform_convergence_of_monotone
    {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hL_pos : ∀ᶠ s in atTop, 0 < L s)
    (hL_mono : MonotoneOn L (Set.Ioi 0) ∨ AntitoneOn L (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun t x => L (t * x) / L t) (fun _ => 1)
      atTop (Set.Icc a b) := by
  have hb_pos : 0 < b := lt_of_lt_of_le ha hab
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε_pos
  have h_close_a : ∀ᶠ t in atTop, dist (L (t * a) / L t) 1 < ε :=
    (hL a ha).eventually (Metric.ball_mem_nhds 1 hε_pos)
  have h_close_b : ∀ᶠ t in atTop, dist (L (t * b) / L t) 1 < ε :=
    (hL b hb_pos).eventually (Metric.ball_mem_nhds 1 hε_pos)
  have h_lift_a : Tendsto (fun t : ℝ => t * a) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const ha
  have h_lift_b : Tendsto (fun t : ℝ => t * b) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hb_pos
  have h_pos_ta : ∀ᶠ t in atTop, 0 < L (t * a) := h_lift_a.eventually hL_pos
  have h_pos_tb : ∀ᶠ t in atTop, 0 < L (t * b) := h_lift_b.eventually hL_pos
  filter_upwards [h_close_a, h_close_b, hL_pos, h_pos_ta, h_pos_tb,
                  eventually_gt_atTop (0 : ℝ)]
    with t h_close_a h_close_b hL_t hL_ta hL_tb ht_pos x hx_in
  obtain ⟨hx_ge_a, hx_le_b⟩ := hx_in
  have h_ta_pos : 0 < t * a := mul_pos ht_pos ha
  have h_tx_pos : 0 < t * x := mul_pos ht_pos (lt_of_lt_of_le ha hx_ge_a)
  have h_tb_pos : 0 < t * b := mul_pos ht_pos hb_pos
  have h_ta_le_tx : t * a ≤ t * x := mul_le_mul_of_nonneg_left hx_ge_a ht_pos.le
  have h_tx_le_tb : t * x ≤ t * b := mul_le_mul_of_nonneg_left hx_le_b ht_pos.le
  -- In both monotone and antitone cases, L(t·x)/L(t) is sandwiched between
  -- L(t·a)/L(t) and L(t·b)/L(t).
  have h_sandwich : (L (t * a) / L t ≤ L (t * x) / L t ∧
                    L (t * x) / L t ≤ L (t * b) / L t) ∨
                   (L (t * b) / L t ≤ L (t * x) / L t ∧
                    L (t * x) / L t ≤ L (t * a) / L t) := by
    rcases hL_mono with hmono | hanti
    · left
      refine ⟨?_, ?_⟩
      · gcongr
        exact hmono h_ta_pos h_tx_pos h_ta_le_tx
      · gcongr
        exact hmono h_tx_pos h_tb_pos h_tx_le_tb
    · right
      refine ⟨?_, ?_⟩
      · gcongr
        exact hanti h_tx_pos h_tb_pos h_tx_le_tb
      · gcongr
        exact hanti h_ta_pos h_tx_pos h_ta_le_tx
  -- Both close_a and close_b put the endpoints in (1−ε, 1+ε).
  rw [Real.dist_eq] at h_close_a h_close_b
  rw [abs_lt] at h_close_a h_close_b
  rw [Real.dist_eq, abs_lt]
  rcases h_sandwich with ⟨h_lo, h_hi⟩ | ⟨h_lo, h_hi⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩


end TailOptionPricing
