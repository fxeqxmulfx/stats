module

/-
  A sufficient local condition for the matched butterfly in
  arXiv:1908.02347v3, "Arbitrage Boundaries", display `arbitrage`.
  Strict separation of the two derivatives makes the first-order term
  positive. This complements the necessary condition in Stats.Arbitrage.
-/
public import Stats.Arbitrage

@[expose] public section

open Filter Topology

namespace TailOptionPricing

/-- A strictly smaller left derivative suffices for the paper's local
mixed-butterfly inequality, provided the two call values match. -/
theorem matched_butterfly_of_deriv_lt {f g : ℝ → ℝ} {f' g' K : ℝ}
    (hf : HasDerivAt f f' K) (hg : HasDerivAt g g' K)
    (hmatch : f K = g K) (hlt : g' < f') :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), f (K + d) + g (K - d) ≥ 2 * f K := by
  let p : ℝ → ℝ := fun d => f (K + d) + g (K - d)
  have hf0 : HasDerivAt f f' (K + 0) := by simpa using hf
  have hg0 : HasDerivAt g g' (K - 0) := by simpa using hg
  have hleft : HasDerivAt (fun d : ℝ => f (K + d)) f' 0 := by
    convert hf0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add K) using 1 <;>
      simp [Function.comp_def]
  have hright : HasDerivAt (fun d : ℝ => g (K - d)) (-g') 0 := by
    convert hg0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub K) using 1 <;>
      simp [Function.comp_def]
  have hp : HasDerivAt p (f' - g') 0 := by
    convert hleft.add hright using 1
  have hpos := hp.tendsto_slope_zero_right.eventually
    (eventually_gt_nhds (sub_pos.mpr hlt))
  filter_upwards [hpos, self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with d hd hdp
  have hp0 : p 0 = 2 * f K := by simp [p, ← hmatch, two_mul]
  rw [zero_add, hp0, smul_eq_mul] at hd
  have := (mul_pos_iff_of_pos_left (inv_pos.mpr hdp)).mp hd
  dsimp [p] at this
  linarith

example : ∀ᶠ d in 𝓝[>] (0 : ℝ), (0 + d) + (0 : ℝ) ≥ 2 * 0 := by
  exact matched_butterfly_of_deriv_lt (f := id) (g := fun _ => 0)
    (hasDerivAt_id 0) (hasDerivAt_const 0 0) rfl (by norm_num)

end TailOptionPricing
