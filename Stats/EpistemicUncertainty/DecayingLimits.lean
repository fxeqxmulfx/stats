module

/-
  Actual finite moment limits under decaying errors, arXiv:1912.00277v2,
  Section IV. Uniform bounds and monotonicity give finite real limits.
  This concerns actual moment sequences; it does not infer a limit law
  or interchange an unproved infinite-population expectation and limit.
-/
public import Stats.EpistemicUncertainty.DecayingBounds
public import Stats.EpistemicUncertainty.BranchingLimits
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset Filter Topology

namespace TailOptionPricing

private theorem layer_fourth_factor_ge_one (e : ℝ) : 1 ≤ 1 + 6 * e ^ 2 + e ^ 4 := by
  nlinarith [sq_nonneg e, sq_nonneg (e ^ 2)]

/-- Section IV's actual fourth central moments increase with finite
depth. This holds for any real error sequence, by the true product formula. -/
theorem epistemicLayerBranchLaw_centralMoment_four_monotone
    (μ σ : ℝ) (ε : ℕ → ℝ) :
    Monotone (fun n => centralMoment (fun x : ℝ => x) 4 (epistemicLayerBranchLaw n μ σ ε)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [epistemicLayerBranchLaw_centralMoment_four, epistemicLayerBranchLaw_centralMoment_four,
    prod_range_succ]
  have hp : 0 ≤ ∏ i ∈ range n, (1 + 6 * (ε i) ^ 2 + (ε i) ^ 4) :=
    prod_nonneg (fun i _ => le_trans zero_le_one (layer_fourth_factor_ge_one (ε i)))
  simpa only [mul_assoc] using le_mul_of_one_le_right
    (mul_nonneg (by positivity : 0 ≤ 3 * σ ^ 4) hp) (layer_fourth_factor_ge_one (ε n))

/-- Section IV's actual variance sequence converges to a finite real
value under geometric decay. The true Gaussian base variance and the
explicit geometric/exponential cap bound that limit. -/
theorem epistemicLayerBranchLaw_variance_decaying_converges (μ σ ε₁ : ℝ) {κ : ℝ}
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ < 1) :
    ∃ v : ℝ, σ ^ 2 ≤ v ∧ v ≤ σ ^ 2 * Real.exp (ε₁ ^ 2 / (1 - κ ^ 2)) ∧
      Tendsto (fun n => variance (fun x : ℝ => x)
        (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i))) atTop (𝓝 v) := by
  let f : ℕ → ℝ := fun n => variance (fun x : ℝ => x)
    (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i))
  have hb : BddAbove (Set.range f) := ⟨σ ^ 2 * Real.exp (ε₁ ^ 2 / (1 - κ ^ 2)), by
    rintro y ⟨n, rfl⟩
    exact epistemicLayerBranchLaw_variance_decaying_le n μ σ ε₁ hκ₀ hκ₁⟩
  refine ⟨⨆ n, f n, ?_, ?_, ?_⟩
  · exact (epistemicLayerBranchLaw_variance_decaying_ge_base 0 μ σ ε₁ κ).trans (le_ciSup hb 0)
  · exact ciSup_le (fun n => epistemicLayerBranchLaw_variance_decaying_le n μ σ ε₁ hκ₀ hκ₁)
  · exact tendsto_atTop_ciSup (epistemicLayerBranchLaw_variance_decaying_monotone μ σ ε₁ κ) hb

/-- Section IV's actual fourth central moment sequence converges to a
finite real value. This proves convergence of the genuine moment products,
without asserting a particular infinite-depth probability distribution. -/
theorem epistemicLayerBranchLaw_centralMoment_four_decaying_converges
    (μ σ ε₁ : ℝ) {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ₁ : κ < 1) :
    ∃ m : ℝ, 3 * σ ^ 4 ≤ m ∧
      m ≤ 3 * σ ^ 4 * Real.exp (6 * ε₁ ^ 2 / (1 - κ ^ 2) + ε₁ ^ 4 / (1 - κ ^ 4)) ∧
      Tendsto (fun n => centralMoment (fun x : ℝ => x) 4
        (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i))) atTop (𝓝 m) := by
  let f : ℕ → ℝ := fun n => centralMoment (fun x : ℝ => x) 4
    (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i))
  have hb : BddAbove (Set.range f) :=
    ⟨3 * σ ^ 4 * Real.exp (6 * ε₁ ^ 2 / (1 - κ ^ 2) + ε₁ ^ 4 / (1 - κ ^ 4)), by
      rintro y ⟨n, rfl⟩
      exact epistemicLayerBranchLaw_centralMoment_four_decaying_le n μ σ ε₁ hκ₀ hκ₁⟩
  refine ⟨⨆ n, f n, ?_, ?_, ?_⟩
  · have hzero : 3 * σ ^ 4 = f 0 := by
      dsimp only [f]
      rw [epistemicLayerBranchLaw_centralMoment_four]
      simp
    exact hzero.trans_le (le_ciSup hb 0)
  · exact ciSup_le (fun n =>
      epistemicLayerBranchLaw_centralMoment_four_decaying_le n μ σ ε₁ hκ₀ hκ₁)
  · exact tendsto_atTop_ciSup
      (epistemicLayerBranchLaw_centralMoment_four_monotone μ σ (fun i => ε₁ * κ ^ i)) hb

/-- Section IV's closed kappa interval alone cannot ensure capped
moments: at kappa=1 nonzero error never decays. The actual varying-layer
law becomes the constant-error population, whose true variance diverges. -/
theorem epistemicLayerBranchLaw_variance_kappa_one_diverges (μ : ℝ) {σ ε₁ : ℝ}
    (hσ : σ ≠ 0) (hε : ε₁ ≠ 0) :
    Tendsto (fun n => variance (fun x : ℝ => x)
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * (1 : ℝ) ^ i))) atTop atTop := by
  simpa only [one_pow, mul_one, epistemicLayerBranchLaw_const] using
    epistemicBranchLaw_variance_tendsto_atTop μ hσ hε

example : ∃ v : ℝ, 4 ≤ v ∧ v ≤ 4 * Real.exp (1 / 3) ∧
    Tendsto (fun n => variance (fun x : ℝ => x) (epistemicLayerBranchLaw n 1 2
      (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i))) atTop (𝓝 v) := by
  have h := epistemicLayerBranchLaw_variance_decaying_converges 1 2 (1 / 2) (κ := 1 / 2)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : ∃ m : ℝ, 48 ≤ m ∧ m ≤ 48 * Real.exp (31 / 15) ∧
    Tendsto (fun n => centralMoment (fun x : ℝ => x) 4 (epistemicLayerBranchLaw n 1 2
      (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i))) atTop (𝓝 m) := by
  have h := epistemicLayerBranchLaw_centralMoment_four_decaying_converges 1 2 (1 / 2)
    (κ := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : Tendsto (fun n => variance (fun x : ℝ => x)
    (epistemicLayerBranchLaw n 0 1 (fun i => (1 / 2 : ℝ) * (1 : ℝ) ^ i))) atTop atTop :=
  epistemicLayerBranchLaw_variance_kappa_one_diverges _ (by norm_num) (by norm_num)

#print axioms epistemicLayerBranchLaw_variance_decaying_converges
#print axioms epistemicLayerBranchLaw_centralMoment_four_decaying_converges
#print axioms epistemicLayerBranchLaw_variance_kappa_one_diverges

end TailOptionPricing
