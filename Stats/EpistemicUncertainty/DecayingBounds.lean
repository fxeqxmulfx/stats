module

/-
  Uniform actual moment bounds for geometrically decaying errors,
  arXiv:1912.00277v2, Section IV, Eq. var2 and the fourth moment below it.
  The required decay is 0<=kappa<1; kappa=1 is the nondecaying endpoint.
-/
public import Stats.EpistemicUncertainty.LayerMoments
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section

open Real Set MeasureTheory ProbabilityTheory Finset

namespace TailOptionPricing

private theorem decaying_weighted_geom_sum (n : ℕ) {a q : ℝ}
    (ha : 0 ≤ a) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∑ i ∈ range n, a * q ^ i ≤ a / (1 - q) := by
  have hg : ∑ i ∈ range n, q ^ i ≤ 1 / (1 - q) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq₀ hq₁
  rw [← Finset.mul_sum]
  calc a * ∑ i ∈ range n, q ^ i ≤ a * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left hg ha
    _ = a / (1 - q) := by ring

/-- Geometric errors remain on the source's positive dispersion
domain at every finite depth (Section IV). The source's first error
is index zero; subsequent errors are epsilon_1*kappa^i. -/
theorem epistemicLayerScaleLaw_ae_pos_decaying (n : ℕ) {σ ε₁ κ : ℝ}
    (hσ : 0 < σ) (hε₀ : 0 ≤ ε₁) (hε₁ : ε₁ < 1)
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    ∀ᵐ s ∂epistemicLayerScaleLaw n σ (fun i => ε₁ * κ ^ i), 0 < s := by
  apply epistemicLayerScaleLaw_ae_pos n hσ
  intro i hi
  constructor
  · exact mul_nonneg hε₀ (pow_nonneg hκ₀ i)
  · exact lt_of_le_of_lt (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hκ₀ hκ₁) hε₀) hε₁

/-- Section IV's actual variances are uniformly capped under genuine
geometric decay. The bound follows from the actual product, 1+x<=exp(x),
and a convergent geometric series; no limiting law is assumed. -/
theorem epistemicLayerBranchLaw_variance_decaying_le (n : ℕ) (μ σ ε₁ : ℝ) {κ : ℝ}
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ < 1) :
    variance (fun x : ℝ => x) (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i)) ≤
      σ ^ 2 * Real.exp (ε₁ ^ 2 / (1 - κ ^ 2)) := by
  rw [epistemicLayerBranchLaw_variance_decaying, decayingErrorVariance]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
  have hg := decaying_weighted_geom_sum n (a := ε₁ ^ 2) (q := κ ^ 2)
    (sq_nonneg _) (sq_nonneg _) (pow_lt_one₀ hκ₀ hκ₁ (by decide))
  have hs : ∑ i ∈ range n, ε₁ ^ 2 * κ ^ (2 * i) ≤ ε₁ ^ 2 / (1 - κ ^ 2) := by
    simpa only [← pow_mul] using hg
  exact (Real.prod_one_add_le_exp_sum (range n)
    (fun i => mul_nonneg (sq_nonneg ε₁) (pow_nonneg hκ₀ (2 * i)))).trans
    (Real.exp_le_exp.mpr hs)

/-- Section IV's actual fourth central moments are uniformly capped
for 0<=kappa<1. Both the second- and fourth-power geometric corrections
are retained in the explicit bound. -/
theorem epistemicLayerBranchLaw_centralMoment_four_decaying_le
    (n : ℕ) (μ σ ε₁ : ℝ) {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ₁ : κ < 1) :
    centralMoment (fun x : ℝ => x) 4
      (epistemicLayerBranchLaw n μ σ (fun i => ε₁ * κ ^ i)) ≤
      3 * σ ^ 4 * Real.exp (6 * ε₁ ^ 2 / (1 - κ ^ 2) + ε₁ ^ 4 / (1 - κ ^ 4)) := by
  rw [epistemicLayerBranchLaw_centralMoment_four_decaying]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h₂ := decaying_weighted_geom_sum n (a := 6 * ε₁ ^ 2) (q := κ ^ 2)
    (by positivity) (sq_nonneg _) (pow_lt_one₀ hκ₀ hκ₁ (by decide))
  have h₄ := decaying_weighted_geom_sum n (a := ε₁ ^ 4) (q := κ ^ 4)
    (by positivity) (by positivity) (pow_lt_one₀ hκ₀ hκ₁ (by decide))
  have hs : ∑ i ∈ range n, (6 * ε₁ ^ 2 * κ ^ (2 * i) + ε₁ ^ 4 * κ ^ (4 * i)) ≤
      6 * ε₁ ^ 2 / (1 - κ ^ 2) + ε₁ ^ 4 / (1 - κ ^ 4) := by
    rw [Finset.sum_add_distrib]
    exact add_le_add (by simpa only [← pow_mul] using h₂)
      (by simpa only [← pow_mul] using h₄)
  calc (∏ i ∈ range n, (1 + 6 * ε₁ ^ 2 * κ ^ (2 * i) + ε₁ ^ 4 * κ ^ (4 * i))) ≤
      Real.exp (∑ i ∈ range n, (6 * ε₁ ^ 2 * κ ^ (2 * i) + ε₁ ^ 4 * κ ^ (4 * i))) := by
        simpa only [add_assoc] using Real.prod_one_add_le_exp_sum (range n)
          (f := fun i => 6 * ε₁ ^ 2 * κ ^ (2 * i) + ε₁ ^ 4 * κ ^ (4 * i))
          (fun i => by positivity)
    _ ≤ Real.exp (6 * ε₁ ^ 2 / (1 - κ ^ 2) + ε₁ ^ 4 / (1 - κ ^ 4)) :=
      Real.exp_le_exp.mpr hs

example (n : ℕ) : ∀ᵐ s ∂epistemicLayerScaleLaw n 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i), 0 < s :=
  epistemicLayerScaleLaw_ae_pos_decaying _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example (n : ℕ) : variance (fun x : ℝ => x) (epistemicLayerBranchLaw n 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) ≤ 4 * Real.exp (1 / 3) := by
  have h := epistemicLayerBranchLaw_variance_decaying_le n 1 2 (1 / 2) (κ := 1 / 2)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

example (n : ℕ) : centralMoment (fun x : ℝ => x) 4 (epistemicLayerBranchLaw n 1 2
    (fun i => (1 / 2 : ℝ) * (1 / 2) ^ i)) ≤ 48 * Real.exp (31 / 15) := by
  have h := epistemicLayerBranchLaw_centralMoment_four_decaying_le n 1 2 (1 / 2) (κ := 1 / 2)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

#print axioms epistemicLayerBranchLaw_variance_decaying_le
#print axioms epistemicLayerBranchLaw_centralMoment_four_decaying_le

end TailOptionPricing
